import WritSpec.Shadow
import WritSpec.InvCheck
import Writ.Kernel.Run

/-!
Trace checkers for the frame lemma and theorems 1 to 12 of the design spec, judged against the
shadow model in `WritSpec.Shadow`. `Inv.check` is one checker among many and the only kernel-side
code any checker calls.
-/

namespace Writ.Checks

structure Ctx where
  p : Policy
  m : Model
  m' : Model
  st : TStep
  s : MSess
  s' : MSess

def Ctx.e (c : Ctx) : Event := c.st.event
def Ctx.now (c : Ctx) : Nat := c.st.event.time
def Ctx.dec (c : Ctx) : Option Decision := decisionOf c.st.verdict
def Ctx.claimed (c : Ctx) : Bool := c.dec == some .dispatchClaimed
def Ctx.rejectedWith (c : Ctx) (r : Reason) : Bool := c.st.verdict == .rejected r

def Ctx.rejectedCode (c : Ctx) : Option String :=
  match c.st.verdict with
  | .rejected r => some r.code
  | .ok .. => none

/-- Section 6, Protocol errors: the envelope checks, in the spec's order. -/
def Ctx.envelopeReason (c : Ctx) : Option Reason :=
  let pre := c.st.pre
  let e := c.e
  let isStart := match e.body with | .sessionStart .. => true | _ => false
  let late := match e.body with | .reconcile .. | .ledgerSync _ => true | _ => false
  if !c.s.started && !isStart then some .notStarted
  else if c.s.ended && !late then some .sessionEnded
  else if c.s.started && isStart then some .alreadyStarted
  else if e.seq ≤ pre.lastSeq then some .staleSeq
  else if e.time < pre.lastTime then some .timeDecreasing
  else if e.stateVersion != pre.version then some .stateVersionMismatch
  else none

/-- The kill check rejects the event: it passed the envelope, the session is killed or
tombstoned, and the event is not one a killed session still accepts. -/
def Ctx.gated (c : Ctx) : Bool := c.envelopeReason.isNone && c.s.halted && !openWhenKilled c.e.body

def bodyTag (b : EventBody) : String := ((reprStr b).takeWhile (!·.isWhitespace)).toString.replace "Writ.EventBody." ""

structure Res where
  hits : List Nat := []
  bad : Option String := none

def Res.hit (r : Res) (i : Nat) (b : Bool := true) : Res := if b then { r with hits := i :: r.hits } else r

def Res.need (r : Res) (cond : Bool) (msg : String) : Res :=
  if cond || r.bad.isSome then r else { r with bad := some msg }

structure Checker where
  name : String
  /-- The first premise is the checker's main premise; a campaign must hit it. -/
  premises : List String
  run : Ctx → Res

instance : Inhabited Checker := ⟨⟨"", [], fun _ => {}⟩⟩

def targetOf : EventBody → Option String
  | .propose c .. | .approve c .. | .reject c .. | .approvalExpire c .. | .dispatch c .. | .result c ..
  | .outcomeUnknown c | .reconcile c .. | .cancel c => some c
  | _ => none

def isTerminal : CallStatus → Bool
  | .awaiting | .authorized | .dispatched => false
  | _ => true

def votesOf (s : MSess) (as : List Appr) : Votes :=
  as.filterMap fun a => (s.info? a.id).map (a.principal, ·)

def currentVotes (s : MSess) (c : MCall) : Votes := votesOf s (c.approvals.filter (·.gen == c.gen))

def hasDistinctPair (c : Consent) : Bool := c.groups.any fun g => g.distinct && g.clauses.length > 1

def escalationEligible (p : Policy) (info : ApproverInfo) : Bool :=
  let roles := p.escalationRoles.getD p.approverRoles
  info.principal != "agent" && info.roles.any roles.contains

def liveElsewhere (c : Ctx) : Bool :=
  c.m.sess.fold (init := false) fun acc i s => acc || (i != c.st.inst && s.started && !s.ended)

def frame : Checker where
  name := "frame"
  premises := ["rejected-step"]
  run c := match c.st.verdict with
    | .rejected _ => ({} : Res).hit 0 |>.need (c.st.post == c.st.pre) "a rejected event changed the state"
    | _ => {}

def envelope : Checker where
  name := "envelope"
  premises := ["accepted-step", "event-after-session-end", "session-start"]
  run c := Id.run do
    let pre := c.st.pre
    let post := c.st.post
    let e := c.e
    let mut r : Res := {}
    if c.dec.isNone then return r
    r := r.hit 0
    r := r.need (e.seq > pre.lastSeq) "accepted an event with seq at or below last_seq"
    r := r.need (e.time ≥ pre.lastTime) "accepted an event whose time went back"
    r := r.need (e.stateVersion == pre.version) "accepted an event naming another state version"
    r := r.need (post.lastSeq == e.seq && post.lastTime == e.time) "last_seq or last_time not recorded"
    r := r.need (post.version > pre.version) "state version did not advance"
    if c.s.ended then
      r := r.hit 1
      r := r.need (match e.body with | .reconcile .. | .ledgerSync _ => true | _ => false)
        "after session_end only reconcile and ledger_sync are accepted"
    if let .sessionStart sid _ _ _ _ ledger := e.body then
      r := r.hit 2
      r := r.need (ledger.entries.all (·.session != sid)) "session_start accepted for an id with ledger entries"
    return r

def envelopeCodes : List Reason :=
  [.notStarted, .sessionEnded, .alreadyStarted, .staleSeq, .timeDecreasing, .stateVersionMismatch]

def envelopeOrder : Checker where
  name := "envelopeOrder"
  premises := ["envelope-rejection", "before-start", "after-session-end", "seq-time-or-version", "start-with-own-entries",
    "start-reused-wrong-digest"]
  run c := Id.run do
    let mut r : Res := {}
    match c.envelopeReason with
    | some want =>
      r := r.hit 0
      r := r.hit 1 (want == .notStarted)
      r := r.hit 2 (want == .sessionEnded)
      r := r.hit 3 ([Reason.staleSeq, .timeDecreasing, .stateVersionMismatch].contains want)
      r := r.need (c.st.verdict == .rejected want)
        s!"{bodyTag c.e.body}: the envelope order gives {want.code}, the kernel gave {reprStr c.st.verdict}"
    | none =>
      -- Section 6, Ledger: a session_start's own rules, after the envelope and the kill check (which
      -- a first session_start passes), are the policy digest and then the reused-id rule.
      if let .sessionStart sid pd _ _ _ l := c.e.body then
        if l.entries.any (·.session == sid) then
          r := r.hit 4
          r := r.hit 5 (pd != c.st.pre.expectedPolicyDigest)
          let want := if pd != c.st.pre.expectedPolicyDigest then Reason.policyDigestMismatch else .alreadyStarted
          return r.need (c.st.verdict == .rejected want)
            s!"session_start for {sid}, which owns entries in the ledger it brings, gave {reprStr c.st.verdict}, not rejected {want.code}"
      if let .rejected got := c.st.verdict then
        r := r.need (!envelopeCodes.contains got)
          s!"{bodyTag c.e.body} rejected {got.code} although the envelope checks pass"
    return r

def inv : Checker where
  name := "inv"
  premises := ["step"]
  run c :=
    let r : Res := ({} : Res).hit 0
    if Inv.check c.p c.st.post then r
    else r.need false s!"Inv.check failed: {Inv.failing c.p c.st.post}"

def approvers : Checker where
  name := "approvers"
  premises := ["attest-existing-id", "attest", "attest-changed"]
  run c := Id.run do
    let mut r : Res := {}
    if let .approverAttest id info := c.e.body then
      let changed := (c.s.info? id).any (· != info)
      if c.rejectedCode == some "approver_changed" then
        r := r.need changed "approver_changed for an id that is new or attested identically"
      if changed && c.envelopeReason.isNone && !c.gated then
        r := r.hit 2
        r := r.need (c.rejectedCode == some "approver_changed")
          s!"re-attesting {id} with other details gave {reprStr c.st.verdict}, not approver_changed"
    if c.dec.isNone then return r
    match c.e.body with
    | .approverAttest id info =>
      r := r.hit 1
      if let some old := c.s.info? id then
        r := r.hit 0
        r := r.need (old == info) "an approver id was re-pointed or changed"
    | .sessionStart .. => pure ()
    | _ => return r
    let raw := c.st.post.approvers
    r := r.need (raw.size == c.s'.approvers.length && c.s'.approvers.all fun (id, i) => raw.get? id == some i)
      "the approver registry differs from the first attestations"
    return r

/-- Section 6, Identifiers: the current disposition of a repeated propose. Killed, then escalated,
take precedence for every status. -/
def expectedRepeat (c : Ctx) (cid : String) (k : MCall) : List Decision :=
  let s := c.s
  let r := k.req.getD {}
  let held := s.held k.req
  if s.killed || s.tomb then [.denied .killed]
  else if s.toolBlocked k.tool then [.denied .escalated]
  else match k.st with
  | .awaiting => if !held then [.denied .permissionMissing] else [.needsApproval ⟨s.sid, cid, k.gen⟩]
  | .authorized =>
    if !held then [.denied .permissionMissing]
    else
      let expired := match authorizedTtlOf c.p r, k.authorizedAt with
        | some d, some a => decide (c.now ≥ a + d)
        | _, _ => false
      let grantBad := match k.grant with
        | some g => !((s.grants[g]?).any (s.grantLive · c.now))
        | none => false
      let denials := (if expired then [Decision.denied .authorizationExpired] else [])
        ++ (if s.memory.contains (k.tool, k.digest) then [.denied .previouslyRejected] else [])
        ++ (if grantBad then [.denied .grantInvalid] else [])
      if denials.isEmpty then [if k.approved then .authorized else k.disposition] else denials
  | .dispatched => [.existing .dispatched]
  | .unknown => [.existing .unknown]
  | .ended =>
    match k.term with
    | some (.denied why) => [.denied why]
    | some st => [.existing st]
    | none => []

/-- Section 6, Identifiers: a repeat names the same tool, with the digest and cost either as first
proposed or as current after edits. -/
def sameProposal (k : MCall) (tool digest : String) (cost : Option Cost) : Bool :=
  tool == k.tool && ((digest == k.pDigest && cost == k.pCost) || (digest == k.digest && cost == k.cost))

def «repeat» : Checker where
  name := "repeat"
  premises := ["repeated-propose", "repeat-after-edit", "repeat-unrelated-content", "repeat-awaiting",
    "repeat-authorized", "repeat-ended", "reuse-unrecorded-id", "unknown-tool-on-recorded-id"]
  run c := Id.run do
    let mut r : Res := {}
    let .propose cid tool digest cost _ _ := c.e.body | return r
    let some k := c.s.calls[cid]? | do
      r := r.hit 6 (c.s.unrecorded.contains cid)
      return r.need (c.rejectedCode != some "duplicate_call") s!"a propose on call {cid}, which has no record, was rejected duplicate_call"
    if !sameProposal k tool digest cost then
      r := r.hit 2
      r := r.hit 7 (reqOf c.p tool).isNone
      r := r.need c.dec.isNone "a propose reusing a call id with other content was accepted"
      if c.envelopeReason.isNone then
        r := r.need (c.rejectedCode == some "duplicate_call")
          s!"a propose reusing call {cid} with other content gave {reprStr c.st.verdict}, not rejected duplicate_call"
      return r
    let some d := c.dec | return r
    r := r.hit 0
    r := r.hit 1 (k.edited && digest == k.digest && cost == k.cost)
    let pre := c.st.pre
    let post := c.st.post
    r := r.need ({ pre with lastSeq := post.lastSeq, lastTime := post.lastTime, version := post.version } == post)
      "a repeated propose changed the state"
    if k.enforce then
      r := r.hit 3 (k.st == .awaiting)
      r := r.hit 4 (k.st == .authorized)
      r := r.hit 5 (k.st != .awaiting && k.st != .authorized)
      let exp := expectedRepeat c cid k
      r := r.need (exp.contains d) s!"repeated propose answered {reprStr d}, expected one of {reprStr exp}"
    return r

def t1Consent : Checker where
  name := "t1Consent"
  premises := ["claim-with-consent", "claim-quorum>=2", "claim-distinct", "claim-after-edit", "claim-via-grant",
    "claim-escalated-consent", "approve-authorized", "propose-allowed", "propose-by-grant", "propose-needs-approval",
    "reject-accepted", "edit-without-cost-on-money-meter"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    let elig := s.elig c.p
    if let .approve cid _ _ _ _ (some ed) := c.e.body then
      r := r.hit 11 (ed.newCost.isNone && (s.calls[cid]?).any fun k => k.req.any (hasMoneyMeter c.p))
    match c.e.body, c.dec with
    | .propose cid _ _ _ _ _, some d =>
      if s.calls.contains cid then return r
      let some k := c.s'.calls[cid]? | return r
      if !k.enforce then return r
      match d with
      | .allowed =>
        r := r.hit 7
        r := r.need (trivialC k.consent) "allowed although the effective consent is not none"
      | .allowedByGrant _ =>
        r := r.hit 8
        r := r.need k.grantCovered "allowed by a grant that does not cover the call"
      | .needsApproval _ =>
        r := r.hit 9
        r := r.need (!trivialC k.consent) "needs_approval although the effective consent is none"
        let covering := match k.req with
          | some rq => s.grants.fold (init := false) fun acc gid _ =>
              acc || s.grantCovers c.p gid rq k.consent k.tool k.pDigest k.pCost k.pEsc c.now
          | none => false
        r := r.need (!covering) "needs_approval although a valid grant covers the call"
      | _ => pure ()
    | .approve cid _ who rd rc edit, some d =>
      let some k := s.calls[cid]? | return r
      let some k' := c.s'.calls[cid]? | return r
      if !k.enforce then return r
      let some info := s.info? who
        | return r.need false "an approval from an unattested approver was accepted"
      r := r.need (rd == k.digest && rc == k.cost) "an approval whose review differs from the current generation was accepted"
      r := r.need ((clausesOf k'.consent).any (elig · info)) "an approval from an approver eligible for no clause was accepted"
      match edit with
      | none =>
        r := r.need (!(k.approvals.any fun a => a.gen == k.gen && a.principal == info.principal))
          "one principal approved a generation twice"
      | some ed =>
        r := r.need c.p.bindingMutable "an edit was accepted under an immutable binding"
        if ed.newCost.isNone && (k.req.any (hasMoneyMeter c.p)) then
          r := r.need false "an edit without new_cost was accepted on an action with a money meter"
      if d == .authorized then
        r := r.hit 6
        r := r.need (satisfiedBy elig k'.consent (currentVotes s k')) "authorized without quorum"
    | .reject cid _ who, some _ =>
      let some k := s.calls[cid]? | return r
      if !k.enforce then return r
      r := r.hit 10
      -- With consent none there is no clause; any attested non-agent approver may veto.
      let eligible (info : ApproverInfo) := if trivialC k.consent then
          info.principal != "agent" && info.roles.any c.p.approverRoles.contains
        else (clausesOf k.consent).any (elig · info)
      r := r.need ((s.info? who).any eligible)
        "a reject from an approver eligible for no clause of the current consent was accepted"
    | .dispatch cid _ dg cost _ _, some .dispatchClaimed =>
      let some k := s.calls[cid]? | return r
      if !k.enforce then return r
      r := r.need (dg == k.digest && cost == k.cost) "claimed a digest or cost other than the authorized one"
      if trivialC k.consent then return r
      r := r.hit 0
      r := r.hit 1 ((clausesOf k.consent).any (·.k ≥ 2))
      r := r.hit 2 (hasDistinctPair k.consent)
      r := r.hit 3 k.edited
      r := r.hit 4 k.grant.isSome
      r := r.hit 5 (match k.req with | some rq => !(firedOf rq k.pEsc).isEmpty | none => false)
      let ttl := k.req.bind (approvalTtlOf c.p)
      let counted := k.approvals.filter fun a =>
        a.gen == k.gen && a.digest == dg && a.cost == cost && ttl.all (a.time < k.genStart + ·)
      let pathA := k.approved && !k.vetoedByEligible && satisfiedBy elig k.consent (votesOf s counted)
      let pathB := match k.grant with
        | some g => k.grantCovered && (s.grants[g]?).any (s.grantLive · c.now)
        | none => false
      r := r.need (pathA || pathB) "claimed without a satisfied consent (1a) or a covering, valid grant (1b)"
    | _, _ => pure ()
    return r

def quorumComplete : Checker where
  name := "quorumComplete"
  premises := ["approve-pending", "pending-distinct"]
  run c := Id.run do
    let mut r : Res := {}
    let .approve cid .. := c.e.body | return r
    if c.dec != some .pending then return r
    let some k := c.s'.calls[cid]? | return r
    r := r.hit 0
    r := r.hit 1 (hasDistinctPair k.consent)
    r := r.need (!satisfiedBy (c.s.elig c.p) k.consent (currentVotes c.s k))
      "quorum is reached but the approval left the call pending"
    return r

def scopeLe : GrantScope → GrantScope → Bool
  | .turn, _ => true
  | .session, .session => true
  | .session, .turn => false

def t2Grants : Checker where
  name := "t2Grants"
  premises := ["grant-claim", "grant-create", "grant-reuse-after-return", "grant-maxcost-claim", "grant-retry"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    if c.dec.isNone then return r
    match c.e.body with
    | .grantCreate gid who tool digest scope maxUses _ _ exp _ =>
      r := r.hit 1
      r := r.need (!s.grants.contains gid) "a duplicate grant id was accepted"
      match reqOf c.p tool with
      | none => r := r.need false "a grant for an unknown action was accepted"
      | some rq =>
        match rq.grantable, s.info? who with
        | some gr, some info =>
          let consents := rq.consent :: (rq.escalate.filter (·.2.grantable)).map (·.2.consent)
          r := r.need (consents.all fun k => (clausesOf k).all (eligibleFor c.p s.requester info ·))
            "a grant creator is not eligible for every clause"
          r := r.need (maxUses ≤ gr.maxUses) "a grant above max_uses was accepted"
          r := r.need (scopeLe scope gr.scope) "a grant wider than the action's scope was accepted"
          r := r.need (digest.isSome || gr.anyArgs) "a grant without a digest was accepted without any_args"
          if let some dmax := gr.maxDurationMs then
            r := r.need (exp.any (· ≤ c.now + dmax)) "a grant expiring after creation time + max_duration_ms was accepted"
        | none, _ => r := r.need false "a grant for a non-grantable action was accepted"
        | _, none => r := r.need false "a grant from an unattested approver was accepted"
    | .propose cid .. =>
      if let some (.allowedByGrant g) := c.dec then
        if !s.calls.contains cid then
          r := r.hit 2 (s.calls.fold (init := false) fun acc _ k =>
            acc || (k.grant == some g && k.claims == 0 && k.st == .ended))
    | .dispatch cid .. =>
      if c.claimed then
        if let some k := s.calls[cid]? then
          if let some g := k.grant then
            r := r.hit 0
            r := r.hit 4 (k.claims > 0)
            r := r.hit 3 ((s.grants[g]?).any (·.maxCost.isSome))
    | _ => pure ()
    for (gid, g) in c.s'.grants.toList do
      let u := c.s'.grantUse gid
      match c.st.post.grants.get? gid with
      | none => r := r.need false s!"grant {gid} is missing from the state"
      | some raw =>
        r := r.need (raw.consumed == u.consumed && raw.reserved == u.reserved)
          s!"grant {gid}: consumed {raw.consumed} reserved {raw.reserved}, spec gives {u.consumed} and {u.reserved}"
        r := r.need (u.consumed + u.reserved ≤ g.maxUses) s!"grant {gid} holds more uses than max_uses"
        r := r.need (g.firstClaims ≤ g.maxUses) s!"grant {gid} backed more first claims than max_uses"
        if let some mc := g.maxCost then
          r := r.need (raw.costConsumed == u.costConsumed && raw.costReserved == u.costReserved)
            s!"grant {gid}: cost consumed {raw.costConsumed} reserved {raw.costReserved}, spec gives {u.costConsumed} and {u.costReserved}"
          r := r.need (u.costConsumed + u.costReserved ≤ mc.amount && g.claimedCost ≤ mc.amount)
            s!"grant {gid} exceeds max_cost"
    return r

def t3Permission : Checker where
  name := "t3Permission"
  premises := ["nondenied-proposal-with-permission", "claim-with-permission", "repeat-with-permission",
    "permission-add"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    let some d := c.dec | return r
    match c.e.body with
    | .propose cid .. =>
      let k? := match s.calls[cid]? with | some k => some k | none => c.s'.calls[cid]?
      if let some k := k? then
        if k.enforce && nonDenied d && (k.req.bind (·.permission)).isSome then
          r := r.hit (if s.calls.contains cid then 2 else 0)
          r := r.need (s.held k.req) "a proposal without the permission got a non-denied disposition"
    | .dispatch cid .. =>
      if c.claimed then
        if let some k := s.calls[cid]? then
          if k.enforce && (k.req.bind (·.permission)).isSome then
            r := r.hit 1
            r := r.need (s.held k.req) "a claim without the permission"
    | .permissionAdd _ who =>
      r := r.hit 3
      r := r.need ((s.info? who).any fun i => i.principal != "agent" && i.roles.any c.p.approverRoles.contains)
        "permission_add accepted from an approver without an approver role"
    | _ => pure ()
    let raw := c.st.post.permissions
    r := r.need (raw.all c.s'.perms.contains && c.s'.perms.all raw.contains)
      "the held permissions differ from those attested and added"
    return r

def t4AtMostOnce : Checker where
  name := "t4AtMostOnce"
  premises := ["claim", "claim-retry", "claim-at-max-attempts"]
  run c := Id.run do
    let mut r : Res := {}
    let .dispatch cid attempt .. := c.e.body | return r
    if !c.claimed then return r
    let some k := c.s.calls[cid]? | return r.need false "a claim for a call never proposed"
    if !k.enforce then return r
    r := r.hit 0
    let rq := k.req.getD {}
    if !rq.retryAfterUnknown then
      r := r.need (k.claims == 0) "a second claim for an action without retry_after_unknown"
    else
      r := r.need (k.claims + 1 ≤ rq.maxAttempts) "more claims than max_attempts"
      if k.claims > 0 then
        r := r.hit 1
        r := r.hit 2 (k.claims + 1 == rq.maxAttempts)
        r := r.need (k.st == .unknown) "a retry not preceded by Unknown"
        r := r.need (k.claims ≤ k.unknowns) "more claims than 1 plus accepted outcome_unknown events"
        r := r.need (attempt > k.lastAttempt) "attempt numbers not strictly increasing"
    return r

def edgeOk (b : EventBody) (k : String) (claimed : Bool) : CallStatus → CallStatus → Bool
  | .awaiting, .authorized => match b with | .approve c .. => c == k | _ => false
  | .awaiting, .rejected | .authorized, .rejected => match b with | .reject c .. => c == k | _ => false
  | .awaiting, .expired => match b with | .approvalExpire c .. | .approve c .. => c == k | _ => false
  | .awaiting, .cancelled | .authorized, .cancelled => match b with
    | .cancel c => c == k
    | .reset | .sessionEnd | .kill | .ledgerSync _ => true
    | _ => false
  | .authorized, .dispatched => claimed && targetOf b == some k
  | .authorized, .deniedAtDispatch _ | .authorized, .expired => match b with | .dispatch c .. => c == k | _ => false
  | .dispatched, .succeeded => match b with | .result c .succeeded .. => c == k | _ => false
  | .dispatched, .failed => match b with | .result c .failed .. => c == k | _ => false
  | .dispatched, .declined => match b with | .result c .declined .. => c == k | _ => false
  | .dispatched, .unknown => match b with
    | .outcomeUnknown c => c == k
    | .reset | .sessionEnd => true
    | _ => false
  | _, _ => false

def t5Terminal : Checker where
  name := "t5Terminal"
  premises := ["event-on-terminal-call", "unknown-retry-edge", "status-change"]
  run c := Id.run do
    let mut r : Res := {}
    if c.dec.isNone then return r
    let b := c.e.body
    let tgt := targetOf b
    let post := c.st.post
    for (k, cr) in c.st.pre.calls.toList do
      match post.calls.get? k with
      | none => r := r.need false s!"call {k} disappeared"
      | some cr' =>
        if isTerminal cr.status then
          r := r.hit 0 (tgt == some k)
          if cr.status == .unknown && cr'.status == .dispatched then
            r := r.hit 1
            r := r.need (c.claimed && tgt == some k) s!"call {k} left Unknown without a claim"
            r := r.need (cr'.tool == cr.tool && cr'.epoch == cr.epoch && cr'.digest == cr.digest
                && cr'.cost == cr.cost && cr'.consent == cr.consent && cr'.tally == cr.tally
                && cr'.generations == cr.generations) s!"the retry edge changed call {k}"
          else if cr.status == .unknown then
            r := r.need ({ cr' with reconciled := cr.reconciled } == cr) s!"Unknown call {k} changed beyond reconcile evidence"
            if cr'.reconciled != cr.reconciled then
              r := r.need (match b with | .reconcile x .. => x == k | _ => false) s!"call {k} gained evidence without reconcile"
          else
            r := r.need (cr' == cr) s!"terminal call {k} changed ({reprStr cr.status} to {reprStr cr'.status})"
        else if cr'.status != cr.status then
          r := r.hit 2
          r := r.need (edgeOk b k c.claimed cr.status cr'.status)
            s!"call {k}: {reprStr cr.status} to {reprStr cr'.status} is not a lifecycle edge for this event"
    for (k, _) in post.calls.toList do
      if !c.st.pre.calls.contains k then
        r := r.need (match b with | .propose x .. => x == k | _ => false) s!"call {k} appeared without a propose"
    return r

def coarse : CallStatus → St
  | .awaiting => .awaiting
  | .authorized => .authorized
  | .dispatched => .dispatched
  | .unknown => .unknown
  | _ => .ended

/-- Section 6's lifecycle as the shadow model runs it (reset, session end, kill and a synced
tombstone void pending calls) against each call's status in the state. -/
def lifecycle : Checker where
  name := "lifecycle"
  premises := ["accepted-step-with-calls", "void-step", "ended-call"]
  run c := Id.run do
    let mut r : Res := {}
    if c.dec.isNone || c.s'.calls.isEmpty then return r
    r := r.hit 0
    r := r.hit 1 (match c.e.body with | .reset | .sessionEnd | .kill | .ledgerSync _ => true | _ => false)
    let raw := c.st.post.calls
    r := r.need (raw.size == c.s'.calls.size) "the state and the spec disagree on which calls exist"
    for (k, mc) in c.s'.calls.toList do
      match raw.get? k with
      | none => r := r.need false s!"call {k} is missing from the state"
      | some cr =>
        r := r.need (coarse cr.status == mc.st) s!"call {k} is {reprStr cr.status} in the state, {reprStr mc.st} by the spec"
        if mc.st == .ended then
          r := r.hit 2
          r := r.need (mc.term == some cr.status)
            s!"ended call {k} is {reprStr cr.status} in the state, {reprStr mc.term} by the spec"
    return r

/-- Section 6, Protocol errors: a call-scoped event that does not fit the call's status is rejected
with the reason naming that status, as its first rule after the envelope and the kill check (for
dispatch the spec puts it before the attempt number). -/
def stageJudge (c : Ctx) : Res := Id.run do
  let mut r : Res := {}
  let b := c.e.body
  if c.envelopeReason.isSome || c.gated then return r
  let cid ← match b with
    | .propose .. => return r
    | _ => match targetOf b with | some x => pure x | none => return r
  let k? := c.s.calls[cid]?
  if k?.isNone then
    r := r.hit 7
    r := r.hit 8 (c.s.unrecorded.contains cid)
    r := r.hit (match b with
      | .approve .. => 9 | .reject .. => 10 | .approvalExpire .. => 11 | .dispatch .. => 12 | .result .. => 13
      | .outcomeUnknown _ => 14 | .reconcile .. => 15 | _ => 16)
    r := r.need (c.rejectedCode == some "unknown_call")
      s!"{bodyTag b} on call {cid}, which has no record, gave {reprStr c.st.verdict}, not rejected unknown_call"
    return r
  let want := k?.bind (stageExpect b)
  let stageName := (k?.map fun k => reprStr k.st).getD "none"
  if let some got := c.rejectedCode then
    if stageCodes.contains got then
      r := r.need (want.any (·.contains got)) s!"{bodyTag b} on call {cid} rejected {got}, but the call is at stage {stageName}"
  let some codes := want | return r
  r := r.hit 0
  r := r.hit 1 (match b with | .dispatch .. => true | _ => false)
  r := r.hit 2 (match b with | .result .. | .outcomeUnknown _ | .reconcile .. => true | _ => false)
  r := r.hit 3 (match b with | .cancel _ => true | _ => false)
  r := r.hit 4 (codes.contains "retry_not_allowed")
  r := r.hit 5 (match b with | .reconcile .. => codes.contains "already_reconciled" | _ => false)
  r := r.hit 6 (match b with | .approve .. | .reject .. | .approvalExpire .. => true | _ => false)
  r := r.need (c.rejectedCode.any codes.contains)
    s!"{bodyTag b} on call {cid} at stage {stageName} gave {reprStr c.st.verdict}, expected one of {codes}"
  return r

def stages : Checker where
  name := "stages"
  premises := ["out-of-stage-event", "dispatch-out-of-stage", "report-out-of-stage", "cancel-out-of-stage",
    "retry-refused", "reconcile-twice", "approval-out-of-stage", "event-on-unrecorded-call", "event-after-unknown-tool",
    "unrecorded-approve", "unrecorded-reject", "unrecorded-approval-expire", "unrecorded-dispatch", "unrecorded-result",
    "unrecorded-outcome-unknown", "unrecorded-reconcile", "unrecorded-cancel"]
  run c := (stageJudge c).need (c.rejectedCode != some "protocol_order")
    s!"{bodyTag c.e.body} rejected protocol_order, which the spec no longer has"

def sameValues (a b : List (String × Bool)) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

/-- Section 6, Propose: a proposal for an undefined tool counts toward the proposal limits and
leaves no record; a record keeps guard and escalator values only for the action's declared names. -/
def proposalRecord : Checker where
  name := "proposalRecord"
  premises := ["fresh-propose", "unknown-tool-propose", "undeclared-guard", "undeclared-escalator",
    "unknown-tool-repeat"]
  run c := Id.run do
    let mut r : Res := {}
    if c.dec.isNone then return r
    let post := c.st.post
    if let .propose cid tool _ _ guards esc := c.e.body then
      if !c.s.calls.contains cid then
        r := r.hit 0
        match reqOf c.p tool with
        | none =>
          r := r.hit 1
          r := r.hit 4 (c.s.unrecorded.contains cid)
          r := r.need (!post.calls.contains cid) s!"the proposal of undefined tool {tool} left a record for call {cid}"
        | some rq =>
          r := r.hit 2 (guards.any fun (n, _) => !rq.guards.contains n)
          r := r.hit 3 (esc.any fun (n, _) => !rq.escalate.any (·.1 == n))
    r := r.need (post.proposalsThisTurn == c.s'.propsT && post.proposalsThisSession == c.s'.propsS)
      s!"proposal counts {post.proposalsThisTurn} this turn and {post.proposalsThisSession} this session, spec gives {c.s'.propsT} and {c.s'.propsS}"
    for (cid, k) in c.s'.calls.toList do
      if let some cr := post.calls.get? cid then
        r := r.need (sameValues cr.proposedGuards k.pGuards)
          s!"call {cid} records guards {reprStr cr.proposedGuards}, spec keeps {reprStr k.pGuards}"
        r := r.need (sameValues cr.proposedEscalators k.pEsc)
          s!"call {cid} records escalators {reprStr cr.proposedEscalators}, spec keeps {reprStr k.pEsc}"
    return r

def t6Freshness : Checker where
  name := "t6Freshness"
  premises := ["claim-with-auth-ttl", "approve-accepted", "approve-with-ttl", "claim-after-reset", "reject-earlier-generation"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    if c.dec.isNone then return r
    match c.e.body with
    | .approve cid rid .. =>
      let some k := s.calls[cid]? | return r
      if !k.enforce then return r
      r := r.hit 1
      r := r.need (rid == ⟨s.sid, cid, k.gen⟩) "an approval with a stale request id was accepted"
      r := r.need (k.epoch == s.epoch) "an approval for a call of an earlier epoch was accepted"
      if let some ttl := k.req.bind (approvalTtlOf c.p) then
        r := r.hit 2
        r := r.need (c.now < k.genStart + ttl) "an approval at or after requested_at + approval_ttl was accepted"
    | .reject cid rid _ =>
      let some k := s.calls[cid]? | return r
      r := r.need (rid.session == s.sid && rid.call == cid && rid.generation ≤ k.gen)
        "a reject echoing no generation of the call was accepted"
      r := r.hit 4 (rid.generation < k.gen)
    | .approvalExpire cid rid =>
      let some k := s.calls[cid]? | return r
      r := r.need (rid == ⟨s.sid, cid, k.gen⟩) "approval_expire with a stale request id was accepted"
    | .dispatch cid .. =>
      if !c.claimed then return r
      let some k := s.calls[cid]? | return r
      if !k.enforce then return r
      r := r.hit 3 (s.epoch > 0)
      r := r.need (k.epoch == s.epoch) "a claim for a call from an earlier epoch"
      if let some ttl := k.req.bind (authorizedTtlOf c.p) then
        r := r.hit 0
        r := r.need (k.authorizedAt.any (c.now < · + ttl)) "a claim at or after authorized_at + authorized_ttl"
    | _ => pure ()
    return r

def t7Kill : Checker where
  name := "t7Kill"
  premises := ["dispatch-after-kill", "dispatch-under-foreign-tombstone", "killed-denial"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    let dead := s.killed || s.tomb || c.m.tomb
    match c.e.body with
    | .dispatch .. =>
      if dead then
        r := r.hit 0
        r := r.hit 1 (c.m.tomb && !s.killed && !s.tomb)
        r := r.need (!c.claimed) "a claim after kill or while the principal tombstone is set"
    | _ => pure ()
    let killedDenial := c.st.verdict == .rejected .killed || c.dec == some (.denied .killed)
    if killedDenial then
      r := r.hit 2
      r := r.need (s.killed || s.tomb) "denied killed although neither kill nor a tombstone applies"
    return r

/-- Section 6, Kill: after the envelope checks, a killed or tombstoned session rejects every event
but the seven that settle or end it, and a kill never ends a call `DeniedAtDispatch`. A proposal
while killed, new or repeated, is denied `killed`; kill is never shadowed, so this holds for
`log_only` actions too. -/
def killGate : Checker where
  name := "killGate"
  premises := ["event-while-killed", "dispatch-while-killed", "settle-while-killed", "propose-while-killed",
    "start-under-tombstone", "repeat-while-killed"]
  run c := Id.run do
    let mut r : Res := {}
    let b := c.e.body
    r := r.need (c.dec != some (.dispatchDenied .killed)) "a dispatch ended its call denied_at_dispatch killed"
    if c.envelopeReason.isSome then return r
    if let .sessionStart _ _ _ _ _ l := b then
      if l.tombstone then
        r := r.hit 4
        r := r.need (!c.rejectedWith .killed) "a session_start under a set tombstone was rejected killed"
    if !c.s.halted then return r
    if c.gated then
      r := r.hit 0
      r := r.hit 1 (match b with | .dispatch .. => true | _ => false)
      r := r.need (c.rejectedWith .killed) s!"{bodyTag b} while killed gave {reprStr c.st.verdict}, not rejected killed"
      return r
    r := r.need (!c.rejectedWith .killed) s!"{bodyTag b}, which a killed session still accepts, was rejected killed"
    match b with
    | .propose cid tool digest cost _ _ =>
      match c.s.calls[cid]? with
      | none =>
        r := r.hit 3
        if let some d := c.dec then
          r := r.need (d == .denied .killed) s!"a new proposal while killed was answered {reprStr d}"
      | some k =>
        if sameProposal k tool digest cost then
          r := r.hit 5
          r := r.need (c.dec == some (.denied .killed))
            s!"a repeated proposal while killed gave {reprStr c.st.verdict}, not denied killed"
    | .kill | .ledgerSync _ => pure ()
    | _ => r := r.hit 2
    return r

def t8Limits : Checker where
  name := "t8Limits"
  premises := ["nondenied-proposal-with-limit", "needs-approval-with-limit", "step-with-limit", "limit-denial"]
  run c := Id.run do
    let mut r : Res := {}
    if c.p.mode != .enforce then return r
    let s := c.s
    let l := c.p.limits
    match c.e.body, c.dec with
    | .stepStart, some _ =>
      if let some lim := l.maxStepsPerTurn then
        r := r.hit 2
        r := r.need (s.stepsT < lim) "a step_start beyond max_steps_per_turn was accepted"
    | .stepStart, none =>
      if c.rejectedWith .stepLimit then
        r := r.hit 3
        r := r.need (l.maxStepsPerTurn.any (s.stepsT ≥ ·)) "step_limit before the limit was reached"
    | .propose cid .., some d =>
      if s.calls.contains cid then return r
      let some k := c.s'.calls[cid]? | return r
      if nonDenied d && k.enforce && (l.maxProposalsPerTurn.isSome || l.maxProposalsPerSession.isSome) then
        r := r.hit 0
        r := r.need (l.maxProposalsPerTurn.all (s.propsT < ·)) "a non-denied proposal beyond max_proposals_per_turn"
        r := r.need (l.maxProposalsPerSession.all (s.propsS < ·)) "a non-denied proposal beyond max_proposals_per_session"
      if (match d with | .needsApproval _ => true | _ => false) && k.enforce
          && (l.maxApprovalRequestsPerTurn.isSome || l.maxApprovalRequestsPerSession.isSome) then
        r := r.hit 1
        r := r.need (l.maxApprovalRequestsPerTurn.all (s.needsT < ·)) "needs_approval beyond max_approval_requests_per_turn"
        r := r.need (l.maxApprovalRequestsPerSession.all (s.needsS < ·)) "needs_approval beyond max_approval_requests_per_session"
      match d with
      | .denied .proposalLimit =>
        r := r.hit 3
        r := r.need (l.maxProposalsPerTurn.any (s.propsT ≥ ·)) "proposal_limit before the turn limit was reached"
      | .denied .sessionProposalLimit =>
        r := r.hit 3
        r := r.need (l.maxProposalsPerSession.any (s.propsS ≥ ·)) "session_proposal_limit before the limit was reached"
      | .denied .approvalBudget =>
        r := r.hit 3
        r := r.need (l.maxApprovalRequestsPerTurn.any (s.needsT ≥ ·)) "approval_budget before the turn budget was spent"
      | .denied .sessionApprovalBudget =>
        r := r.hit 3
        r := r.need (l.maxApprovalRequestsPerSession.any (s.needsS ≥ ·)) "session_approval_budget before the budget was spent"
      | _ => pure ()
    | _, _ => pure ()
    return r

def Ctx.pool (c : Ctx) (spec : MeterSpec) : List MeterEntry :=
  match spec.scope with | .session => c.s.entries | .principal => c.m.pentries

def Ctx.pool' (c : Ctx) (spec : MeterSpec) : List MeterEntry :=
  match spec.scope with | .session => c.s'.entries | .principal => c.m'.pentries

/-- The meters a claim must reserve on now: all of them on a first attempt, and on a retry the
ones whose entry has left the window. -/
def Ctx.needsRoom (c : Ctx) (cid : String) (k : MCall) : List (String × MeterSpec) :=
  (metersOf c.p (k.req.getD {})).filter fun (n, spec) =>
    k.claims == 0 || !((entryOf (c.pool spec) n c.s.sid cid).any (inWindow spec.windowMs ·.time c.now))

def Ctx.fits (c : Ctx) (k : MCall) (n : String) (spec : MeterSpec) : Bool :=
  spec.cap.all (usageOf (c.pool spec) n spec.windowMs c.now + drawOf spec k.cost ≤ ·)

def t8Meters : Checker where
  name := "t8Meters"
  premises := ["metered-first-claim", "retry-outside-window", "meter-exceeded", "calls-meter-claim",
    "multi-meter-claim", "dispatch-while-over-cap", "claim-on-window-1-meter", "usage-counts-future-entry"]
  run c := Id.run do
    let mut r : Res := {}
    let .dispatch cid .. := c.e.body | return r
    let some k := c.s.calls[cid]? | return r
    let ms := metersOf c.p (k.req.getD {})
    if ms.isEmpty then return r
    let room := c.needsRoom cid k
    r := r.hit 5 (k.enforce && room.any fun (n, spec) => spec.cap.any (usageOf (c.pool spec) n spec.windowMs c.now > ·))
    r := r.hit 7 (room.any fun (n, spec) => (c.pool spec).any fun x => x.meter == n && x.time > c.now)
    if c.claimed && k.enforce then
      if k.claims == 0 then
        r := r.hit 0
        r := r.hit 4 (ms.length > 1)
      else
        r := r.hit 1 (!room.isEmpty)
      for (n, spec) in room do
        r := r.hit 3 (spec.unit == .calls)
        r := r.hit 6 (spec.windowMs == some 1)
        if let .money cur := spec.unit then
          r := r.need (k.cost.any (·.currency == cur)) s!"claim on money meter {n} without a cost in {cur}"
          r := r.need (spec.maxPerCall.all (drawOf spec k.cost ≤ ·)) s!"a reservation above max_per_call on {n}"
        r := r.need (c.fits k n spec) s!"a reservation that brings {n} above its cap"
    let exceeded := c.st.verdict == .rejected .meterExceeded || c.dec == some (.dispatchDenied .meterExceeded)
    let stale := !c.m.current c.st.inst && room.any (·.2.scope == .principal)
    if exceeded && !stale then
      r := r.hit 2
      r := r.need (room.any fun (n, spec) => !c.fits k n spec) "meter_exceeded although every meter had room"
    return r

/-- Section 6, Propose, step 8: the first cost shape failure, money meter by money meter. -/
def costShape (ms : List (String × MeterSpec)) (cost : Option Cost) : Option Reason :=
  ms.findSome? fun (_, spec) => match spec.unit, cost with
    | .calls, _ => none
    | .money _, none => some .costMissing
    | .money cur, some x =>
      if x.currency != cur then some .currencyMismatch
      else if spec.maxPerCall.any (x.amount > ·) then some .costAbovePerCall
      else none

def Ctx.covering (c : Ctx) (r : Requirements) (consent : Consent) (tool digest : String) (cost : Option Cost)
    (esc : List (String × Bool)) : List String :=
  c.s.grants.fold (init := []) fun acc gid _ =>
    if c.s.grantCovers c.p gid r consent tool digest cost esc c.now then acc ++ [gid] else acc

/-- Section 6, Propose: every numbered check a proposal of a new call fails, in the spec's order and
tagged with its step, and whether the list is complete. A session that has not seen every ledger
write cannot be judged on principal room, so the list stops before it. -/
def Ctx.proposeFailures (c : Ctx) (tool digest : String) (cost : Option Cost) (guards esc : List (String × Bool)) :
    List (Nat × Reason) × Bool := Id.run do
  let s := c.s
  let l := c.p.limits
  let r? := reqOf c.p tool
  let mut fs : List (Nat × Reason) := []
  if s.halted then fs := fs ++ [(1, .killed)]
  if r?.isNone then fs := fs ++ [(2, .unknownTool)]
  if r?.any (!·.exposed) then fs := fs ++ [(3, .notExposed)]
  if s.toolBlocked tool then fs := fs ++ [(4, .escalated)]
  if l.maxProposalsPerSession.any (s.propsS ≥ ·) then fs := fs ++ [(5, .sessionProposalLimit)]
  if l.maxProposalsPerTurn.any (s.propsT ≥ ·) then fs := fs ++ [(5, .proposalLimit)]
  let some r := r? | return (fs, true)
  if !s.held r? then fs := fs ++ [(6, .permissionMissing)]
  if r.guards.any fun g => !((guards.find? (·.1 == g)).any (·.2)) then fs := fs ++ [(7, .guardFalse)]
  let ms := metersOf c.p r
  match costShape ms cost with
  | some why => fs := fs ++ [(8, why)]
  | none =>
    if !c.m.current c.st.inst && ms.any (·.2.scope == .principal) then return (fs, false)
    if ms.any fun (n, spec) => !spec.cap.all (usageOf (c.pool spec) n spec.windowMs c.now + drawOf spec cost ≤ ·) then
      fs := fs ++ [(8, .meterExceeded)]
  if s.memory.contains (tool, digest) then fs := fs ++ [(9, .previouslyRejected)]
  let consent := consentAt r cost esc
  if !trivialC consent && (c.covering r consent tool digest cost esc).isEmpty then
    if l.maxApprovalRequestsPerSession.any (s.needsS ≥ ·) then fs := fs ++ [(10, .sessionApprovalBudget)]
    if l.maxApprovalRequestsPerTurn.any (s.needsT ≥ ·) then fs := fs ++ [(10, .approvalBudget)]
  return (fs, true)

/-- Section 6, Propose and Shadow mode: an accepted proposal of a new call is denied with the first
failing check, else decided by consent. For a `log_only` action only a kill denies, and never with a
shadow; the first failing check from step 4 on is reported as `would_deny`, a would-be
`needs_approval` as `would_need_approval`, and either way the call proceeds as `allowed`. -/
def proposeOrder : Checker where
  name := "proposeOrder"
  premises := ["multi-failure-propose", "killed-before-unknown-tool", "not-exposed-before-escalated",
    "escalated-before-limits", "limits-before-permission", "permission-before-guard", "guard-before-cost",
    "meter-before-previously-rejected", "previously-rejected-before-budget", "session-limit-before-turn-limit",
    "session-budget-before-turn-budget", "shadowed-propose"]
  run c := Id.run do
    let mut r : Res := {}
    let .propose cid tool digest cost guards esc := c.e.body | return r
    if c.s.calls.contains cid then return r
    let .ok d sh := c.st.verdict | return r
    let (fs, complete) := c.proposeFailures tool digest cost guards esc
    let steps := fs.map (·.1)
    let first := fs.head?.map (·.2)
    -- A pair counts only when its earlier step is the one that decides the proposal.
    let firstStep := fs.head?.map (·.1)
    r := r.hit 0 (fs.length ≥ 2)
    for ((i, j), k) in [(1, 2), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10)].zipIdx do
      r := r.hit (k + 1) (firstStep == some i && steps.contains j)
    r := r.hit 9 (first == some .sessionProposalLimit && fs.contains (5, .proposalLimit))
    r := r.hit 10 (first == some .sessionApprovalBudget && fs.contains (10, .approvalBudget))
    let rq := reqOf c.p tool
    let consent := (rq.map (consentAt · cost esc)).getD {}
    let grants := match rq with | some x => c.covering x consent tool digest cost esc | none => []
    if enforced c.p rq then
      let want : List Decision := match first with
        | some why => [.denied why]
        | none =>
          if trivialC consent then [.allowed]
          else if !grants.isEmpty then grants.map .allowedByGrant
          else [.needsApproval ⟨c.s.sid, cid, 0⟩]
      if first.isNone && !complete then return r
      return r.need (want.contains d && sh.isNone)
        s!"a new proposal of {tool} gave {reprStr c.st.verdict}, the propose order gives {reprStr want}"
    if first == some .killed then
      return r.need (d == .denied .killed && sh.isNone)
        s!"a new log_only proposal while killed gave {reprStr c.st.verdict}, not denied killed without a shadow"
    if first.isNone && !complete then return r
    r := r.hit 11
    let wantSh : Option Shadow := match first with
      | some why => some (.wouldDeny why)
      | none => if !trivialC consent && grants.isEmpty then some .wouldNeedApproval else none
    let want : List Decision := if wantSh.isNone && !trivialC consent then grants.map .allowedByGrant else [.allowed]
    r := r.need (want.contains d && sh == wantSh)
      s!"a new log_only proposal of {tool} gave {reprStr c.st.verdict}, expected {reprStr want} with {reprStr wantSh}"
    return r

/-- `excess_at` means nothing while `excess` is 0. -/
def normEntry (e : MeterEntry) : MeterEntry := if e.excess == 0 then { e with excessAt := 0 } else e

def sameBag (a b : List MeterEntry) : Bool :=
  let a := a.map normEntry
  let b := b.map normEntry
  a.length == b.length && a.all fun x => a.count x == b.count x

/-- Theorem 8's accounting invariant and section 6's release, commit and pruning rules. Each list
of the state must equal the model's; the principal list only while the session has seen every
ledger write of the interleaving, since another session may have pruned the stored one. -/
def t8Accounting : Checker where
  name := "t8Accounting"
  premises := ["settle-metered", "overrun-settle", "partial-capture", "release", "late-overrun", "metered-step",
    "declined-release", "window-prune", "prune-principal", "prune-foreign-entry", "no-prune-without-update",
    "prune-keeps-other-scope"]
  run c := Id.run do
    let mut r : Res := {}
    if c.dec.isNone then return r
    let s' := c.s'
    let post := c.st.post
    let sid := s'.sid
    let mine := post.ledger.entries.filter (·.session == sid)
    if post.sessionMeters.isEmpty && post.ledger.entries.isEmpty && s'.entries.isEmpty && c.m'.pentries.isEmpty then
      return r
    r := r.hit 5
    let owned (spec : MeterScope) (e : MeterEntry) : Bool :=
      (s'.calls[e.call]?).any fun k => k.claims > 0 && (k.req.any fun rq => rq.meters.contains e.meter)
        && ((meterOf c.p e.meter).any (·.scope == spec))
    r := r.need (post.sessionMeters.all (owned .session)) "a session meter entry belongs to no dispatched call of that meter"
    r := r.need (mine.all (owned .principal)) "a principal meter entry belongs to no dispatched call of that meter"
    for (cid, k) in s'.calls.toList do
      if k.claims == 0 then continue
      let inFlight := k.st == .dispatched || (k.st == .unknown && !k.reconciled)
      for (n, spec) in metersOf c.p (k.req.getD {}) do
        let raw := match spec.scope with | .session => post.sessionMeters | .principal => mine
        let hits := raw.filter fun e => e.meter == n && e.call == cid
        if inFlight then
          r := r.need (hits.length == 1 && hits.all (!·.committed))
            s!"call {cid} may still run or settle but holds {reprStr hits} on meter {n}, not one uncommitted entry"
        else if k.released then
          r := r.need hits.isEmpty s!"call {cid} was released but holds {reprStr hits} on meter {n}"
        else
          r := r.need (hits.length ≤ 1 && hits.all (·.committed))
            s!"settled call {cid} holds {reprStr hits} on meter {n}, not at most one committed entry"
    let tgt := match c.e.body with
      | .dispatch x .. => if c.claimed then some x else none
      | .result x .. | .reconcile x .. => some x
      | _ => none
    if let some cid := tgt then
      if let some k := c.s.calls[cid]? then
        let rq := k.req.getD {}
        let ms := metersOf c.p rq
        match c.e.body with
        | .result _ o actual ne | .reconcile _ o actual ne =>
          if !ms.isEmpty then
            let rel := releases o ne
            r := r.hit 0
            r := r.hit 3 rel
            r := r.hit 6 (o == .declined && !ne)
            let res := (k.cost.map Cost.amount).getD 0
            let over := overrun c.p rq k actual rel
            r := r.hit 1 over
            r := r.hit 2 (!rel && actual.any (· < res) && hasMoneyMeter c.p rq)
            r := r.hit 4 (over && match c.e.body with | .reconcile .. => true | _ => false)
        | _ => pure ()
        for (n, spec) in ms do
          let want := entryOf (c.pool' spec) n sid cid
          let got := entryOf (match spec.scope with | .session => post.sessionMeters | .principal => post.ledger.entries) n sid cid
          let same := match want, got with
            | none, none => true
            | some a, some b => normEntry a == normEntry b
            | _, _ => false
          r := r.need same s!"meter {n} entry for {cid}: spec gives {reprStr want}, state has {reprStr got}"
    let current := c.m'.current c.st.inst
    r := r.hit 7 (!c.m'.pruned.isEmpty)
    r := r.hit 8 (current && c.m'.pruned.any fun e => (meterOf c.p e.meter).any (·.scope == .principal))
    r := r.hit 9 (current && c.m'.pruned.any (·.session != sid))
    r := r.hit 10 ((c.s.entries == s'.entries && c.s.entries.any (expired c.p .session c.now))
      || (current && c.m.pentries == c.m'.pentries && c.m.pentries.any (expired c.p .principal c.now)))
    let sessionExpired (e : MeterEntry) : Bool := (meterOf c.p e.meter).any fun spec =>
      spec.scope == .session && spec.windowMs.any (outsideWindow · c.now e)
    let kept := c.m'.pentries.filter sessionExpired
    r := r.hit 11 (current && c.m.pentries != c.m'.pentries && !kept.isEmpty)
    r := r.need (sameBag post.sessionMeters s'.entries)
      s!"session meter entries: spec gives {reprStr s'.entries}, state has {reprStr post.sessionMeters}"
    if current then
      let lost := kept.filter fun e => !post.ledger.entries.any (normEntry · == normEntry e)
      r := r.need lost.isEmpty s!"a session meter pruned the principal ledger: {reprStr lost} dropped"
      r := r.need (sameBag post.ledger.entries c.m'.pentries)
        s!"principal ledger entries: spec gives {reprStr c.m'.pentries}, state has {reprStr post.ledger.entries}"
    return r

/-- Section 6, Meters and Verdicts: an accepted `result` or `reconcile` decides `overrun` with the
overrun meters when it commits above the reservation, and nothing otherwise. -/
def overrunDecision : Checker where
  name := "overrunDecision"
  premises := ["settling-report", "overrun-report", "multi-meter-overrun", "release-with-excess"]
  run c := Id.run do
    let mut r : Res := {}
    let some d := c.dec | return r
    let (cid, o, actual, ne) ← match c.e.body with
      | .result x o a ne | .reconcile x o a ne => pure (x, o, a, ne)
      | _ => return r
    let some k := c.s.calls[cid]? | return r
    let rq := k.req.getD {}
    let rel := releases o ne
    let ms := overrunMeters c.p rq k actual rel
    r := r.hit 0
    r := r.hit 1 (!ms.isEmpty)
    r := r.hit 2 (ms.length ≥ 2)
    r := r.hit 3 (rel && hasMoneyMeter c.p rq && actual.any (· > (k.cost.map Cost.amount).getD 0))
    let want := if ms.isEmpty then "no decision" else s!"overrun {ms}"
    r := r.need (decisionIs d ms) s!"{bodyTag c.e.body} on call {cid} decided {reprStr d}, expected {want}"
    return r

def t9Ledger : Checker where
  name := "t9Ledger"
  premises := ["principal-claim-multi-live", "principal-claim", "sync-accepted", "sync-conflict",
    "claim-after-foreign-commit", "sync-after-foreign-prune", "sync-missing-reservation", "sync-changed-entry",
    "sync-clears-tombstone-ended", "sync-duplicate-own-entry"]
  run c := Id.run do
    let mut r : Res := {}
    let pre := c.st.pre
    let post := c.st.post
    match c.e.body with
    | .ledgerSync l =>
      -- Section 6, Ledger: an own entry may be missing only if committed, since another session
      -- may have pruned it; a reservation may not, and an own entry may not change or appear more
      -- often than the state holds it. Only an ended session may take a ledger whose tombstone was
      -- cleared.
      let own (x : Ledger) := x.entries.filter (·.session == c.s.sid)
      let ownPre := own pre.ledger
      let ownL := own l
      let missing := ownPre.filter (!ownL.contains ·)
      let clears := c.s.tomb && !l.tombstone
      let within := ownL.all fun x => ownL.count x ≤ ownPre.count x
      let ok := l.version ≥ pre.ledger.version && within && missing.all (·.committed)
        && (!clears || c.s.ended)
      if c.envelopeReason.isNone then
        r := r.hit 5 (missing.any (·.committed))
        r := r.hit 6 (missing.any (!·.committed))
        r := r.hit 7 (!ownL.all ownPre.contains)
        r := r.hit 8 (clears && c.s.ended)
        r := r.hit 9 (ownL.all ownPre.contains && !within)
      if c.dec.isSome then
        r := r.hit 2
        r := r.need ok
          "ledger_sync accepted an older ledger, a tombstone-clearing one on a live session, or one that changes or duplicates an own entry or drops a reservation"
        r := r.need (post.ledger == l) "ledger_sync did not adopt the stored ledger"
      else if c.rejectedWith .ledgerConflict then
        r := r.hit 3
        r := r.need (!ok) "ledger_conflict for a ledger that brings the session up to date"
      return r
    | _ => pure ()
    if c.dec.isSome then
      let changed := post.ledger.entries != pre.ledger.entries || post.ledger.tombstone != pre.ledger.tombstone
      r := r.need (!(changed || c.claimed) || post.ledger.version > pre.ledger.version)
        "the ledger changed, or a dispatch was claimed, without a ledger version increment"
    let .dispatch cid .. := c.e.body | return r
    if !c.claimed then return r
    let some k := c.s.calls[cid]? | return r
    r := r.need (!c.m.tomb) "a claim while the principal tombstone is set in the interleaving"
    let prin := (c.needsRoom cid k).filter (·.2.scope == .principal)
    if prin.isEmpty || !k.enforce then return r
    r := r.hit 1
    r := r.hit 0 (liveElsewhere c)
    r := r.hit 4 (c.m.lastLedgerWriter.any (· != c.st.inst))
    r := r.need (prin.all fun (n, spec) => c.fits k n spec) "a principal meter reservation above its cap across sessions"
    return r

def unexposedTool (p : Policy) (tool : String) : Bool := (reqOf p tool).all (!·.exposed)

/-- Theorem 10: whatever the policy-level or action-level mode. -/
def t10DefaultDeny : Checker where
  name := "t10DefaultDeny"
  premises := ["unknown-or-unexposed-propose", "unexposed-claim-attempt", "under-log-only-policy"]
  run c := Id.run do
    let mut r : Res := {}
    match c.e.body with
    | .propose cid tool .. =>
      let some d := c.dec | return r
      if c.s.calls.contains cid || !unexposedTool c.p tool then return r
      r := r.hit 0
      r := r.hit 2 (c.p.mode == .logOnly)
      r := r.need (!nonDenied d) "an unknown or unexposed action was not denied"
    | .dispatch cid .. =>
      if let some k := c.s.calls[cid]? then
        if unexposedTool c.p k.tool then
          r := r.hit 1
          r := r.need (!c.claimed) "a claim of an unknown or unexposed action"
    | _ => pure ()
    return r

def t11Escalation : Checker where
  name := "t11Escalation"
  premises := ["proposal-while-escalated", "dispatch-while-escalated", "ack-accepted", "stale-ack",
    "tool-blocked-proposal", "repeat-while-escalated", "escalated-denial", "escalation-count-step", "idle-ack"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    let s' := c.s'
    let pre := c.st.pre
    let post := c.st.post
    match c.e.body with
    | .propose cid tool .. =>
      let k? := match s.calls[cid]? with | some k => some k | none => s'.calls[cid]?
      let enf := k?.any (·.enforce)
      if enf && s.toolBlocked tool then
        r := r.hit 0
        r := r.hit 4 (!s.sessBlocked)
        r := r.hit 5 (s.calls.contains cid)
        r := r.need (!(c.dec.any nonDenied)) "a non-denied proposal while escalated"
    | .dispatch cid .. =>
      if let some k := s.calls[cid]? then
        if k.enforce && s.toolBlocked k.tool then
          r := r.hit 1
          r := r.need (!c.claimed) "a claim while escalated"
    | .escalationAck who echo =>
      if echo != pre.escalations && s.anyBlocked then r := r.hit 3
      if c.dec.isSome then
        r := r.hit 2
        r := r.need s.anyBlocked "escalation_ack accepted while nothing is blocked"
        r := r.need (echo == pre.escalations) "escalation_ack echoing a stale count was accepted"
        r := r.need ((s.info? who).any (escalationEligible c.p)) "escalation_ack from an approver without an escalation role"
      else if c.rejectedWith .staleRequest then
        r := r.need (echo != pre.escalations) "escalation_ack echoing the current count rejected as stale"
      else if c.rejectedCode == some "not_escalated" then
        r := r.need (!s.anyBlocked) "escalation_ack rejected not_escalated while something is blocked"
      if !s.anyBlocked && echo == pre.escalations && (s.info? who).any (escalationEligible c.p)
          && c.envelopeReason.isNone && !c.gated then
        r := r.hit 8
        r := r.need (c.rejectedCode == some "not_escalated")
          s!"an eligible, current escalation_ack while nothing is blocked gave {reprStr c.st.verdict}, not not_escalated"
    | _ => pure ()
    let escDenial := c.st.verdict == .rejected .escalated
      || c.dec == some (.denied .escalated) || c.dec == some (.dispatchDenied .escalated)
    -- A repeated propose reports the call's original denial, so only fresh decisions count here.
    let freshTool := match c.e.body with
      | .propose x t .. => if s.calls.contains x then none else some t
      | .dispatch x .. => (s.calls[x]?).map MCall.tool
      | _ => none
    if escDenial && freshTool.isSome then
      r := r.hit 6
      r := r.need (freshTool.all s.toolBlocked) "denied escalated although neither the session nor the tool is blocked"
    if c.dec.isSome then
      -- Section 6: each newly blocked tool or session, and every failure recorded while
      -- anything is blocked, increments the count.
      let newBlocks := (if !s.sessBlocked && s'.sessBlocked then 1 else 0)
        + (s'.blocked.filter (!s.blocked.contains ·)).length
      let failWhileBlocked := s'.failCount > s.failCount && s.anyBlocked
      let bound := newBlocks + (if failWhileBlocked then 1 else 0)
      r := r.hit 7 (bound > 0)
      r := r.need (post.escalations ≥ pre.escalations) "the escalation count decreased"
      if bound > 0 then
        r := r.need (post.escalations > pre.escalations) "a new block or a failure while blocked left the escalation count unchanged"
        r := r.need (post.escalations ≤ pre.escalations + bound)
          s!"the escalation count rose by {post.escalations - pre.escalations}, above {bound} new blocks and failures while blocked"
      else
        r := r.need (post.escalations == pre.escalations) "the escalation count changed without a new block or a failure while blocked"
    return r

def t12Rejection : Checker where
  name := "t12Rejection"
  premises := ["propose-rejected-pair", "approve-rejected-pair", "dispatch-rejected-pair", "edit-to-rejected-digest"]
  run c := Id.run do
    let mut r : Res := {}
    let s := c.s
    match c.e.body with
    | .propose cid tool digest .. =>
      if s.calls.contains cid || !s.memory.contains (tool, digest) then return r
      let some d := c.dec | return r
      let some k := c.s'.calls[cid]? | return r
      if !k.enforce then return r
      r := r.hit 0
      r := r.need (!(d == .allowed || match d with | .allowedByGrant _ => true | _ => false))
        "a rejected (tool, digest) was newly authorized at propose"
    | .approve cid _ _ _ _ edit =>
      let some k := s.calls[cid]? | return r
      if !k.enforce then return r
      let target := match edit with | some ed => ed.newDigest | none => k.digest
      if !s.memory.contains (k.tool, target) then return r
      r := r.hit 1
      r := r.hit 3 edit.isSome
      r := r.need (c.dec != some .authorized) "a rejected (tool, digest) was newly authorized by an approval"
    | .dispatch cid _ dg .. =>
      let some k := s.calls[cid]? | return r
      if !k.enforce || k.claims > 0 || !s.memory.contains (k.tool, dg) then return r
      r := r.hit 2
      r := r.need (!c.claimed) "a first-attempt claim of a rejected (tool, digest)"
    | _ => pure ()
    return r

def checkers : List Checker :=
  [frame, envelope, envelopeOrder, inv, approvers, «repeat», t1Consent, quorumComplete, t2Grants, t3Permission,
   t4AtMostOnce, t5Terminal, stages, proposalRecord, proposeOrder, t6Freshness, t7Kill, killGate, t8Limits, t8Meters, t8Accounting,
   overrunDecision, t9Ledger, t10DefaultDeny, t11Escalation, t12Rejection, lifecycle]

structure Outcome where
  name : String
  premises : List (String × Nat)
  firstBad : Option (Nat × String) := none
  deriving Repr

def Outcome.ok (o : Outcome) : Bool := o.firstBad.isNone

def runWith (cs : List Checker) (t : Trace) : List Outcome := Id.run do
  let cs := cs.toArray
  let mut counts : Array (Array Nat) := cs.map fun k => Array.replicate k.premises.length 0
  let mut bads : Array (Option (Nat × String)) := cs.map fun _ => none
  let mut m := Model.init t.initLedger
  let mut idx := 0
  for it in t.items do
    let m' := m.apply t.policy it
    if let .step st := it then
      let ctx : Ctx := { p := t.policy, m, m', st, s := m.session st.inst, s' := m'.session st.inst }
      for j in [0:cs.size] do
        let res := cs[j]!.run ctx
        if !res.hits.isEmpty then
          counts := counts.modify j fun a => res.hits.foldl (fun a i => a.modify i (· + 1)) a
        if bads[j]!.isNone then
          if let some msg := res.bad then bads := bads.set! j (some (idx, msg))
    m := m'
    idx := idx + 1
  return (List.range cs.size).map fun j =>
    { name := cs[j]!.name, premises := cs[j]!.premises.zip counts[j]!.toList, firstBad := bads[j]! }

def check (t : Trace) : List Outcome := runWith checkers t

def firstViolation (name : String) (t : Trace) : Option Nat :=
  ((runWith (checkers.filter (·.name == name)) t).head?.bind (·.firstBad)).map (·.1)

/-- Rebuild a trace from per-session scripts and an interleaving; `none` in `order` clears the
stored tombstone. `mk` builds the event from the script entry, its 0-based position and the
session's current state. -/
def replayScripts (p : Policy) (initLedger : Ledger) (scripts : List (List α))
    (order : List (Option Nat)) (mk : α → Nat → State → Event) (digest : String) : Trace := Id.run do
  let scripts := scripts.toArray
  let mut states : Array State := scripts.map fun _ => State.initial digest
  let mut pos : Array Nat := scripts.map fun _ => 0
  let mut items : Array Item := #[]
  for o in order do
    match o with
    | none => items := items.push .storeClear
    | some i =>
      if h : i < scripts.size then
        if let some x := scripts[i][pos[i]!]? then
          let s := (states[i]?).getD (State.initial digest)
          let e := mk x pos[i]! s
          let (s', v) := step p s e
          items := items.push (.step ⟨i, s, e, v, s'⟩)
          states := states.set! i s'
          pos := pos.modify i (· + 1)
  return { policy := p, initLedger, items := items.toList }

/-- Scripts in the `checkedScript` envelope: seq from 1 and the current state version. -/
def scripted (p : Policy) (initLedger : Ledger) (scripts : List (List (Nat × EventBody)))
    (order : List (Option Nat)) (digest : String := "pd") : Trace :=
  replayScripts p initLedger scripts order (fun (t, b) k s => ⟨k + 1, t, s.version, none, b⟩) digest

/-- Raw envelopes, for traces that need stale seq numbers or versions. -/
def rawScripted (p : Policy) (initLedger : Ledger) (scripts : List (List Event))
    (order : List (Option Nat)) (digest : String := "pd") : Trace :=
  replayScripts p initLedger scripts order (fun e _ _ => e) digest


end Writ.Checks
