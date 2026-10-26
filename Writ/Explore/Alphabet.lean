import Writ.Codec.Event
import Writ.Kernel.Step
import Writ.Explore.Key

namespace Writ.Explore

def callPool : List String := ["c1", "c2"]
def digestPool : List String := ["d1", "d2"]
def grantPool : List String := ["g1", "g2"]
def sessionName : String := "s1"
def requesterName : String := "u1"
def reviewedScope : String := "rsd"
def wrongDigest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')

/-- One event to try from a state. A probe is there to sample a rejection: once its event type has
been sampled with `probe` as the reason, the explorer skips it. -/
structure Candidate where
  event : Event
  probe : Option Reason := none

/-- The parts of the alphabet that depend only on the policy. -/
structure Alphabet where
  policy : Policy
  digest : String
  /-- One action per distinct requirements, in policy order. -/
  actions : List (String × Requirements)
  unknownTool : String
  permissions : List String
  costs : List Cost
  /-- `u1`, `a2`, `a3`, `a4`; `session_start` attests the first two. -/
  approvers : List (String × ApproverInfo)

/-- An event string the codec accepts, so every event the explorer emits decodes back to itself. -/
def fits (s : String) : Bool := s.utf8ByteSize ≤ maxEventStringBytes

/-- An event integer the JSON parser reads back (at most 2^53 - 1, as in `Writ.Json.parse`). A time
or count a policy pushes past it is dropped, or the trace would not replay. -/
def fitsInt (n : Nat) : Bool := n ≤ 9007199254740991

/-- An amount the codec reads back. -/
def fitsAmount (n : Nat) : Bool := (toString n).length ≤ maxAmountDigits

/-- The action's name, guard names and escalator names all fit in an event. -/
def nameable (n : String) (r : Requirements) : Bool :=
  fits n && r.guards.all fits && r.escalate.all fun (e : String × Escalator) => fits e.1

def representatives (p : Policy) : List (String × Requirements) :=
  p.actions.foldl (init := []) fun acc (n, r) =>
    if !nameable n r || acc.any (·.2 == r) then acc else acc ++ [(n, r)]

/-- The actions `representatives` leaves out because an event could not name them. -/
def unnameable (p : Policy) : List String :=
  p.actions.filterMap fun (n, r) => if nameable n r then none else some n

def currencies (p : Policy) : List String :=
  let metered := p.meters.filterMap fun (_, m) => match m.unit with
    | .money c => some c
    | .calls => none
  (metered ++ p.actions.filterMap (·.2.consentIfCostOver.map (·.currency))).eraseDups.filter fits

/-- 1, each cap, each `consent_if_cost_over` amount plus 1 and each `max_per_call`, at most 4. -/
def amounts (p : Policy) (cur : String) : List Nat :=
  let money := p.meters.filter fun (_, m) => m.unit == .money cur
  let over := p.actions.filterMap fun (_, r) =>
    r.consentIfCostOver.bind fun c => if c.currency == cur then some (c.amount + 1) else none
  let caps := money.filterMap fun (_, m) => m.cap
  let perCall := money.filterMap fun (_, m) => m.maxPerCall
  ([1] ++ caps ++ over ++ perCall).eraseDups.filter fitsAmount |>.take 4

def freshName (taken : List String) (base : String) : String :=
  if base ∉ taken then base
  else ((List.range taken.length).map fun i => s!"{base}_{i + 1}").find? (· ∉ taken) |>.getD base

def Alphabet.build (p : Policy) (digest : String) : Alphabet :=
  let roles := p.approverRoles.filter fits
  { policy := p, digest
    actions := representatives p
    unknownTool := freshName (p.actions.map (·.1)) "unknown"
    permissions := (p.actions.filterMap (·.2.permission)).eraseDups.filter fits
    costs := (currencies p).flatMap fun c => (amounts p c).map (⟨·, c⟩)
    approvers := [("u1", ⟨"u1", .human, roles⟩), ("a2", ⟨"a2", .human, roles.take 1⟩),
      ("a3", ⟨"a3", .automated, roles⟩), ("a4", ⟨reservedPrincipal, .human, roles⟩)] }

namespace Alphabet

variable (a : Alphabet) (s : State)

def approverIds : List String := a.approvers.map (·.1)

def req (tool : String) : Requirements := (a.policy.action? tool).getD {}

def costRelevant (r : Requirements) : Bool :=
  r.meters.any a.policy.isMoney || r.consentIfCostOver.isSome

def costChoices (r : Requirements) : List (Option Cost) :=
  if a.costRelevant r then none :: a.costs.map some else [none]

def otherCost (c : Option Cost) : Option Cost :=
  match c with
  | some _ => none
  | none => some (a.costs.head?.getD ⟨1, "XXX"⟩)

end Alphabet

def guardChoices (r : Requirements) : List (List (String × Bool)) :=
  if r.guards.isEmpty then [[]] else [r.guards.map (·, true), r.guards.map (·, false)]

/-- Every escalator reported false, or none reported (an unreported escalator counts as fired). -/
def escalatorChoices (r : Requirements) : List (List (String × Bool)) :=
  if r.escalate.isEmpty then [[]] else [r.escalate.map (·.1, false), []]

def ev (s : State) (time : Nat) (b : EventBody) : Event := ⟨s.lastSeq + 1, time, s.version, none, b⟩

def regular (s : State) (time : Nat) (b : EventBody) : Candidate := ⟨ev s time b, none⟩

def probe (s : State) (r : Reason) (b : EventBody) : Candidate := ⟨ev s s.lastTime b, some r⟩

def idemKey (callId : String) : String := idemPrefix ++ callId

def freshCall (s : State) : Option String := callPool.find? (!s.calls.contains ·)

def freshGrant (s : State) : Option String := grantPool.find? (!s.grants.contains ·)

def usedDigests (s : State) : List String :=
  s.calls.toList.flatMap (fun (_, r) => r.proposedDigest :: r.digest :: r.generations.map (·.1))
    ++ s.rejectedMemory.map (·.2) ++ s.grants.toList.filterMap (·.2.digest)

/-- The digests in use plus the first fresh one: up to renaming, any other fresh digest is the same. -/
def digestChoices (s : State) : List String :=
  let used := usedDigests s
  match digestPool.find? (· ∉ used) with
  | some f => digestPool.filter fun d => d ∈ used || d == f
  | none => digestPool

def otherDigest (d : String) : String := (digestPool.find? (· != d)).getD "d2"

/-- The windows of the action's meters that hold entries: a later time matters only where a
time-dependent check can turn. -/
def windows (p : Policy) (s : State) (r : Requirements) : List Nat :=
  r.meters.filterMap fun m => (p.meter? m).bind fun spec =>
    if (s.meterEntries p m).any (·.meter == m) then spec.windowMs else none

def times (s : State) (later : List Nat) : List Nat :=
  (s.lastTime :: later.map (s.lastTime + ·)).eraseDups.filter fitsInt

namespace Alphabet

variable (a : Alphabet) (s : State)

def sessionStart : List Candidate :=
  let t := s.lastTime + 1
  let start (digest : String) (l : Ledger) :=
    EventBody.sessionStart sessionName digest requesterName a.permissions (a.approvers.take 2) l
  let reused : MeterEntry :=
    { meter := "m", session := sessionName, call := "c0", time := 0, amount := 1, committed := true }
  if !fitsInt t then []
  else if s.started then [⟨ev s t (start a.digest {}), some .alreadyStarted⟩]
  else
    [regular s t (start a.digest {}), regular s t (start a.digest { tombstone := true, version := 1 }),
     ⟨ev s t (start wrongDigest {}), some .policyDigestMismatch⟩,
     ⟨ev s t (start a.digest { entries := [reused], version := 1 }), some .alreadyStarted⟩]

def propose : List Candidate :=
  let p := a.policy
  let t := s.lastTime
  let fresh := match freshCall s with
    | none => []
    | some c =>
      (a.actions.flatMap fun (tool, r) =>
        let grants := s.grants.toList.filter (·.2.tool == tool)
        let later := windows p s r ++
          (if grants.isEmpty then [] else (r.grantable.bind (·.maxDurationMs)).toList) ++
          (if grants.any (·.2.notBefore.isSome) then [1] else [])
        (times s later).flatMap fun time =>
          (digestChoices s).flatMap fun d => (a.costChoices r).flatMap fun cost =>
            let gs := guardChoices r
            let es := escalatorChoices r
            let (gs, es) := if time == t then (gs, es) else (gs.take 1, es.take 1)
            gs.flatMap fun g => es.map fun e => regular s time (.propose c tool d cost g e)) ++
      [regular s t (.propose c a.unknownTool ((digestChoices s).head?.getD "d1") none [] [])]
  -- Every new proposal in a killed session is denied killed, so one stands for all of them.
  let fresh := if s.killed || s.ledger.tombstone then fresh.take 1 else fresh
  let existing := s.calls.toList.flatMap fun (c, rec) =>
    let again (d : String) (cost : Option Cost) :=
      EventBody.propose c rec.tool d cost rec.proposedGuards rec.proposedEscalators
    let current := if (rec.digest, rec.cost) != (rec.proposedDigest, rec.proposedCost) then
      [regular s t (again rec.digest rec.cost)] else []
    let late := if rec.status == .authorized then
      ((p.authorizedTtl (a.req rec.tool)).toList.filter (fitsInt <| t + ·) |>.map fun ttl =>
        regular s (t + ttl) (again rec.proposedDigest rec.proposedCost)) else []
    [regular s t (again rec.proposedDigest rec.proposedCost)] ++ current ++ late ++
      [probe s .duplicateCall (.propose c a.unknownTool rec.proposedDigest none [] [])]
  fresh ++ existing

/-- A call-scoped probe on a call id the state does not hold. -/
def unknownCall (b : String → EventBody) : List Candidate :=
  match freshCall s with
  | some c => [probe s .unknownCall (b c)]
  | none => []

def approve : List Candidate :=
  let t := s.lastTime
  (s.calls.toList.flatMap fun (c, rec) =>
    let rid : RequestId := ⟨sessionName, c, rec.generation⟩
    let plain (who : String) := EventBody.approve c rid who rec.digest rec.cost none
    if rec.status == .awaiting then
      let r := a.req rec.tool
      let edits := (escalatorChoices r).map fun es =>
        ({ newDigest := otherDigest rec.digest, newCost := rec.cost, escalators := es } : Edit)
      let byEach := a.approverIds.flatMap fun who =>
        regular s t (plain who) :: edits.map fun e => regular s t (.approve c rid who rec.digest rec.cost (some e))
      let late := (a.policy.approvalTtl r).toList.filter (fitsInt <| t + ·) |>.map fun ttl =>
        regular s (t + ttl) (plain "u1")
      let costMissing := if rec.cost.isSome && r.meters.any a.policy.isMoney then
        [probe s .costMissing (.approve c rid "u1" rec.digest rec.cost
          (some { newDigest := otherDigest rec.digest, newCost := none
                  escalators := (escalatorChoices r).head?.getD [] }))]
        else []
      byEach ++ late ++
        [probe s .staleRequest (.approve c { rid with generation := rec.generation + 1 } "u1" rec.digest rec.cost none),
         probe s .digestMismatch (.approve c rid "u1" (otherDigest rec.digest) rec.cost none),
         probe s .costMismatch (.approve c rid "u1" rec.digest (a.otherCost rec.cost) none)] ++ costMissing
    else [probe s rec.status.stageReason (plain "u1")]) ++
  unknownCall s fun c => .approve c ⟨sessionName, c, 0⟩ "u1" "d1" none none

def reject : List Candidate :=
  (s.calls.toList.flatMap fun (c, rec) =>
    let rid : RequestId := ⟨sessionName, c, rec.generation⟩
    if rec.status == .awaiting || (rec.status == .authorized && rec.attempts == 0) then
      a.approverIds.map (fun who => regular s s.lastTime (.reject c rid who)) ++
        (if rec.generation > 0 then [regular s s.lastTime (.reject c { rid with generation := 0 } "u1")] else []) ++
        [probe s .staleRequest (.reject c { rid with generation := rec.generation + 1 } "u1")]
    else [probe s rec.status.stageReason (.reject c rid "u1")]) ++
  unknownCall s fun c => .reject c ⟨sessionName, c, 0⟩ "u1"

def approvalExpire : List Candidate :=
  (s.calls.toList.flatMap fun (c, rec) =>
    let rid : RequestId := ⟨sessionName, c, rec.generation⟩
    if rec.status == .awaiting then
      [regular s s.lastTime (.approvalExpire c rid),
       probe s .staleRequest (.approvalExpire c { rid with generation := rec.generation + 1 })]
    else [probe s rec.status.stageReason (.approvalExpire c rid)]) ++
  unknownCall s fun c => .approvalExpire c ⟨sessionName, c, 0⟩

def grantCreate : List Candidate :=
  let t := s.lastTime
  let probeId := (freshGrant s).getD "g1"
  let existing := s.grants.toList.head?.map (·.1)
  (a.actions.flatMap fun (tool, r) =>
    match r.grantable with
    | none =>
      [probe s .grantNotAllowed (.grantCreate probeId "u1" tool (some "d1") .session 1 none none none reviewedScope)]
    | some gr =>
      let expires := gr.maxDurationMs.map (t + ·)
      if !expires.all fitsInt then [] else
      let maxCosts : List (Option Cost) :=
        if a.costRelevant r then [none] ++ (a.costs.head?.map some).toList else [none]
      let digests := (digestChoices s).map some ++ (if gr.anyArgs then [none] else [])
      let fresh := match freshGrant s with
        | none => []
        | some g => (a.approverIds.flatMap fun who => digests.flatMap fun d => maxCosts.map fun mc =>
          regular s t (.grantCreate g who tool d gr.scope gr.maxUses mc none expires reviewedScope)) ++
          (if fitsInt (t + 1) then
            [regular s t (.grantCreate g "u1" tool digests.head?.join gr.scope gr.maxUses none (some (t + 1))
              expires reviewedScope)] else [])
      fresh ++
        (if fitsInt (gr.maxUses + 1) then
          [probe s .grantNotAllowed (.grantCreate probeId "u1" tool (digestChoices s).head? gr.scope
            (gr.maxUses + 1) none none expires reviewedScope)] else []) ++
        (existing.map fun g => probe s .duplicateGrant (.grantCreate g "u1" tool (digestChoices s).head?
          gr.scope gr.maxUses none none expires reviewedScope)).toList) ++
  [probe s .unknownTool (.grantCreate probeId "u1" a.unknownTool (some "d1") .session 1 none none none reviewedScope)]

def grantRevoke : List Candidate :=
  s.grants.toList.map (fun (g, _) => regular s s.lastTime (.grantRevoke g)) ++
    ((freshGrant s).map fun g => probe s .unknownGrant (.grantRevoke g)).toList

def approverAttest : List Candidate :=
  a.approvers.map (fun (id, info) => regular s s.lastTime (.approverAttest id info)) ++
    ((a.approvers.find? (·.1 == "a2")).map fun (id, info) =>
      probe s .approverChanged (.approverAttest id { info with kind := .automated })).toList

def permissionAdd : List Candidate :=
  (a.permissions.filter (· ∉ s.permissions)).map (fun perm => regular s s.lastTime (.permissionAdd perm "u1")) ++
    -- The one approval-plane event every other approver passes, so its rejection shows the `agent` rule.
    (if s.approvers.contains "a4" then [regular s s.lastTime (.permissionAdd (a.permissions.head?.getD "p") "a4")]
     else []) ++
    (if s.approvers.contains "a3" then []
     else [probe s .unknownApprover (.permissionAdd (a.permissions.head?.getD "p") "a3")])

def permissionRevoke : List Candidate :=
  if a.permissions.isEmpty then [regular s s.lastTime (.permissionRevoke "p")]
  else (a.permissions.filter (· ∈ s.permissions)).map fun perm => regular s s.lastTime (.permissionRevoke perm)

def dispatch : List Candidate :=
  let p := a.policy
  let t := s.lastTime
  (s.calls.toList.flatMap fun (c, rec) =>
    let r := a.req rec.tool
    let n := rec.attempts + 1
    let go (n : Nat) (d : String) (cost : Option Cost) (g : List (String × Bool)) (k : String) :=
      EventBody.dispatch c n d cost g k
    let trueGuards := r.guards.map (·, true)
    if rec.status == .authorized || rec.status == .unknown then
      let notBefore := rec.grant.any fun g => (s.grants.get? g).any (·.notBefore.isSome)
      let later := (p.authorizedTtl r).toList ++ windows p s r ++
        (if rec.grant.isSome then (r.grantable.bind (·.maxDurationMs)).toList else []) ++
        (if notBefore then [1] else [])
      let atNow := (guardChoices r).map fun g => regular s t (go n rec.digest rec.cost g (idemKey c))
      let late := ((times s later).drop 1).map fun time =>
        regular s time (go n rec.digest rec.cost trueGuards (idemKey c))
      atNow ++ late ++
        [probe s .attemptOrder (go (n + 1) rec.digest rec.cost trueGuards (idemKey c)),
         probe s .digestMismatch (go n (otherDigest rec.digest) rec.cost trueGuards (idemKey c)),
         probe s .costMismatch (go n rec.digest (a.otherCost rec.cost) trueGuards (idemKey c))] ++
        (if rec.idempotencyKey.isSome then
          [probe s .idempotencyKeyMismatch (go n rec.digest rec.cost trueGuards (idemPrefix ++ "x"))] else [])
    else [probe s rec.status.stageReason (go n rec.digest rec.cost trueGuards (idemKey c))]) ++
  unknownCall s fun c => .dispatch c 1 "d1" none [] (idemKey c)

/-- Every outcome; for a call on a money meter also an overrun and a release. -/
def outcomes (r : Requirements) (rec : CallRec) : List (Outcome × Option Nat × Bool) :=
  [(.succeeded, none, false), (.failed, none, false), (.declined, none, false)] ++
    (if r.meters.any a.policy.isMoney then
      let over := (rec.cost.map (·.amount)).getD 0 + 1
      (if fitsAmount over then [(.succeeded, some over, false)] else []) ++ [(.failed, none, true)]
     else [])

def report (settle : String → Outcome → Option Nat → Bool → EventBody) (c : String) (rec : CallRec) :
    List Candidate :=
  let r := a.req rec.tool
  let t := s.lastTime
  (a.outcomes r rec).map (fun (o, ac, ne) => regular s t (settle c o ac ne)) ++
    ((times s (windows a.policy s r)).drop 1).map fun time => regular s time (settle c .succeeded none false)

def result : List Candidate :=
  (s.calls.toList.flatMap fun (c, rec) =>
    if rec.status == .dispatched then a.report s .result c rec
    else [probe s rec.status.stageReason (.result c .succeeded none false)]) ++
  unknownCall s fun c => .result c .succeeded none false

def outcomeUnknown : List Candidate :=
  (s.calls.toList.map fun (c, rec) =>
    if rec.status == .dispatched then regular s s.lastTime (.outcomeUnknown c)
    else probe s rec.status.stageReason (.outcomeUnknown c)) ++
  unknownCall s .outcomeUnknown

def reconcile : List Candidate :=
  (s.calls.toList.flatMap fun (c, rec) =>
    if rec.status == .unknown && rec.reconciled.isNone then a.report s .reconcile c rec
    else if rec.status == .unknown then [probe s .alreadyReconciled (.reconcile c .succeeded none false)]
    else [probe s rec.status.stageReason (.reconcile c .succeeded none false)]) ++
  unknownCall s fun c => .reconcile c .succeeded none false

def cancel : List Candidate :=
  (s.calls.toList.map fun (c, rec) =>
    if rec.status == .awaiting || rec.status == .authorized then regular s s.lastTime (.cancel c)
    else probe s rec.status.stageReason (.cancel c)) ++
  unknownCall s .cancel

def escalationAck : List Candidate :=
  if s.anyBlocked then
    a.approverIds.map (fun who => regular s s.lastTime (.escalationAck who s.escalations)) ++
      [probe s .staleRequest (.escalationAck "u1" (s.escalations + 1))]
  else [probe s .notEscalated (.escalationAck "u1" s.escalations)]

/-- The stored ledger as it is; with the tombstone flipped; one version older; without this
session's committed entries (another session pruned them); with another session's spend filling
the first principal meter. -/
def ledgerSync : List Candidate :=
  let p := a.policy
  let l := s.ledger
  let t := s.lastTime
  let bump (l' : Ledger) : Ledger := { l' with version := l.version + 1 }
  -- A store bumps the version on every write, so the store one version back from 1 is empty.
  let older : Ledger := if l.version > 1 then { l with version := l.version - 1 } else {}
  let stale := if l.version > 0 then [probe s .ledgerConflict (.ledgerSync older)] else []
  let own := l.entries.filter fun e => e.session == s.sessionId && e.committed
  let pruned := if own.isEmpty then [] else
    [regular s t (.ledgerSync (bump { l with entries := l.entries.filter (!own.contains ·) }))]
  let foreign := match p.meters.find? (·.2.scope == .principal) with
    | some (m, spec) =>
      if l.entries.any (·.session == "s0") then []
      else [regular s t (.ledgerSync (bump { l with entries := l.entries ++
        [{ meter := m, session := "s0", call := "c0", time := t, amount := spec.cap.getD 1, committed := true }] }))]
    | none => []
  [regular s t (.ledgerSync l), regular s t (.ledgerSync (bump { l with tombstone := !l.tombstone }))] ++
    stale ++ pruned ++ foreign

/-- A body for each event type, used for the wrong-envelope samples when the state offers none. -/
def defaultBody : String → EventBody
  | "session_start" => .sessionStart sessionName a.digest requesterName [] [] {}
  | "session_end" => .sessionEnd
  | "turn_start" => .turnStart true
  | "turn_end" => .turnEnd
  | "step_start" => .stepStart
  | "propose" => .propose "c1" a.unknownTool "d1" none [] []
  | "approve" => .approve "c1" ⟨sessionName, "c1", 0⟩ "u1" "d1" none none
  | "reject" => .reject "c1" ⟨sessionName, "c1", 0⟩ "u1"
  | "approval_expire" => .approvalExpire "c1" ⟨sessionName, "c1", 0⟩
  | "grant_create" => .grantCreate "g1" "u1" a.unknownTool (some "d1") .session 1 none none none reviewedScope
  | "grant_revoke" => .grantRevoke "g1"
  | "approver_attest" => .approverAttest "u1" ⟨"u1", .human, []⟩
  | "permission_add" => .permissionAdd "p" "u1"
  | "permission_revoke" => .permissionRevoke "p"
  | "dispatch" => .dispatch "c1" 1 "d1" none [] (idemKey "c1")
  | "result" => .result "c1" .succeeded none false
  | "outcome_unknown" => .outcomeUnknown "c1"
  | "reconcile" => .reconcile "c1" .succeeded none false
  | "cancel" => .cancel "c1"
  | "escalation_ack" => .escalationAck "u1" 0
  | "ledger_sync" => .ledgerSync {}
  | "reset" => .reset
  | _ => .kill

/-- The event types in the order the explorer tries them, the order of `eventTypes`. -/
def byKind : List (String × List Candidate) := [
  ("session_start", a.sessionStart s), ("session_end", [regular s s.lastTime .sessionEnd]),
  ("turn_start", [regular s s.lastTime (.turnStart true), regular s s.lastTime (.turnStart false)]),
  ("turn_end", [regular s s.lastTime .turnEnd]), ("step_start", [regular s s.lastTime .stepStart]),
  ("propose", a.propose s), ("approve", a.approve s), ("reject", a.reject s),
  ("approval_expire", approvalExpire s), ("grant_create", a.grantCreate s),
  ("grant_revoke", grantRevoke s), ("approver_attest", a.approverAttest s),
  ("permission_add", a.permissionAdd s), ("permission_revoke", a.permissionRevoke s),
  ("dispatch", a.dispatch s), ("result", a.result s), ("outcome_unknown", outcomeUnknown s),
  ("reconcile", a.reconcile s), ("cancel", cancel s), ("escalation_ack", a.escalationAck s),
  ("ledger_sync", a.ledgerSync s), ("reset", [regular s s.lastTime .reset]),
  ("kill", [regular s s.lastTime .kill])]

/-- A stale `seq`, a decreasing time and a wrong `state_version`, on the first event of a type. -/
def envelope (e : Event) : List Candidate :=
  [⟨{ e with seq := s.lastSeq }, some .staleSeq⟩] ++
    (if s.lastTime > 0 then [⟨{ e with seq := s.lastSeq + 1, time := s.lastTime - 1 }, some .timeDecreasing⟩]
     else []) ++
    [⟨{ e with stateVersion := s.version + 1 }, some .stateVersionMismatch⟩]

/-- Every candidate event from `s`, each event type's own events followed by its wrong-envelope samples. -/
def events : List Candidate :=
  (a.byKind s).flatMap fun (kind, cs) =>
    let first := match cs.head? with
      | some c => c.event
      | none => ev s s.lastTime (a.defaultBody kind)
    cs ++ envelope s first

end Alphabet

end Writ.Explore
