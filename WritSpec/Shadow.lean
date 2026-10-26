import Std.Data.HashMap
import Writ.Core.State

/-!
A shadow model of the kernel, restated from the design spec (sections 5 to 8) without reading or
calling any kernel code. It advances only on accepted verdicts, and it takes the kernel's verdict
as the record of what happened; every rule it uses to judge that verdict is its own.
-/

namespace Writ.Checks

structure TStep where
  inst : Nat
  pre : State
  event : Event
  verdict : Verdict
  post : State

inductive Item where
  | step (s : TStep)
  /-- The stored tombstone was cleared out of band (section 7), which bumps the ledger version. -/
  | storeClear

structure Trace where
  policy : Policy
  initLedger : Ledger := {}
  items : List Item

def reqOf (p : Policy) (tool : String) : Option Requirements :=
  (p.actions.find? (·.1 == tool)).map (·.2)

def meterOf (p : Policy) (name : String) : Option MeterSpec :=
  (p.meters.find? (·.1 == name)).map (·.2)

/-- Section 6, Shadow mode: log-only never applies to an unknown or unexposed action, so those are
always enforced, whatever the policy-level mode. -/
def enforced (p : Policy) (r : Option Requirements) : Bool :=
  match r with
  | some r => !r.exposed || (match r.mode with | some m => m | none => p.mode) == .enforce
  | none => true

def approvalTtlOf (p : Policy) (r : Requirements) : Option Nat :=
  match r.approvalTtlMs with | some d => some d | none => p.limits.approvalTtlMs

def authorizedTtlOf (p : Policy) (r : Requirements) : Option Nat :=
  match r.authorizedTtlMs with | some d => some d | none => p.limits.authorizedTtlMs

/-- Section 5: an escalator fires when reported true or missing. -/
def fires (reported : List (String × Bool)) (name : String) : Bool :=
  match reported.find? (·.1 == name) with
  | some (_, b) => b
  | none => true

def firedOf (r : Requirements) (reported : List (String × Bool)) : List Escalator :=
  r.escalate.filterMap fun (n, e) => if fires reported n then some e else none

def addGroups (acc : List Group) (gs : List Group) : List Group :=
  gs.foldl (fun acc g => if acc.contains g then acc else acc ++ [g]) acc

/-- Section 5: consent joins by the union of groups, equal groups once. -/
def joinC (a b : Consent) : Consent := ⟨addGroups (addGroups [] a.groups) b.groups⟩

def clausesOf (c : Consent) : List Clause := c.groups.flatMap (·.clauses)

def trivialC (c : Consent) : Bool := (clausesOf c).isEmpty

/-- Section 8, theorem 1(b): every clause has k at most 1 and no distinct group has two clauses. -/
def singleC (c : Consent) : Bool :=
  (clausesOf c).all (·.k ≤ 1) && c.groups.all fun g => !g.distinct || g.clauses.length ≤ 1

/-- `consent_if_cost_over`: a declared cost in the same currency below it needs no consent; the
fired escalators are joined in regardless. -/
def costBelow (r : Requirements) (cost : Option Cost) : Bool :=
  match r.consentIfCostOver, cost with
  | some t, some c => c.currency == t.currency && c.amount < t.amount
  | _, _ => false

def consentAt (r : Requirements) (cost : Option Cost) (reported : List (String × Bool)) : Consent :=
  let base : Consent := if costBelow r cost then {} else r.consent
  (firedOf r reported).foldl (fun c e => joinC c e.consent) (joinC {} base)

/-- Section 6, Approve: attested, an approver role and one of the clause's roles, human if
`human_only`, not the requester if `exclude_requester`; section 5: never `agent`. -/
def eligibleFor (p : Policy) (requester : String) (info : ApproverInfo) (cl : Clause) : Bool :=
  info.principal != "agent"
    && info.roles.any p.approverRoles.contains
    && (match cl.roles with | none => true | some rs => info.roles.any rs.contains)
    && (!cl.humanOnly || info.kind == .human)
    && (!cl.excludeRequester || info.principal != requester)

abbrev Votes := List (String × ApproverInfo)

def distinctPrincipals (vs : Votes) : List String := (vs.map (·.1)).eraseDups

/-- Distinct assignment of principals to slots, by exhaustive search (slots are few). -/
def assignAll (ok : Clause → ApproverInfo → Bool) (vs : Votes) : List Clause → List String → Bool
  | [], _ => true
  | cl :: rest, used => vs.any fun (pr, info) => !used.contains pr && ok cl info && assignAll ok vs rest (pr :: used)

def groupSat (ok : Clause → ApproverInfo → Bool) (vs : Votes) (g : Group) : Bool :=
  if g.distinct then
    let slots := g.clauses.flatMap fun cl => List.replicate cl.k cl
    let slots := slots.mergeSort fun a b => (vs.filter (ok a ·.2)).length ≤ (vs.filter (ok b ·.2)).length
    slots.length ≤ (distinctPrincipals vs).length && assignAll ok vs slots []
  else
    g.clauses.all fun cl => (distinctPrincipals (vs.filter (ok cl ·.2))).length ≥ cl.k

def satisfiedBy (ok : Clause → ApproverInfo → Bool) (c : Consent) (vs : Votes) : Bool :=
  c.groups.all (groupSat ok vs)

/-- Section 6, Meters: an entry at `t` with window `w` counts while `now < t + w`, with no lower
bound, so an entry dated ahead of this session's clock (another session's clock runs ahead) counts. -/
def inWindow (w : Option Nat) (t now : Nat) : Bool :=
  match w with | none => true | some w => now < t + w

def usageOf (entries : List MeterEntry) (name : String) (w : Option Nat) (now : Nat) : Nat :=
  entries.foldl (init := 0) fun acc e =>
    if e.meter != name then acc
    else acc + (if inWindow w e.time now then e.amount else 0)
      + (if e.excess > 0 && inWindow w e.excessAt now then e.excess else 0)

def drawOf (spec : MeterSpec) (cost : Option Cost) : Nat :=
  match spec.unit with
  | .calls => 1
  | .money _ => (cost.map Cost.amount).getD 0

def metersOf (p : Policy) (r : Requirements) : List (String × MeterSpec) :=
  r.meters.filterMap fun n => (meterOf p n).map (n, ·)

def hasMoneyMeter (p : Policy) (r : Requirements) : Bool :=
  (metersOf p r).any fun (_, m) => match m.unit with | .money _ => true | .calls => false

inductive St where | awaiting | authorized | dispatched | unknown | ended
  deriving DecidableEq, Repr, Inhabited

structure Appr where
  id : String
  principal : String
  gen : Nat
  time : Nat
  digest : String
  cost : Option Cost
  deriving Repr

structure MCall where
  tool : String
  req : Option Requirements
  enforce : Bool
  epoch : Nat
  proposedAt : Nat
  pDigest : String
  pCost : Option Cost
  pGuards : List (String × Bool)
  pEsc : List (String × Bool)
  disposition : Decision
  consent : Consent
  digest : String
  cost : Option Cost
  gen : Nat := 0
  genStart : Nat
  gens : List String
  approvals : List Appr := []
  edited : Bool := false
  vetoedByEligible : Bool := false
  st : St
  approved : Bool := false
  authorizedAt : Option Nat := none
  grant : Option String := none
  grantCovered : Bool := false
  claims : Nat := 0
  lastAttempt : Nat := 0
  unknowns : Nat := 0
  reconciled : Bool := false
  released : Bool := false
  /-- The terminal disposition section 6's lifecycle gives an ended call. -/
  term : Option CallStatus := none

structure MGrant where
  creator : String
  creatorInfo : Option ApproverInfo
  tool : String
  digest : Option String
  scope : GrantScope
  maxUses : Nat
  maxCost : Option Cost
  notBefore : Option Nat
  expiresAt : Option Nat
  epoch : Nat
  turn : Nat
  revoked : Bool := false
  dead : Bool := false
  firstClaims : Nat := 0
  claimedCost : Nat := 0

structure MSess where
  started : Bool := false
  ended : Bool := false
  sid : String := ""
  requester : String := ""
  approvers : List (String × ApproverInfo) := []
  perms : List String := []
  epoch : Nat := 0
  turnActive : Bool := false
  turn : Nat := 0
  stepsT : Nat := 0
  propsT : Nat := 0
  needsT : Nat := 0
  propsS : Nat := 0
  needsS : Nat := 0
  calls : Std.HashMap String MCall := {}
  /-- Call ids proposed for a tool the policy does not define, which leaves no call record. -/
  unrecorded : List String := []
  grants : Std.HashMap String MGrant := {}
  killed : Bool := false
  tomb : Bool := false
  fails : List (String × Nat) := []
  total : Nat := 0
  failCount : Nat := 0
  sessBlocked : Bool := false
  blocked : List String := []
  memory : List (String × String) := []
  entries : List MeterEntry := []

structure Model where
  sess : Std.HashMap Nat MSess := {}
  pentries : List MeterEntry := []
  tomb : Bool := false
  lastLedgerWriter : Option Nat := none
  writes : Nat := 0
  seen : Std.HashMap Nat Nat := {}
  /-- The entries the last step pruned, from either list. -/
  pruned : List MeterEntry := []

def MSess.info? (s : MSess) (id : String) : Option ApproverInfo :=
  (s.approvers.find? (·.1 == id)).map (·.2)

def MSess.elig (p : Policy) (s : MSess) : Clause → ApproverInfo → Bool := fun cl info =>
  eligibleFor p s.requester info cl

def MSess.held (s : MSess) (r : Option Requirements) : Bool :=
  match r.bind (·.permission) with
  | none => true
  | some perm => s.perms.contains perm

def MSess.toolBlocked (s : MSess) (tool : String) : Bool := s.sessBlocked || s.blocked.contains tool

def MSess.anyBlocked (s : MSess) : Bool := s.sessBlocked || !s.blocked.isEmpty

def MSess.grantLive (s : MSess) (g : MGrant) (now : Nat) : Bool :=
  !g.revoked && !g.dead && g.epoch == s.epoch
    && g.notBefore.all (· ≤ now) && g.expiresAt.all (now < ·)
    && (g.scope != .turn || (s.turnActive && g.turn == s.turn))

/-- Section 6, Grants: a use (and, with `max_cost`, the cost) is reserved at propose, consumed at
the first claim, and returned when the call ends without a claim. -/
structure GrantUse where
  consumed : Nat := 0
  reserved : Nat := 0
  costConsumed : Nat := 0
  costReserved : Nat := 0

def MSess.grantUse (s : MSess) (gid : String) : GrantUse :=
  s.calls.fold (init := {}) fun u _ c =>
    if c.grant != some gid then u
    else
      let amt := (c.cost.map Cost.amount).getD 0
      if c.claims > 0 then { u with consumed := u.consumed + 1, costConsumed := u.costConsumed + amt }
      else if c.st == .authorized then { u with reserved := u.reserved + 1, costReserved := u.costReserved + amt }
      else u

def MSess.grantCovers (p : Policy) (s : MSess) (gid : String) (r : Requirements) (consent : Consent)
    (tool digest : String) (cost : Option Cost) (reported : List (String × Bool)) (now : Nat) : Bool :=
  match s.grants[gid]? with
  | none => false
  | some g =>
    let u := s.grantUse gid
    r.grantable.isSome && singleC consent && (firedOf r reported).all (·.grantable)
      && (match g.creatorInfo with
          | some info => (clausesOf consent).all fun cl => eligibleFor p s.requester info cl
          | none => false)
      && g.tool == tool && g.digest.all (· == digest)
      && (match g.maxCost with
          | none => true
          | some mc => match cost with
            | some c => c.currency == mc.currency && u.costConsumed + u.costReserved + c.amount ≤ mc.amount
            | none => false)
      && s.grantLive g now && u.consumed + u.reserved < g.maxUses

def MSess.setCall (s : MSess) (id : String) (c : MCall) : MSess := { s with calls := s.calls.insert id c }

def MSess.mapCalls (s : MSess) (f : MCall → MCall) : MSess :=
  { s with calls := s.calls.fold (init := {}) fun acc k c => acc.insert k (f c) }

def voidPending (c : MCall) : MCall :=
  if c.st == .awaiting || c.st == .authorized then { c with st := .ended, term := some .cancelled } else c

def toUnknown (c : MCall) : MCall := if c.st == .dispatched then { c with st := .unknown } else c

def MSess.fail (p : Policy) (s : MSess) (tool : String) : MSess :=
  let n := ((s.fails.find? (·.1 == tool)).map (·.2)).getD 0 + 1
  let fails := (tool, n) :: s.fails.filter (·.1 != tool)
  let total := s.total + 1
  let toolHit := p.limits.maxConsecutiveFailures.any (n ≥ ·)
  let sessHit := p.limits.maxFailuresPerSession.any (total ≥ ·)
    || (p.limits.escalationScope == .session && toolHit)
  let toolBlock := p.limits.escalationScope == .tool && toolHit
  { s with fails, total, failCount := s.failCount + 1
           sessBlocked := s.sessBlocked || sessHit
           blocked := if toolBlock && !s.blocked.contains tool then s.blocked ++ [tool] else s.blocked }

def MSess.succeed (s : MSess) (tool : String) : MSess :=
  { s with fails := (tool, 0) :: s.fails.filter (·.1 != tool) }

def updEntry (sid cid meter : String) (f : MeterEntry → Option MeterEntry) (es : List MeterEntry) :
    List MeterEntry :=
  es.filterMap fun e => if e.meter == meter && e.session == sid && e.call == cid then f e else some e

/-- Section 6, Meters: `no_effect` or a `declined` outcome releases every meter of the call. -/
def releases (outcome : Outcome) (noEffect : Bool) : Bool := noEffect || outcome == .declined

/-- Section 6, Meters: release, or commit the actual cost (else the reservation) on money meters and
1 on calls meters; an overrun's excess is dated at the report. -/
def settleEntry (spec : MeterSpec) (now : Nat) (actual : Option Nat) (release : Bool) (e : MeterEntry) :
    Option MeterEntry :=
  if release then none
  else match spec.unit with
    | .calls => some { e with amount := 1, committed := true }
    | .money _ =>
      let res := e.amount
      let total := actual.getD res
      if total ≤ res then some { e with amount := total, committed := true }
      else some { e with amount := res, excess := total - res, excessAt := now, committed := true }

/-- A retry reuses its entry while the entry is inside the window, else re-times it. -/
def retimeEntry (spec : MeterSpec) (now : Nat) (e : MeterEntry) : Option MeterEntry :=
  if inWindow spec.windowMs e.time now then some e else some { e with time := now }

structure Pool where
  sess : List MeterEntry
  prin : List MeterEntry

def Pool.edit (pl : Pool) (spec : MeterSpec) (f : List MeterEntry → List MeterEntry) : Pool :=
  match spec.scope with
  | .session => { pl with sess := f pl.sess }
  | .principal => { pl with prin := f pl.prin }

def Pool.list (pl : Pool) (spec : MeterSpec) : List MeterEntry :=
  match spec.scope with | .session => pl.sess | .principal => pl.prin

def reserveAll (p : Policy) (r : Requirements) (sid cid : String) (cost : Option Cost) (now : Nat)
    (pl : Pool) : Pool :=
  (metersOf p r).foldl (init := pl) fun pl (n, spec) =>
    pl.edit spec (· ++ [⟨n, sid, cid, now, drawOf spec cost, false, 0, 0⟩])

def forEachMeter (p : Policy) (r : Requirements) (sid cid : String)
    (f : MeterSpec → MeterEntry → Option MeterEntry) (pl : Pool) : Pool :=
  (metersOf p r).foldl (init := pl) fun pl (n, spec) => pl.edit spec (updEntry sid cid n (f spec))

def entryOf (es : List MeterEntry) (meter sid cid : String) : Option MeterEntry :=
  es.find? fun e => e.meter == meter && e.session == sid && e.call == cid

/-- Section 6, Meters: the money meters, in the action's order, on which a committing report's
actual cost is above the reservation. A release reports none. -/
def overrunMeters (p : Policy) (r : Requirements) (c : MCall) (actual : Option Nat) (release : Bool) :
    List String :=
  if release || c.claims == 0 || !actual.any (· > (c.cost.map Cost.amount).getD 0) then []
  else (metersOf p r).filterMap fun (n, spec) => match spec.unit with | .money _ => some n | .calls => none

def overrun (p : Policy) (r : Requirements) (c : MCall) (actual : Option Nat) (release : Bool) : Bool :=
  !(overrunMeters p r c actual release).isEmpty

/-- A committed entry whose reserved part and excess part have both left window `w` at `now`. An
entry dated after `now` (a session whose clock runs ahead) has not left its window. -/
def outsideWindow (w now : Nat) (e : MeterEntry) : Bool :=
  e.committed && now ≥ e.time + w && (e.excess == 0 || now ≥ e.excessAt + w)

/-- Section 6, Ledger pruning: an entry the list of `scope` drops, because the policy defines its
meter in that scope with a window it has left. A meter the policy defines only in the other scope,
or not at all, never prunes, whatever its name. -/
def expired (p : Policy) (scope : MeterScope) (now : Nat) (e : MeterEntry) : Bool :=
  match meterOf p e.meter with
  | some spec => spec.scope == scope && spec.windowMs.any (outsideWindow · now e)
  | none => false

def prune (p : Policy) (scope : MeterScope) (now : Nat) (es : List MeterEntry) : List MeterEntry :=
  es.filter (!expired p scope now ·)

/-- Only a list the step changed is pruned. Returns the list and what it dropped. -/
def pruneChanged (p : Policy) (scope : MeterScope) (now : Nat) (before after : List MeterEntry) :
    List MeterEntry × List MeterEntry :=
  if after == before then (after, []) else (prune p scope now after, after.filter (expired p scope now))

def decisionIs (d : Decision) (ms : List String) : Bool := d == if ms.isEmpty then .none else .overrun ms

/-- Section 6, Propose: the call record keeps guard and escalator values only for declared names. -/
def declaredGuards (r : Requirements) (gs : List (String × Bool)) : List (String × Bool) :=
  gs.filter (r.guards.contains ·.1)

def declaredEscalators (r : Requirements) (es : List (String × Bool)) : List (String × Bool) :=
  es.filter fun (n, _) => r.escalate.any (·.1 == n)

def decisionOf : Verdict → Option Decision
  | .ok d _ => some d
  | .rejected _ => none

def nonDenied : Decision → Bool
  | .allowed | .allowedByGrant _ | .needsApproval _ | .authorized => true
  | _ => false

/-- Apply one accepted step to the session model; principal entries and the tombstone are shared. -/
def MSess.apply (p : Policy) (s : MSess) (pl : Pool) (gtomb : Bool) (e : Event) (d : Decision) :
    MSess × Pool × Bool :=
  let now := e.time
  match e.body with
  | .sessionStart sid _ req perms apprs ledger =>
    let approvers := apprs.foldl (fun acc (id, i) => if acc.any (·.1 == id) then acc else acc ++ [(id, i)]) []
    ({ started := true, sid, requester := req, perms := perms.eraseDups, approvers, tomb := ledger.tombstone },
     pl, gtomb)
  | .sessionEnd =>
    let s := s.mapCalls (toUnknown ∘ voidPending)
    ({ s with ended := true, turnActive := false
              grants := s.grants.fold (init := {}) fun acc k g => acc.insert k { g with dead := true } },
     pl, gtomb)
  | .turnStart ui =>
    ({ s with turnActive := true, turn := s.turn + 1, stepsT := 0, propsT := 0, needsT := 0
              memory := if ui then [] else s.memory }, pl, gtomb)
  | .turnEnd =>
    ({ s with turnActive := false
              grants := s.grants.fold (init := {}) fun acc k g =>
                acc.insert k (if g.scope == .turn then { g with dead := true } else g) }, pl, gtomb)
  | .stepStart => ({ s with stepsT := s.stepsT + 1 }, pl, gtomb)
  | .propose cid tool digest cost guards esc =>
    if s.calls.contains cid then (s, pl, gtomb)
    else if (reqOf p tool).isNone then
      -- Section 6, Propose: an undefined tool leaves no record whatever the disposition, and still
      -- counts toward the proposal limits.
      ({ s with propsT := s.propsT + 1, propsS := s.propsS + 1
                unrecorded := if s.unrecorded.contains cid then s.unrecorded else s.unrecorded ++ [cid] }, pl, gtomb)
    else
      let r? := reqOf p tool
      let enforce := enforced p r?
      let consent := match r? with | some r => consentAt r cost esc | none => {}
      let st : St := match d with
        | .allowed | .allowedByGrant _ => .authorized
        | .needsApproval _ => .awaiting
        | _ => .ended
      let grant := match d with | .allowedByGrant g => some g | _ => none
      let covered := match grant, r? with
        | some g, some r => s.grantCovers p g r consent tool digest cost esc now
        | _, _ => false
      let needs := match d with | .needsApproval _ => enforce | _ => false
      let c : MCall :=
        { tool, req := r?, enforce, epoch := s.epoch, proposedAt := now, pDigest := digest, pCost := cost
          pGuards := (r?.map (declaredGuards · guards)).getD [], pEsc := (r?.map (declaredEscalators · esc)).getD []
          disposition := d, consent, digest, cost, genStart := now, gens := [digest], st
          authorizedAt := if st == .authorized then some now else none, grant, grantCovered := covered
          term := match d with | .denied why => some (.denied why) | _ => none }
      let s := { s with propsT := s.propsT + 1, propsS := s.propsS + 1
                        needsT := s.needsT + (if needs then 1 else 0), needsS := s.needsS + (if needs then 1 else 0) }
      (s.setCall cid c, pl, gtomb)
  | .approve cid _ who rd rc edit =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c =>
      let pr := ((s.info? who).map (·.principal)).getD who
      let c := match edit with
        | some ed =>
          let nc := match ed.newCost with | some x => some x | none => c.cost
          let raised := match c.req with | some r => consentAt r nc ed.escalators | none => {}
          { c with gen := c.gen + 1, genStart := now, gens := c.gens ++ [ed.newDigest], digest := ed.newDigest
                   cost := nc, consent := joinC c.consent raised, edited := true
                   approvals := c.approvals ++ [⟨who, pr, c.gen + 1, now, ed.newDigest, nc⟩] }
        | none => { c with approvals := c.approvals ++ [⟨who, pr, c.gen, now, rd, rc⟩] }
      let c := match d with
        | .authorized => { c with st := .authorized, approved := true, authorizedAt := some now }
        | .denied why => { c with st := .ended, term := some (if why == .approvalExpired then .expired else .denied why) }
        | _ => c
      (s.setCall cid c, pl, gtomb)
  | .reject cid rid who =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c =>
      let byElig := match s.info? who with
        | some info => (clausesOf c.consent).any (eligibleFor p s.requester info)
        | none => false
      let echoed := (c.gens[rid.generation]?).toList
      let pairs := ([c.pDigest, c.digest] ++ echoed).map (c.tool, ·)
      let memory := pairs.foldl (fun m x => if m.contains x then m else m ++ [x]) s.memory
      let s := s.setCall cid { c with st := .ended, term := some .rejected, vetoedByEligible := c.vetoedByEligible || byElig }
      ({ s with memory }, pl, gtomb)
  | .approvalExpire cid _ =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c => (s.setCall cid { c with st := .ended, term := some .expired }, pl, gtomb)
  | .grantCreate gid who tool digest scope maxUses maxCost nb exp _ =>
    let g : MGrant := { creator := who, creatorInfo := s.info? who, tool, digest, scope, maxUses, maxCost
                        notBefore := nb, expiresAt := exp, epoch := s.epoch, turn := s.turn }
    ({ s with grants := s.grants.insert gid g }, pl, gtomb)
  | .grantRevoke gid =>
    match s.grants[gid]? with
    | none => (s, pl, gtomb)
    | some g => ({ s with grants := s.grants.insert gid { g with revoked := true } }, pl, gtomb)
  | .approverAttest id info =>
    (if s.approvers.any (·.1 == id) then s else { s with approvers := s.approvers ++ [(id, info)] }, pl, gtomb)
  | .permissionAdd perm _ => ({ s with perms := if s.perms.contains perm then s.perms else s.perms ++ [perm] }, pl, gtomb)
  | .permissionRevoke perm => ({ s with perms := s.perms.filter (· != perm) }, pl, gtomb)
  | .dispatch cid attempt _ _ _ _ =>
    match s.calls[cid]?, d with
    | some c, .dispatchClaimed =>
      let r := c.req.getD {}
      let pl := if c.claims == 0 then reserveAll p r s.sid cid c.cost now pl
        else forEachMeter p r s.sid cid (fun spec en => retimeEntry spec now en) pl
      let s := match c.grant, c.claims == 0 with
        | some gid, true => match s.grants[gid]? with
          | some g =>
            let g := { g with firstClaims := g.firstClaims + 1
                              claimedCost := g.claimedCost + ((c.cost.map Cost.amount).getD 0) }
            { s with grants := s.grants.insert gid g }
          | none => s
        | _, _ => s
      (s.setCall cid { c with claims := c.claims + 1, lastAttempt := attempt, st := .dispatched }, pl, gtomb)
    | some c, .dispatchDenied why =>
      let term : CallStatus := if why == .authorizationExpired then .expired else .deniedAtDispatch why
      (s.setCall cid { c with st := .ended, term := some term }, pl, gtomb)
    | _, _ => (s, pl, gtomb)
  | .result cid outcome actual noEffect =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c =>
      let r := c.req.getD {}
      let rel := releases outcome noEffect
      let pl := forEachMeter p r s.sid cid (fun spec en => settleEntry spec now actual rel en) pl
      let over := overrun p r c actual rel
      let s := if over || outcome == .failed then s.fail p c.tool
        else if outcome == .succeeded then s.succeed c.tool else s
      let term : CallStatus := match outcome with | .succeeded => .succeeded | .failed => .failed | .declined => .declined
      (s.setCall cid { c with st := .ended, term := some term, released := rel }, pl, gtomb)
  | .outcomeUnknown cid =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c => ((s.setCall cid { c with st := .unknown, unknowns := c.unknowns + 1 }).fail p c.tool, pl, gtomb)
  | .reconcile cid outcome actual noEffect =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c =>
      let r := c.req.getD {}
      let rel := releases outcome noEffect
      let pl := forEachMeter p r s.sid cid (fun spec en => settleEntry spec now actual rel en) pl
      let s := s.setCall cid { c with reconciled := true, released := rel }
      (if overrun p r c actual rel then s.fail p c.tool else s, pl, gtomb)
  | .cancel cid =>
    match s.calls[cid]? with
    | none => (s, pl, gtomb)
    | some c => (s.setCall cid { c with st := .ended, term := some .cancelled }, pl, gtomb)
  | .escalationAck _ _ => ({ s with fails := [], total := 0, sessBlocked := false, blocked := [] }, pl, gtomb)
  | .ledgerSync ledger =>
    let s := if ledger.tombstone && !s.tomb then s.mapCalls voidPending else s
    -- Section 6, Ledger: only an ended session accepts a sync that clears the tombstone.
    ({ s with tomb := if s.ended then ledger.tombstone else s.tomb || ledger.tombstone }, pl, gtomb)
  | .reset =>
    let s := s.mapCalls (toUnknown ∘ voidPending)
    ({ s with epoch := s.epoch + 1
              grants := s.grants.fold (init := {}) fun acc k g => acc.insert k { g with dead := true } }, pl, gtomb)
  | .kill =>
    let s := s.mapCalls voidPending
    let t := p.killSetsTombstone
    ({ s with killed := true, tomb := s.tomb || t }, pl, gtomb || t)

/-- Section 6, Kill: the only events a killed or tombstoned session still accepts. -/
def openWhenKilled : EventBody → Bool
  | .propose .. | .kill | .sessionEnd | .result .. | .outcomeUnknown _ | .reconcile .. | .ledgerSync _ => true
  | _ => false

def MSess.halted (s : MSess) : Bool := s.killed || s.tomb

/-- Section 6, Protocol errors: the reason naming a call's status. These are codes rather than
`Reason` constructors so the model does not depend on which constructors the kernel defines. -/
def St.stageCode : St → String
  | .awaiting => "call_awaiting"
  | .authorized => "call_authorized"
  | .dispatched => "call_dispatched"
  | .unknown => "call_unknown"
  | .ended => "call_ended"

def stageCodes : List String :=
  ["call_awaiting", "call_authorized", "call_dispatched", "call_unknown", "call_ended", "retry_not_allowed",
   "already_reconciled"]

/-- The codes a call-scoped event is rejected with when it does not fit the call's status, or
`none` when it fits. On an Unknown call, `retry_not_allowed` and `already_reconciled` take
precedence over `call_unknown`; the spec orders neither before the other. -/
def stageExpect (b : EventBody) (k : MCall) : Option (List String) :=
  let own := some [k.st.stageCode]
  match b with
  | .dispatch .. =>
    match k.st with
    | .authorized => none
    | .unknown =>
      let codes := (if (k.req.getD {}).retryAfterUnknown then [] else ["retry_not_allowed"])
        ++ (if k.reconciled then ["already_reconciled"] else [])
      if codes.isEmpty then none else some codes
    | _ => own
  | .result .. | .outcomeUnknown _ => if k.st == .dispatched then none else own
  | .reconcile .. =>
    if k.st != .unknown then own else if k.reconciled then some ["already_reconciled"] else none
  | .cancel _ | .reject .. => if k.st == .awaiting || k.st == .authorized then none else own
  | .approve .. | .approvalExpire .. => if k.st == .awaiting then none else own
  | _ => none

def Model.session (m : Model) (inst : Nat) : MSess := (m.sess[inst]?).getD {}

/-- Whether a step wrote the stored ledger: an accepted step other than `ledgerSync` and
`sessionStart` (which only read it) that changed the ledger version. -/
def writesLedger (st : TStep) : Bool :=
  (decisionOf st.verdict).isSome && st.post.ledger.version != st.pre.ledger.version
    && (match st.event.body with | .ledgerSync _ | .sessionStart .. => false | _ => true)

def readsStore (st : TStep) : Bool :=
  (decisionOf st.verdict).isSome && (match st.event.body with | .ledgerSync _ | .sessionStart .. => true | _ => false)

/-- A session is current when it has seen every ledger write of the interleaving. -/
def Model.current (m : Model) (inst : Nat) : Bool := (m.seen[inst]?).getD 0 == m.writes

def Model.apply (p : Policy) (m : Model) : Item → Model
  | .storeClear => { m with tomb := false, writes := m.writes + 1, pruned := [] }
  | .step st =>
    let m := if writesLedger st then
        { m with lastLedgerWriter := some st.inst, writes := m.writes + 1, seen := m.seen.insert st.inst (m.writes + 1) }
      else if readsStore st then { m with seen := m.seen.insert st.inst m.writes } else m
    match decisionOf st.verdict with
    | none => { m with pruned := [] }
    | some d =>
      let s := m.session st.inst
      let pl0 : Pool := ⟨s.entries, m.pentries⟩
      let (s, pl, tomb) := s.apply p pl0 m.tomb st.event d
      let now := st.event.time
      let (sessE, dropS) := pruneChanged p .session now pl0.sess pl.sess
      let (prinE, dropP) := pruneChanged p .principal now pl0.prin pl.prin
      -- Section 6, Ledger and section 7: an accepted ledger_sync brings the session up to the stored
      -- ledger, taken as is and never pruned, so the principal entries and tombstone become the
      -- stored ones, including writes by sessions this trace does not contain.
      let (prinE, tomb) := match st.event.body with
        | .ledgerSync l => (l.entries, l.tombstone)
        | _ => (prinE, tomb)
      { m with sess := m.sess.insert st.inst { s with entries := sessE }, pentries := prinE, tomb
               pruned := dropS ++ dropP }

def Model.init (l : Ledger) : Model := { pentries := l.entries, tomb := l.tombstone }

end Writ.Checks
