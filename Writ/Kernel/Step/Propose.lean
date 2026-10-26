import Writ.Kernel.Meter
import Writ.Kernel.Failures
import Writ.Kernel.Calls

namespace Writ

def exceeded (n : Option Nat) (count : Nat) : Bool :=
  match n with
  | some n => decide (count ≥ n)
  | Option.none => false

def costShapeDenial (spec : MeterSpec) (cost : Option Cost) : Option Reason :=
  match spec.unit, cost with
  | .calls, _ => Option.none
  | .money _, Option.none => some .costMissing
  | .money currency, some c =>
    if c.currency ≠ currency then some .currencyMismatch
    else if spec.maxPerCall.any (c.amount > ·) then some .costAbovePerCall
    else Option.none

def meterShapeDenial (p : Policy) (m : String) (cost : Option Cost) : Option Reason :=
  match p.meter? m with
  | Option.none => some .meterExceeded -- unknown meter: fail closed rather than spend unmetered
  | some spec => costShapeDenial spec cost

/-- Cost problems on any meter come before room, so a request the host must fix is not reported
as a transient `meterExceeded`. -/
def metersDenial (p : Policy) (s : State) (time : Nat) (meters : List String) (cost : Option Cost) :
    Option Reason :=
  match meters.findSome? (meterShapeDenial p · cost) with
  | some r => some r
  | Option.none => if meters.all (s.hasRoom p time · cost) then Option.none else some .meterExceeded

def preConsentDenial (p : Policy) (s : State) (time : Nat) (r : Requirements) (tool digest : String)
    (cost : Option Cost) (guards : List (String × Bool)) : Option Reason :=
  if exceeded p.limits.maxProposalsPerSession s.proposalsThisSession then some .sessionProposalLimit
  else if exceeded p.limits.maxProposalsPerTurn s.proposalsThisTurn then some .proposalLimit
  else if (r.permission.any (· ∉ s.permissions)) then some .permissionMissing
  else if r.guards.any (lookupFlag guards · ≠ some true) then some .guardFalse
  else
    match metersDenial p s time r.meters cost with
    | some d => some d
    | Option.none => if (tool, digest) ∈ s.rejectedMemory then some .previouslyRejected else Option.none

/-- What the enforce-mode rules decide for a new proposal, before shadow mode is applied. -/
inductive Disposition where
  | allowed | allowedByGrant (grant : String) | needsApproval (rid : RequestId) | denied (r : Reason)
  deriving DecidableEq, Repr

def Disposition.decision : Disposition → Decision
  | .allowed => .allowed
  | .allowedByGrant g => .allowedByGrant g
  | .needsApproval rid => .needsApproval rid
  | .denied r => .denied r

def Disposition.status : Disposition → CallStatus
  | .allowed | .allowedByGrant _ => .authorized
  | .needsApproval _ => .awaiting
  | .denied r => .denied r

def Disposition.grant : Disposition → Option String
  | .allowedByGrant g => some g
  | _ => Option.none

def Disposition.needsApproval? : Disposition → Bool
  | .needsApproval _ => true
  | _ => false

def Disposition.shadowed (mode : Mode) (d : Disposition) : Disposition × Option Shadow :=
  match mode, d with
  | .logOnly, .denied r =>
    if r = .killed ∨ r = .unknownTool ∨ r = .notExposed then (d, Option.none)
    else (.allowed, some (.wouldDeny r))
  | .logOnly, .needsApproval _ => (.allowed, some .wouldNeedApproval)
  | _, _ => (d, Option.none)

def enforceDecision (p : Policy) (s : State) (time : Nat) (callId tool digest : String)
    (cost : Option Cost) (guards escalators : List (String × Bool)) : Disposition × Consent :=
  let r := (p.action? tool).getD {}
  if s.killed || s.ledger.tombstone then (.denied .killed, r.consent)
  else if (p.action? tool).isNone then (.denied .unknownTool, .none)
  else if !r.exposed then (.denied .notExposed, r.consent)
  else if s.blocked tool then (.denied .escalated, r.consent)
  else
    match preConsentDenial p s time r tool digest cost guards with
    | some d => (.denied d, r.consent)
    | Option.none =>
      let c := r.effectiveConsent cost escalators
      if c.clauses.isEmpty then (.allowed, c)
      else
        let grant := if c.single && r.firedGrantable escalators then s.findGrant p tool digest c cost time
          else Option.none
        match grant with
        | some g => (.allowedByGrant g, c)
        | Option.none =>
          if exceeded p.limits.maxApprovalRequestsPerSession s.approvalsThisSession then
            (.denied .sessionApprovalBudget, c)
          else if exceeded p.limits.maxApprovalRequestsPerTurn s.approvalsThisTurn then
            (.denied .approvalBudget, c)
          else (.needsApproval ⟨s.sessionId, callId, 0⟩, c)

/-- The terminal denials of an authorized call's re-evaluation, authorization expiry first, as
dispatch checks them. A repeated propose checks permission before calling this, so it reports
`permissionMissing` ahead of `authorizationExpired`. The status is what a first attempt moves to. -/
def authorizedDenial (p : Policy) (s : State) (time : Nat) (r : Requirements) (rec : CallRec)
    (retry : Bool) : Option (Reason × CallStatus) :=
  if (p.authorizedTtl r).any (time ≥ rec.authorizedAt.getD 0 + ·) then
    some (.authorizationExpired, .expired)
  else if r.permission.any (· ∉ s.permissions) then
    some (.permissionMissing, .deniedAtDispatch .permissionMissing)
  else if !retry && decide ((rec.tool, rec.digest) ∈ s.rejectedMemory) then
    some (.previouslyRejected, .deniedAtDispatch .previouslyRejected)
  else if rec.grant.any (fun gid => !(s.grants.get? gid).any (·.validAt s time)) then
    some (.grantInvalid, .deniedAtDispatch .grantInvalid)
  else Option.none

def repeatDecision (p : Policy) (s : State) (time : Nat) (callId : String) (rec : CallRec) :
    Decision × Option Shadow :=
  let r := (p.action? rec.tool).getD {}
  let current : Decision := match rec.status with
    | .awaiting => .needsApproval ⟨s.sessionId, callId, rec.generation⟩
    | .authorized => if rec.tally.isEmpty then rec.decision else .authorized
    | .denied x => .denied x
    | st => .existing st
  let pending := rec.status = .awaiting ∨ rec.status = .authorized
  let denial :=
    if s.blocked rec.tool then some .escalated
    else if pending ∧ r.permission.any (· ∉ s.permissions) then some .permissionMissing
    else if rec.status = .authorized then (authorizedDenial p s time r rec false).map (·.1)
    else Option.none
  if s.killed || s.ledger.tombstone then (.denied .killed, Option.none)
  else match denial, p.modeOf rec.tool with
    | some x, .enforce => (.denied x, Option.none)
    | some x, .logOnly => (current, some (.wouldDeny x))
    | Option.none, _ => (current, if rec.status = .authorized then rec.shadow else Option.none)

def handlePropose (p : Policy) (s : State) (time : Nat) (callId tool digest : String)
    (cost : Option Cost) (guards escalators : List (String × Bool)) : State × Verdict :=
  match s.calls.get? callId with
  | some rec =>
    if rec.tool = tool ∧ ((rec.proposedDigest, rec.proposedCost) = (digest, cost)
        ∨ (rec.digest, rec.cost) = (digest, cost)) then
      let (d, shadow) := repeatDecision p s time callId rec
      (s, .ok d shadow)
    else (s, .rejected .duplicateCall)
  | Option.none =>
    let (d, c) := enforceDecision p s time callId tool digest cost guards escalators
    let counted := { s with
      proposalsThisTurn := s.proposalsThisTurn + 1
      proposalsThisSession := s.proposalsThisSession + 1 }
    match p.action? tool with
    -- killed or unknownTool, neither of which log-only mode softens; no record keeps a host from
    -- filling the state with calls to names the policy never defined
    | Option.none => (counted, .ok d.decision Option.none)
    | some r =>
      let mode := p.modeOf tool
      let (d', shadow) := d.shadowed mode
      let status := d'.status
      let grant := d'.grant
      -- a log-only action's would-need-approval must not use up the live budget
      let needsApproval := d.needsApproval? && mode == .enforce
      let entry : CallRec :=
        { tool, epoch := s.epoch, proposedDigest := digest, proposedCost := cost
          proposedGuards := guards.filter (r.guards.contains ·.1)
          proposedEscalators := escalators.filter fun (n, _) => r.escalate.any (·.1 == n)
          decision := d'.decision, shadow, consent := c, digest, cost, status
          generations := [(digest, cost)]
          requestedAt := if status = .awaiting then time else 0
          authorizedAt := if status = .authorized then some time else Option.none
          grant }
      let grants := match grant with
        | some gid => s.grants.modify gid fun g =>
          { g with reserved := g.reserved + 1, costReserved := g.costReserved + g.costHeld cost }
        | Option.none => s.grants
      ({ counted with
          grants
          calls := s.calls.insert callId entry
          approvalsThisTurn := s.approvalsThisTurn + if needsApproval then 1 else 0
          approvalsThisSession := s.approvalsThisSession + if needsApproval then 1 else 0 },
       .ok d'.decision shadow)

end Writ
