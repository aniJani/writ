import Std.Data.ExtTreeMap
import Writ.Core.Reason
import Writ.Core.Event

namespace Writ

inductive CallStatus where
  | denied (r : Reason) | awaiting | authorized | dispatched | succeeded | failed | declined
  | unknown | rejected | expired | deniedAtDispatch (r : Reason) | cancelled
  deriving DecidableEq, Repr

inductive Decision where
  | none | pending | authorized | allowed | allowedByGrant (grant : String)
  | needsApproval (rid : RequestId) | denied (r : Reason)
  | dispatchClaimed | dispatchDenied (r : Reason) | existing (status : CallStatus)
  | overrun (meters : List String)
  deriving DecidableEq, Repr

inductive Shadow where | wouldDeny (r : Reason) | wouldNeedApproval deriving DecidableEq, Repr

inductive Verdict where
  | ok (d : Decision) (shadow : Option Shadow)
  | rejected (r : Reason)
  deriving DecidableEq, Repr

def CallStatus.terminal : CallStatus → Bool
  | .awaiting | .authorized | .dispatched => false
  | _ => true

structure CallRec where
  tool : String
  epoch : Nat
  proposedDigest : String
  proposedCost : Option Cost
  proposedGuards : List (String × Bool)
  proposedEscalators : List (String × Bool)
  decision : Decision
  shadow : Option Shadow
  consent : Consent
  digest : String
  cost : Option Cost
  status : CallStatus
  generation : Nat := 0
  generations : List (String × Option Cost)
  tally : List (String × String) := []
  requestedAt : Nat := 0
  authorizedAt : Option Nat := Option.none
  grant : Option String := Option.none
  attempts : Nat := 0
  idempotencyKey : Option String := Option.none
  reconciled : Option Outcome := Option.none
  deriving Repr, BEq

structure GrantRec where
  approver : String
  principal : String
  tool : String
  digest : Option String
  scope : GrantScope
  maxUses : Nat
  consumed : Nat := 0
  reserved : Nat := 0
  maxCost : Option Cost
  costConsumed : Nat := 0
  costReserved : Nat := 0
  notBefore : Option Nat
  expiresAt : Option Nat
  revoked : Bool := false
  epoch : Nat
  turn : Nat
  reviewedScopeDigest : String
  deriving Repr, BEq

structure State where
  expectedPolicyDigest : String
  started : Bool := false
  ended : Bool := false
  sessionId : String := ""
  requester : String := ""
  permissions : List String := []
  approvers : Std.ExtTreeMap String ApproverInfo compare := {}
  epoch : Nat := 0
  lastSeq : Nat := 0
  lastTime : Nat := 0
  version : Nat := 0
  turnActive : Bool := false
  turnIndex : Nat := 0
  stepsThisTurn : Nat := 0
  proposalsThisTurn : Nat := 0
  approvalsThisTurn : Nat := 0
  proposalsThisSession : Nat := 0
  approvalsThisSession : Nat := 0
  calls : Std.ExtTreeMap String CallRec compare := {}
  grants : Std.ExtTreeMap String GrantRec compare := {}
  sessionMeters : List MeterEntry := []
  ledger : Ledger := {}
  killed : Bool := false
  escalated : Bool := false
  failures : Std.ExtTreeMap String Nat compare := {}
  failuresThisSession : Nat := 0
  blockedTools : List String := []
  escalations : Nat := 0
  rejectedMemory : List (String × String) := []
  deriving BEq

def State.initial (policyDigest : String) : State := { expectedPolicyDigest := policyDigest }

end Writ
