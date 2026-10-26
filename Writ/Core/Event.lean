import Writ.Core.Policy

namespace Writ

inductive ApproverKind where | human | automated deriving DecidableEq, Repr

structure ApproverInfo where
  principal : String
  kind : ApproverKind
  roles : List String
  deriving DecidableEq, Repr

structure MeterEntry where
  meter : String
  session : String
  call : String
  time : Nat
  amount : Nat
  committed : Bool
  excess : Nat := 0
  excessAt : Nat := 0
  deriving DecidableEq, Repr

structure Ledger where
  version : Nat := 0
  entries : List MeterEntry := []
  tombstone : Bool := false
  deriving DecidableEq, Repr

structure RequestId where
  session : String
  call : String
  generation : Nat
  deriving DecidableEq, Repr

/-- `escalators` are host-recomputed for the edited arguments; a missing name counts as true. -/
structure Edit where
  newDigest : String
  newCost : Option Cost := none
  escalators : List (String × Bool) := []
  deriving DecidableEq, Repr

inductive Outcome where | succeeded | failed | declined deriving DecidableEq, Repr

inductive EventBody where
  | sessionStart (sessionId policyDigest requester : String) (permissions : List String)
      (approvers : List (String × ApproverInfo)) (ledger : Ledger)
  | sessionEnd
  | turnStart (userInitiated : Bool)
  | turnEnd
  | stepStart
  | propose (callId tool digest : String) (cost : Option Cost)
      (guards : List (String × Bool)) (escalators : List (String × Bool))
  | approve (callId : String) (requestId : RequestId) (approver reviewedDigest : String)
      (reviewedCost : Option Cost) (edit : Option Edit)
  | reject (callId : String) (requestId : RequestId) (approver : String)
  | approvalExpire (callId : String) (requestId : RequestId)
  | grantCreate (grantId approver tool : String) (digest : Option String) (scope : GrantScope)
      (maxUses : Nat) (maxCost : Option Cost) (notBefore expiresAt : Option Nat) (reviewedScopeDigest : String)
  | grantRevoke (grantId : String)
  | approverAttest (approver : String) (info : ApproverInfo)
  | permissionAdd (permission approver : String)
  | permissionRevoke (permission : String)
  | dispatch (callId : String) (attempt : Nat) (digest : String) (cost : Option Cost)
      (guards : List (String × Bool)) (idempotencyKey : String)
  | result (callId : String) (outcome : Outcome) (actualCost : Option Nat) (noEffect : Bool)
  | outcomeUnknown (callId : String)
  | reconcile (callId : String) (outcome : Outcome) (actualCost : Option Nat) (noEffect : Bool)
  | cancel (callId : String)
  | escalationAck (approver : String) (escalation : Nat)
  | ledgerSync (ledger : Ledger)
  | reset
  | kill
  deriving DecidableEq, Repr

structure Event where
  seq : Nat
  time : Nat
  stateVersion : Nat
  origin : Option String := none
  body : EventBody
  deriving DecidableEq, Repr

def lookupFlag (m : List (String × Bool)) (k : String) : Option Bool := List.lookup k m

end Writ
