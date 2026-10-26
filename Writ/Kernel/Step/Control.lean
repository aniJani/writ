import Writ.Kernel.Step.Session
import Writ.Kernel.Failures

namespace Writ

def handleReset (s : State) : State × Verdict :=
  ({ s.interrupt with epoch := s.epoch + 1 }, .ok .none Option.none)

def handleKill (p : Policy) (s : State) : State × Verdict :=
  let s := cancelPending s
  let ledger := if p.killSetsTombstone then { s.ledger with tombstone := true, version := s.ledger.version + 1 }
    else s.ledger
  ({ s with killed := true, ledger }, .ok .none Option.none)

def Ledger.setTombstone (l : Ledger) (b : Bool) : Ledger :=
  if l.tombstone = b then l else { l with tombstone := b, version := l.version + 1 }

def handlePermissionAdd (p : Policy) (s : State) (permission approver : String) : State × Verdict :=
  match s.eligibleAny p .none approver with
  | some r => (s, .rejected r)
  | Option.none =>
    if permission ∈ s.permissions then (s, .ok .none Option.none)
    else ({ s with permissions := s.permissions ++ [permission] }, .ok .none Option.none)

def State.escalationEligible (p : Policy) (s : State) (approverId : String) : Option Reason :=
  match s.approvers.get? approverId with
  | Option.none => some .unknownApprover
  | some info =>
    if info.principal != "agent" && info.roles.any (· ∈ p.escalationRoles.getD p.approverRoles) then
      Option.none
    else some .approverNotEligible

def handleEscalationAck (p : Policy) (s : State) (approver : String) (escalation : Nat) :
    State × Verdict :=
  if !s.anyBlocked then (s, .rejected .notEscalated)
  else match s.escalationEligible p approver with
  | some r => (s, .rejected r)
  | Option.none =>
    if escalation ≠ s.escalations then (s, .rejected .staleRequest)
    else
      ({ s with escalated := false, blockedTools := [], failures := {}, failuresThisSession := 0 },
       .ok .none Option.none)

end Writ
