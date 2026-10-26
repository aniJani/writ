import Writ.Kernel.Step.Propose
import Writ.Kernel.Grants

namespace Writ

def grantDenial (p : Policy) (s : State) (time : Nat) (grantId approver tool : String)
    (digest : Option String) (scope : GrantScope) (maxUses : Nat) (maxCost : Option Cost)
    (expiresAt : Option Nat) :
    Option Reason :=
  match p.action? tool with
  | Option.none => if s.grants.contains grantId then some .duplicateGrant else some .unknownTool
  | some r =>
    if s.grants.contains grantId then some .duplicateGrant
    else match r.grantable with
    | Option.none => some .grantNotAllowed
    | some gr =>
      match s.eligibleAll p r.grantConsent approver with
      | some e => some e
      | Option.none =>
        if scope = .turn ∧ !s.turnActive then some .turnState
        else if !scope.le gr.scope || maxUses == 0 || maxCost.any (·.amount == 0) || decide (maxUses > gr.maxUses)
            || (digest.isNone && !gr.anyArgs)
            || (digest.isNone && !r.meters.isEmpty && !gr.allowAnyArgsMetered)
            || gr.maxDurationMs.any (fun d => expiresAt.all (fun x => decide (x > time + d))) then
          some .grantNotAllowed
        else Option.none

def handleGrantCreate (p : Policy) (s : State) (time : Nat) (grantId approver tool : String)
    (digest : Option String) (scope : GrantScope) (maxUses : Nat) (maxCost : Option Cost)
    (notBefore expiresAt : Option Nat) (reviewedScopeDigest : String) : State × Verdict :=
  match grantDenial p s time grantId approver tool digest scope maxUses maxCost expiresAt with
  | some r => (s, .rejected r)
  | Option.none =>
    let principal := ((s.approvers.get? approver).map (·.principal)).getD approver
    ({ s with grants := s.grants.insert grantId {
          approver, principal, tool, digest, scope, maxUses, maxCost, notBefore, expiresAt,
          epoch := s.epoch, turn := s.turnIndex, reviewedScopeDigest } },
     .ok .none Option.none)

def handleGrantRevoke (s : State) (grantId : String) : State × Verdict :=
  match s.grants.get? grantId with
  | Option.none => (s, .rejected .unknownGrant)
  | some g => ({ s with grants := s.grants.insert grantId { g with revoked := true } },
      .ok .none Option.none)

end Writ
