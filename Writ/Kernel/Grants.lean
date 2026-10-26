import Writ.Kernel.Eligibility

namespace Writ

def GrantRec.validAt (g : GrantRec) (s : State) (time : Nat) : Bool :=
  !g.revoked && g.epoch == s.epoch
    && g.notBefore.all (· ≤ time) && g.expiresAt.all (time < ·)
    && (g.scope != .turn || (s.turnActive && g.turn == s.turnIndex))

def GrantRec.coversCost (g : GrantRec) (cost : Option Cost) : Bool :=
  match g.maxCost with
  | Option.none => true
  | some m =>
    match cost with
    | Option.none => false
    | some c => c.currency == m.currency && g.costConsumed + g.costReserved + c.amount ≤ m.amount

def GrantRec.costHeld (g : GrantRec) (cost : Option Cost) : Nat :=
  if g.maxCost.isSome then (cost.map (·.amount)).getD 0 else 0

def State.findGrant (p : Policy) (s : State) (tool digest : String) (c : Consent)
    (cost : Option Cost) (time : Nat) : Option String :=
  (s.grants.toList.find? fun (_, g) =>
    g.validAt s time && g.tool == tool && g.digest.all (· == digest)
      && g.consumed + g.reserved < g.maxUses && g.coversCost cost
      && (s.eligibleAll p c g.approver).isNone).map (·.1)

def State.releaseGrant (s : State) (callId : String) : State :=
  match s.calls.get? callId with
  | some { grant := some gid, attempts := 0, cost, .. } =>
    match s.grants.get? gid with
    | some g =>
      let g := { g with reserved := g.reserved - 1, costReserved := g.costReserved - g.costHeld cost }
      { s with grants := s.grants.insert gid g }
    | Option.none => s
  | _ => s

def State.consumeGrant (s : State) (callId : String) : State :=
  match s.calls.get? callId with
  | some { grant := some gid, attempts := 0, cost, .. } =>
    match s.grants.get? gid with
    | some g =>
      let amt := g.costHeld cost
      let g := { g with reserved := g.reserved - 1, consumed := g.consumed + 1
                        costReserved := g.costReserved - amt, costConsumed := g.costConsumed + amt }
      { s with grants := s.grants.insert gid g }
    | Option.none => s
  | _ => s

end Writ
