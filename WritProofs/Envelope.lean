import WritProofs.Basic

namespace Writ.Proofs

open Writ

def EventBody.isStart : EventBody → Bool
  | .sessionStart .. => true
  | _ => false

/-- Section 6, Ended sessions: the events an ended session still accepts. -/
def EventBody.settles : EventBody → Bool
  | .reconcile .. | .ledgerSync _ => true
  | _ => false

/-- Section 6, Kill: the events accepted while the session is killed or the tombstone is set. -/
def EventBody.openWhenKilled : EventBody → Bool
  | .propose .. | .kill | .sessionEnd | .result .. | .outcomeUnknown _ | .reconcile ..
  | .ledgerSync _ => true
  | _ => false

end Writ.Proofs

namespace Writ.EventBody
export Writ.Proofs.EventBody (isStart settles openWhenKilled)
end Writ.EventBody

namespace Writ.Proofs

open Basic

/-- Section 6, Protocol errors: the envelope checks and then the kill check, which every event
passes before its own rules. -/
def EnvelopeOk (s : State) (e : Event) : Prop :=
  (s.started = true ∨ e.body.isStart = true) ∧
  (s.ended = true → e.body.settles = true) ∧
  ¬(s.started = true ∧ e.body.isStart = true) ∧
  s.lastSeq < e.seq ∧ s.lastTime ≤ e.time ∧ e.stateVersion = s.version ∧
  ((s.killed || s.ledger.tombstone) = true → e.body.openWhenKilled = true)

variable {s : State} {e : Event}

namespace Envelope

theorem ite_none {α : Type _} {q : Prop} [Decidable q] {a : α} {x : Option α} :
    (if q then some a else x) = none ↔ ¬q ∧ x = none := by
  split <;> simp_all

theorem checks {st en sk : Bool} {iS se ow : Bool} {ls sq lt tm sv v : Nat} :
    (if !st && !iS then some Reason.notStarted
      else if en && !se then some .sessionEnded
      else if st && iS then some .alreadyStarted
      else if sq ≤ ls then some .staleSeq
      else if tm < lt then some .timeDecreasing
      else if sv ≠ v then some .stateVersionMismatch
      else if sk && !ow then some .killed
      else Option.none) = Option.none ↔
    (st = true ∨ iS = true) ∧ (en = true → se = true) ∧ ¬(st = true ∧ iS = true) ∧
      ls < sq ∧ lt ≤ tm ∧ sv = v ∧ (sk = true → ow = true) := by
  simp only [ite_none, Nat.not_le, Nat.not_lt, ne_eq, Decidable.not_not, and_true]
  refine and_congr (by cases st <;> cases iS <;> decide)
    (and_congr (by cases en <;> cases se <;> decide)
      (and_congr (by cases st <;> cases iS <;> decide)
        (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))))
  cases sk <;> cases ow <;> decide

end Envelope

theorem envelope_iff : stepEnvelope s e = none ↔ EnvelopeOk s e :=
  Envelope.checks

namespace Envelope

def killedEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .kill⟩ ]

def killedDispatch : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

def killedPropose : Event := ⟨5, 5, 4, none, .propose "c2" "t" "d2" none [] []⟩

#guard (after witnessPolicy "pd" killedEvents).killed
#guard !killedDispatch.body.openWhenKilled && killedPropose.body.openWhenKilled
#guard (step witnessPolicy (after witnessPolicy "pd" killedEvents) killedDispatch).2
  == .rejected .killed
#guard (step witnessPolicy (after witnessPolicy "pd" killedEvents) killedPropose).2
  == .ok (.denied .killed) none

end Envelope

end Writ.Proofs
