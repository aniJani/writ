import Writ.Kernel.Meter

namespace Writ.Proofs

open Writ

/-- Section 6: an entry counts at `now` while `now` is below its time plus `window_ms` (the excess
from `excess_at`), with no lower bound, and always on a meter without a window. -/
def usageAt (spec : MeterSpec) (entries : List MeterEntry) (m : String) (now : Nat) : Nat :=
  ((entries.filter (·.meter = m)).map fun en =>
    (if spec.windowMs.all (en.time + · > now) then en.amount else 0) +
      (if spec.windowMs.all (en.excessAt + · > now) then en.excess else 0)).sum

def entriesOf (p : Policy) (s : State) (m : String) : List MeterEntry :=
  if (p.meter? m).any (·.scope = .principal) then s.ledger.entries else s.sessionMeters

/-- Section 6, Meters: the session's own entries for call `k` on meter `m`. -/
def ownEntries (p : Policy) (s : State) (m k : String) : List MeterEntry :=
  (entriesOf p s m).filter fun en => en.meter = m ∧ en.session = s.sessionId ∧ en.call = k

/-- Section 6's draw of a call on a meter: its cost on a money meter, 1 on a calls meter. -/
def draw (spec : MeterSpec) (cost : Option Cost) : Nat :=
  match spec.unit with
  | .money _ => (cost.map (·.amount)).getD 0
  | .calls => 1

variable {p : Policy} {s : State} {m : String} {t now : Nat} {cost : Option Cost}
  {spec : MeterSpec} {es : List MeterEntry}

namespace Usage

theorem inWindowAt_eq : spec.inWindowAt t now = spec.windowMs.all (t + · > now) := by
  unfold MeterSpec.inWindowAt
  cases spec.windowMs <;> rfl

theorem usageAt_nil : usageAt spec [] m now = 0 := rfl

theorem usageAt_cons {x : MeterEntry} :
    usageAt spec (x :: es) m now =
      (if x.meter = m then
        (if spec.windowMs.all (x.time + · > now) then x.amount else 0) +
          (if spec.windowMs.all (x.excessAt + · > now) then x.excess else 0)
      else 0) + usageAt spec es m now := by
  unfold usageAt
  by_cases hx : x.meter = m <;> simp [hx]

theorem usageAt_append {es' : List MeterEntry} :
    usageAt spec (es ++ es') m now = usageAt spec es m now + usageAt spec es' m now := by
  simp [usageAt, List.filter_append]

theorem foldl_usage (b : Nat) :
    es.foldl (init := b) (fun acc en =>
      if en.meter = m then
        acc + (if spec.inWindow en now then en.amount else 0)
          + (if spec.inWindowAt en.excessAt now then en.excess else 0)
      else acc) = b + usageAt spec es m now := by
  induction es generalizing b with
  | nil => rfl
  | cons x es ih =>
    rw [List.foldl_cons, ih, usageAt_cons]
    by_cases hx : x.meter = m <;> simp [hx, MeterSpec.inWindow, inWindowAt_eq] <;> omega

end Usage

theorem usageAt_eq : usageAt spec es m now = Meter.usage spec es m now := by
  unfold Meter.usage
  rw [Usage.foldl_usage, Nat.zero_add]

namespace Usage

theorem meterEntries_eq : s.meterEntries p m = entriesOf p s m := by
  unfold State.meterEntries entriesOf
  cases p.meter? m with
  | none => rfl
  | some spec => cases h : spec.scope <;> simp [h]

theorem amount_eq : spec.amount cost = draw spec cost := by
  unfold MeterSpec.amount draw
  cases spec.unit <;> rfl

theorem callAmount_eq (hs : p.meter? m = some spec) : p.callAmount m cost = draw spec cost := by
  simp [Policy.callAmount, hs, amount_eq]

end Usage

end Writ.Proofs
