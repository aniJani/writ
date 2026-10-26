import WritProofs.Calls
import WritProofs.Dispatch

namespace Writ.Proofs

open Writ
open Basic

/-- The calls holding a reserved use of grant `gid`: authorized and not yet dispatched. -/
def reservedCalls (s : State) (gid : String) : List String :=
  (s.calls.toList.filter fun x =>
    x.2.grant = some gid ∧ x.2.status = .authorized ∧ x.2.attempts = 0).map (·.1)

/-- The calls that consumed a use of grant `gid`: dispatched at least once. -/
def consumedCalls (s : State) (gid : String) : List String :=
  (s.calls.toList.filter fun x => x.2.grant = some gid ∧ 1 ≤ x.2.attempts).map (·.1)

def costOf (s : State) (ks : List String) : Nat :=
  (ks.map fun k => ((s.calls[k]?.bind (·.cost)).map (·.amount)).getD 0).sum

/-- Section 8, theorem 2 at every state: each grant's counters are exactly what its calls hold,
and they stay within `max_uses` and `max_cost`. -/
structure GrantInv (s : State) : Prop where
  reserved : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g →
    g.reserved = (reservedCalls s gid).length
  consumed : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g →
    g.consumed = (consumedCalls s gid).length
  uses : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g →
    g.consumed + g.reserved ≤ g.maxUses
  costReserved : ∀ (gid : String) (g : GrantRec) (mc : Cost), s.grants[gid]? = some g →
    g.maxCost = some mc → g.costReserved = costOf s (reservedCalls s gid)
  costConsumed : ∀ (gid : String) (g : GrantRec) (mc : Cost), s.grants[gid]? = some g →
    g.maxCost = some mc → g.costConsumed = costOf s (consumedCalls s gid)
  cost : ∀ (gid : String) (g : GrantRec) (mc : Cost), s.grants[gid]? = some g →
    g.maxCost = some mc → g.costConsumed + g.costReserved ≤ mc.amount
  known : ∀ (k : String) (c : CallRec) (gid : String), s.calls[k]? = some c →
    c.grant = some gid → ∃ g, s.grants[gid]? = some g

/-- The costs of the claimed first attempts that use grant `gid`: claimed `dispatch` events of a
call whose record before the event is Authorized with that grant. -/
def grantClaims (p : Policy) (d : String) (es : List Event) (gid : String) : List (Option Cost) :=
  (trace p (State.initial d) es).filterMap fun x =>
    match x.2.1.body with
    | .dispatch k _ _ cost _ _ =>
      match x.1.calls[k]? with
      | some c =>
        if x.2.2.claimed = true ∧ c.status = .authorized ∧ c.grant = some gid then some cost
        else none
      | none => none
    | _ => none

namespace Grants

abbrev GrantMap := Std.ExtTreeMap String GrantRec compare

variable {p : Policy} {d : String} {s s' s₁ s₂ : State} {e : Event} {es : List Event}
  {k gid : String} {c c' : CallRec} {g g' : GrantRec} {m m' : CallMap} {f : CallRec → Nat}
  {o o' : Option CallRec}

def optf (f : CallRec → Nat) (o : Option CallRec) : Nat := (o.map f).getD 0

def tot (m : CallMap) (f : CallRec → Nat) : Nat := (m.toList.map fun x => f x.2).sum

/-- The nonzero values of `f` by key, a list with one entry per key. -/
def nz (m : CallMap) (f : CallRec → Nat) : List (String × Nat) :=
  (m.toList.map fun x => (x.1, f x.2)).filter (·.2 ≠ 0)

theorem sum_nz (L : List (String × CallRec)) :
    (L.map fun x => f x.2).sum =
      (((L.map fun x => (x.1, f x.2)).filter (·.2 ≠ 0)).map (·.2)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases h : f x.2 = 0 <;> simp [h, ih]

theorem tot_nz : tot m f = ((nz m f).map (·.2)).sum := sum_nz _

theorem mem_nz {a : String} {n : Nat} : (a, n) ∈ nz m f ↔ n ≠ 0 ∧ optf f m[a]? = n := by
  unfold nz optf
  simp only [List.mem_filter, List.mem_map, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨b, v⟩, hm, rfl, rfl⟩, hn⟩
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm]
    exact ⟨hn, rfl⟩
  · rintro ⟨hn, hv⟩
    cases ha : m[a]? with
    | none => rw [ha] at hv; exact absurd hv.symm hn
    | some v =>
      rw [ha] at hv
      exact ⟨⟨(a, v), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr ha, rfl, hv⟩, hn⟩

theorem nodup_nz : (nz m f).Nodup := by
  unfold nz
  refine List.Pairwise.filter _ ?_
  have hd := Std.ExtTreeMap.distinct_keys_toList (t := m)
  refine List.Pairwise.map _ (fun a b h he => h ?_) hd
  simp only [Prod.mk.injEq] at he
  rw [he.1]
  exact Std.ReflCmp.compare_self

theorem tot_congr (h : ∀ a : String, optf f m'[a]? = optf f m[a]?) : tot m' f = tot m f := by
  rw [tot_nz, tot_nz]
  refine List.Perm.sum_nat (List.Perm.map _ ?_)
  refine (List.perm_ext_iff_of_nodup nodup_nz nodup_nz).mpr fun ⟨a, n⟩ => ?_
  rw [mem_nz, mem_nz, h]

theorem tot_split (m : CallMap) (k : String) (f : CallRec → Nat) :
    tot m f = (((nz m f).filter (·.1 ≠ k)).map (·.2)).sum + optf f m[k]? := by
  rw [tot_nz]
  have hp : List.Perm (nz m f) ((nz m f).filter (·.1 ≠ k) ++
      (if optf f m[k]? = 0 then [] else [(k, optf f m[k]?)])) := by
    refine (List.perm_ext_iff_of_nodup nodup_nz ?_).mpr fun ⟨a, n⟩ => ?_
    · refine List.nodup_append.mpr ⟨List.Pairwise.filter _ nodup_nz, ?_, ?_⟩
      · split <;> simp
      · intro x hx y hy
        split at hy
        · cases hy
        · rw [List.mem_singleton.mp hy]
          rintro rfl
          simp at hx
    · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
      rw [mem_nz]
      split <;> rename_i h0
      · simp only [List.not_mem_nil, or_false]
        refine ⟨fun hx => ⟨hx, fun he => ?_⟩, fun hx => hx.1⟩
        subst he; exact hx.1 (hx.2.symm.trans h0)
      · simp only [List.mem_singleton, Prod.mk.injEq]
        constructor
        · intro hx
          by_cases he : a = k
          · subst he; exact .inr ⟨rfl, hx.2.symm⟩
          · exact .inl ⟨hx, he⟩
        · rintro (hx | ⟨rfl, rfl⟩)
          · exact hx.1
          · exact ⟨h0, rfl⟩
  rw [(hp.map _).sum_nat, List.map_append, List.sum_append_nat]
  congr 1
  split <;> simp_all

theorem tot_update (h : ∀ a, a ≠ k → m'[a]? = m[a]?) :
    ∃ off, tot m f = off + optf f m[k]? ∧ tot m' f = off + optf f m'[k]? := by
  refine ⟨_, tot_split m k f, ?_⟩
  rw [tot_split m' k f]
  congr 1
  refine List.Perm.sum_nat (List.Perm.map _ ?_)
  refine (List.perm_ext_iff_of_nodup (List.Pairwise.filter _ nodup_nz)
    (List.Pairwise.filter _ nodup_nz)).mpr
    fun ⟨a, n⟩ => ?_
  simp only [List.mem_filter, decide_eq_true_eq, mem_nz]
  constructor
  · rintro ⟨⟨hn, hv⟩, ha⟩; exact ⟨⟨hn, by rw [← h a ha]; exact hv⟩, ha⟩
  · rintro ⟨⟨hn, hv⟩, ha⟩; exact ⟨⟨hn, by rw [h a ha]; exact hv⟩, ha⟩

def amt (c : CallRec) : Nat := (c.cost.map (·.amount)).getD 0

def resN (gid : String) (c : CallRec) : Nat :=
  if c.grant = some gid ∧ c.status = .authorized ∧ c.attempts = 0 then 1 else 0

def conN (gid : String) (c : CallRec) : Nat := if c.grant = some gid ∧ 1 ≤ c.attempts then 1 else 0

def resC (gid : String) (c : CallRec) : Nat :=
  if c.grant = some gid ∧ c.status = .authorized ∧ c.attempts = 0 then amt c else 0

def conC (gid : String) (c : CallRec) : Nat :=
  if c.grant = some gid ∧ 1 ≤ c.attempts then amt c else 0

theorem length_filter (P : CallRec → Prop) [DecidablePred P] (L : List (String × CallRec)) :
    ((L.filter fun x => decide (P x.2)).map (·.1)).length =
      (L.map fun x => if P x.2 then 1 else 0).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases h : P x.2 <;> simp [h, ih] <;> omega

theorem costOf_filter (P : CallRec → Prop) [DecidablePred P] (L : List (String × CallRec))
    (hL : ∀ x ∈ L, s.calls[x.1]? = some x.2) :
    costOf s ((L.filter fun x => decide (P x.2)).map (·.1)) =
      (L.map fun x => if P x.2 then amt x.2 else 0).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have hx := hL x List.mem_cons_self
    have ih := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    unfold costOf at ih ⊢
    by_cases h : P x.2
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.map_cons, List.sum_cons,
        ih, List.map_cons, List.sum_cons, ite_eq_left h, hx]
      rfl
    · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons,
        ite_eq_right h, Nat.zero_add]

theorem length_reserved : (reservedCalls s gid).length = tot s.calls (resN gid) :=
  length_filter (fun c => c.grant = some gid ∧ c.status = .authorized ∧ c.attempts = 0) _

theorem length_consumed : (consumedCalls s gid).length = tot s.calls (conN gid) :=
  length_filter (fun c => c.grant = some gid ∧ 1 ≤ c.attempts) _

theorem cost_reserved : costOf s (reservedCalls s gid) = tot s.calls (resC gid) :=
  costOf_filter (fun c => c.grant = some gid ∧ c.status = .authorized ∧ c.attempts = 0) _
    toList_get

theorem cost_consumed : costOf s (consumedCalls s gid) = tot s.calls (conC gid) :=
  costOf_filter (fun c => c.grant = some gid ∧ 1 ≤ c.attempts) _ toList_get

/-- A grant's counters equal the totals `R`, `C`, `RC`, `CC` its calls hold, within its caps. -/
def Acct (g : GrantRec) (R C RC CC : Nat) : Prop :=
  g.reserved = R ∧ g.consumed = C ∧ g.consumed + g.reserved ≤ g.maxUses ∧
    ∀ mc, g.maxCost = some mc →
      g.costReserved = RC ∧ g.costConsumed = CC ∧ g.costConsumed + g.costReserved ≤ mc.amount

/-- A call not yet dispatched has no attempt, a Dispatched or Unknown one has one, and an Awaiting
one holds no grant. -/
def Ok (c : CallRec) : Prop :=
  (c.status = .awaiting ∨ c.status = .authorized → c.attempts = 0) ∧
    (c.status = .dispatched ∨ c.status = .unknown → 1 ≤ c.attempts) ∧
    (c.status = .awaiting → c.grant = none)

structure Inv' (m : CallMap) (gs : GrantMap) : Prop where
  grants : ∀ (gid : String) (g : GrantRec), gs[gid]? = some g →
    Acct g (tot m (resN gid)) (tot m (conN gid)) (tot m (resC gid)) (tot m (conC gid))
  known : ∀ (k : String) (c : CallRec) (gid : String), m[k]? = some c → c.grant = some gid →
    ∃ g, gs[gid]? = some g
  recs : ∀ (k : String) (c : CallRec), m[k]? = some c → Ok c

def Inv (s : State) : Prop := Inv' s.calls s.grants

theorem Inv.grantInv (h : Inv s) : GrantInv s where
  reserved gid g hg := by rw [length_reserved]; exact (h.grants gid g hg).1
  consumed gid g hg := by rw [length_consumed]; exact (h.grants gid g hg).2.1
  uses gid g hg := (h.grants gid g hg).2.2.1
  costReserved gid g mc hg hm := by rw [cost_reserved]; exact ((h.grants gid g hg).2.2.2 mc hm).1
  costConsumed gid g mc hg hm := by
    rw [cost_consumed]; exact ((h.grants gid g hg).2.2.2 mc hm).2.1
  cost gid g mc hg hm := ((h.grants gid g hg).2.2.2 mc hm).2.2
  known := h.known

/-- What a step leaves of a call record that the grant counters read. -/
def SameView (c c' : CallRec) : Prop :=
  c'.grant = c.grant ∧ (c.grant ≠ none →
    (c'.status = .authorized ∧ c'.attempts = 0 ↔ c.status = .authorized ∧ c.attempts = 0) ∧
    (1 ≤ c'.attempts ↔ 1 ≤ c.attempts) ∧ c'.cost = c.cost)

/-- A new record must hold no grant: only a propose with a reserved use makes one that does. -/
def CallMove : Option CallRec → Option CallRec → Prop
  | some c, some c' => SameView c c' ∧ (Ok c → Ok c')
  | none, some c' => c'.grant = none ∧ Ok c'
  | none, none => True
  | some _, none => False

def SameG (g g' : GrantRec) : Prop :=
  g'.reserved = g.reserved ∧ g'.consumed = g.consumed ∧ g'.costReserved = g.costReserved ∧
    g'.costConsumed = g.costConsumed ∧ g'.maxUses = g.maxUses ∧ g'.maxCost = g.maxCost

def GrantMove : Option GrantRec → Option GrantRec → Prop
  | some g, some g' => SameG g g'
  | none, none => True
  | _, _ => False

/-- A step that leaves every grant counter and every call's view alone. -/
structure Idle (s s' : State) : Prop where
  calls : ∀ k : String, CallMove s.calls[k]? s'.calls[k]?
  grants : ∀ gid : String, GrantMove s.grants[gid]? s'.grants[gid]?

def CalmG (g g' : GrantRec) : Prop :=
  g'.consumed = g.consumed ∧ g'.costConsumed = g.costConsumed ∧ g'.maxUses = g.maxUses ∧
    g'.maxCost = g.maxCost

/-- Only a claim consumes: a step without one keeps every grant's consumed counters, and a grant it
creates starts with none. -/
def CalmMove : Option GrantRec → Option GrantRec → Prop
  | some g, some g' => CalmG g g'
  | none, some g' => g'.consumed = 0 ∧ g'.costConsumed = 0
  | none, none => True
  | some _, none => False

def Calm (s s' : State) : Prop := ∀ gid : String, CalmMove s.grants[gid]? s'.grants[gid]?

def Good (s s' : State) : Prop := Inv s → Inv s' ∧ Calm s s'

theorem view_eq (h : SameView c c') :
    resN gid c' = resN gid c ∧ conN gid c' = conN gid c ∧ resC gid c' = resC gid c ∧
      conC gid c' = conC gid c := by
  obtain ⟨hg, hv⟩ := h
  cases hc : c.grant with
  | none => simp [resN, conN, resC, conC, hg, hc]
  | some x =>
    obtain ⟨h₁, h₂, h₃⟩ := hv (by rw [hc]; nofun)
    simp [resN, conN, resC, conC, hg, hc, amt, h₃, h₁, h₂]

theorem CallMove.optf (h : CallMove o o') :
    optf (resN gid) o' = optf (resN gid) o ∧ optf (conN gid) o' = optf (conN gid) o ∧
      optf (resC gid) o' = optf (resC gid) o ∧ optf (conC gid) o' = optf (conC gid) o := by
  match o, o', h with
  | some c, some c', ⟨hv, _⟩ =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := view_eq (gid := gid) hv
    simp [Grants.optf, h₁, h₂, h₃, h₄]
  | none, some c', ⟨hg, _⟩ => simp [Grants.optf, resN, conN, resC, conC, hg]
  | none, none, _ => simp

theorem Idle.inv (hi : Inv s) (h : Idle s s') : Inv s' := by
  have ht : ∀ gid, tot s'.calls (resN gid) = tot s.calls (resN gid) ∧
      tot s'.calls (conN gid) = tot s.calls (conN gid) ∧
      tot s'.calls (resC gid) = tot s.calls (resC gid) ∧
      tot s'.calls (conC gid) = tot s.calls (conC gid) := fun gid =>
    ⟨tot_congr fun a => ((h.calls a).optf).1, tot_congr fun a => ((h.calls a).optf).2.1,
     tot_congr fun a => ((h.calls a).optf).2.2.1, tot_congr fun a => ((h.calls a).optf).2.2.2⟩
  refine ⟨fun gid g' hg' => ?_, fun k c' gid hk hc => ?_, fun k c' hk => ?_⟩
  · have hm := h.grants gid
    rw [hg'] at hm
    cases hg : s.grants[gid]? with
    | none => rw [hg] at hm; exact hm.elim
    | some g =>
      rw [hg] at hm
      obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆⟩ := hm
      obtain ⟨t₁, t₂, t₃, t₄⟩ := ht gid
      obtain ⟨a₁, a₂, a₃, a₄⟩ := hi.grants gid g hg
      refine ⟨by rw [r₁, t₁]; exact a₁, by rw [r₂, t₂]; exact a₂, by rw [r₁, r₂, r₅]; exact a₃,
        fun mc hmc => ?_⟩
      obtain ⟨b₁, b₂, b₃⟩ := a₄ mc (by rw [← r₆]; exact hmc)
      exact ⟨by rw [r₃, t₃]; exact b₁, by rw [r₄, t₄]; exact b₂, by rw [r₃, r₄]; exact b₃⟩
  · have hm := h.calls k
    rw [hk] at hm
    cases ho : s.calls[k]? with
    | none => rw [ho] at hm; exact absurd (hm.1 ▸ hc) nofun
    | some c =>
      rw [ho] at hm
      obtain ⟨g, hg⟩ := hi.known k c gid ho (by rw [← hm.1.1]; exact hc)
      have hgm := h.grants gid
      rw [hg] at hgm
      cases hg' : s'.grants[gid]? with
      | none => rw [hg'] at hgm; exact hgm.elim
      | some g' => exact ⟨g', rfl⟩
  · have hm := h.calls k
    rw [hk] at hm
    cases ho : s.calls[k]? with
    | none => rw [ho] at hm; exact hm.2
    | some c => rw [ho] at hm; exact hm.2 (hi.recs k c ho)

theorem Idle.calm (h : Idle s s') : Calm s s' := fun gid =>
  match s.grants[gid]?, s'.grants[gid]?, h.grants gid with
  | some _, some _, ⟨_, h₂, _, h₄, h₅, h₆⟩ => ⟨h₂, h₄, h₅, h₆⟩
  | none, none, _ => trivial
  | some _, none, h => h.elim
  | none, some _, h => h.elim

theorem Idle.good (h : Idle s s') : Good s s' := fun hi => ⟨h.inv hi, h.calm⟩

theorem Idle.refl : Idle s s :=
  ⟨fun k => by
    cases hk : s.calls[k]? with
    | none => trivial
    | some c => exact ⟨⟨rfl, fun _ => ⟨Iff.rfl, Iff.rfl, rfl⟩⟩, id⟩,
   fun gid => by
    cases hg : s.grants[gid]? with
    | none => trivial
    | some g => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem Idle.congr (h : Idle s s₁) (hc : s₂.calls = s₁.calls) (hg : s₂.grants = s₁.grants) :
    Idle s s₂ := ⟨fun k => hc ▸ h.calls k, fun gid => hg ▸ h.grants gid⟩

theorem Idle.of_eq (hc : s'.calls = s.calls) (hg : s'.grants = s.grants) : Idle s s' :=
  Idle.refl.congr hc hg

theorem Inv.congr (h : Inv s₁) (hc : s₂.calls = s₁.calls) (hg : s₂.grants = s₁.grants) :
    Inv s₂ := by
  unfold Inv; rw [hc, hg]; exact h

theorem Calm.congr (h : Calm s s₁) (hg : s₂.grants = s₁.grants) : Calm s s₂ := by
  unfold Calm; rw [hg]; exact h

theorem Good.congr (h : Good s s₁) (hc : s₂.calls = s₁.calls) (hg : s₂.grants = s₁.grants) :
    Good s s₂ := fun hi => ⟨(h hi).1.congr hc hg, (h hi).2.congr hg⟩

theorem CalmMove.trans : ∀ {a b c : Option GrantRec}, CalmMove a b → CalmMove b c → CalmMove a c
  | some _, some _, some _, ⟨a₁, a₂, a₃, a₄⟩, ⟨b₁, b₂, b₃, b₄⟩ =>
    ⟨b₁.trans a₁, b₂.trans a₂, b₃.trans a₃, b₄.trans a₄⟩
  | none, some _, some _, ⟨a₁, a₂⟩, ⟨b₁, b₂, _, _⟩ => ⟨b₁.trans a₁, b₂.trans a₂⟩
  | none, none, _, _, h => h
  | some _, none, _, h, _ => h.elim
  | _, some _, none, _, h => h.elim

theorem Good.trans (h : Good s s₁) (h' : Good s₁ s₂) : Good s s₂ := fun hi =>
  ⟨(h' (h hi).1).1, fun gid => ((h hi).2 gid).trans ((h' (h hi).1).2 gid)⟩

theorem Good.refl : Good s s := Idle.refl.good

theorem zero_of_ne {x : String} (h : c.grant = some gid) (hx : x ≠ gid) :
    resN x c = 0 ∧ conN x c = 0 ∧ resC x c = 0 ∧ conC x c = 0 := by
  have : c.grant ≠ some x := by rw [h]; intro he; exact hx (Option.some.inj he).symm
  simp [resN, conN, resC, conC, this]

theorem optf_zero {x : String} (h : ∀ c, o = some c → c.grant = some gid) (hx : x ≠ gid) :
    optf (resN x) o = 0 ∧ optf (conN x) o = 0 ∧ optf (resC x) o = 0 ∧ optf (conC x) o = 0 := by
  cases o with
  | none => simp [optf]
  | some c => simpa [optf] using zero_of_ne (h c rfl) hx

/-- A step that changes only call `k`, which holds grant `gid` before (if present) and after, and
only that grant, whose counters move as `hacct` says whatever the other calls hold. -/
theorem shift (hi : Inv s) (hk : ∀ a, a ≠ k → s'.calls[a]? = s.calls[a]?)
    (hk' : s'.calls[k]? = some c') (hold : ∀ c, s.calls[k]? = some c → c.grant = some gid)
    (hgr : c'.grant = some gid) (hok : Ok c') (hg : s.grants[gid]? = some g)
    (hg' : s'.grants[gid]? = some g') (hother : ∀ x, x ≠ gid → s'.grants[x]? = s.grants[x]?)
    (hacct : ∀ R C RC CC, Acct g (R + optf (resN gid) s.calls[k]?) (C + optf (conN gid) s.calls[k]?)
      (RC + optf (resC gid) s.calls[k]?) (CC + optf (conC gid) s.calls[k]?) →
      Acct g' (R + resN gid c') (C + conN gid c') (RC + resC gid c') (CC + conC gid c')) :
    Inv s' := by
  refine ⟨fun x gx hx => ?_, fun a ca gx ha hga => ?_, fun a ca ha => ?_⟩
  · obtain ⟨o₁, e₁, f₁⟩ := tot_update (f := resN x) hk
    obtain ⟨o₂, e₂, f₂⟩ := tot_update (f := conN x) hk
    obtain ⟨o₃, e₃, f₃⟩ := tot_update (f := resC x) hk
    obtain ⟨o₄, e₄, f₄⟩ := tot_update (f := conC x) hk
    rw [hk'] at f₁ f₂ f₃ f₄
    by_cases hxg : x = gid
    · subst hxg
      rw [hg'] at hx
      cases hx
      have h := hi.grants x g hg
      rw [e₁, e₂, e₃, e₄] at h
      rw [f₁, f₂, f₃, f₄]
      exact hacct _ _ _ _ h
    · rw [hother x hxg] at hx
      have h := hi.grants x gx hx
      obtain ⟨z₁, z₂, z₃, z₄⟩ := optf_zero hold hxg
      obtain ⟨y₁, y₂, y₃, y₄⟩ := zero_of_ne hgr hxg
      rw [e₁, e₂, e₃, e₄, z₁, z₂, z₃, z₄] at h
      rw [f₁, f₂, f₃, f₄]
      simpa [optf, y₁, y₂, y₃, y₄] using h
  · have hgs : ∀ (x : String) (gx : GrantRec), s.grants[x]? = some gx →
        ∃ g, s'.grants[x]? = some g := by
      intro x gx hx
      by_cases hxg : x = gid
      · subst hxg; exact ⟨g', hg'⟩
      · rw [hother x hxg]; exact ⟨gx, hx⟩
    by_cases hak : a = k
    · subst hak
      rw [hk'] at ha
      cases ha
      rw [hgr] at hga
      cases hga
      exact ⟨g', hg'⟩
    · rw [hk a hak] at ha
      obtain ⟨g₀, h₀⟩ := hi.known a ca gx ha hga
      exact hgs gx g₀ h₀
  · by_cases hak : a = k
    · subst hak; rw [hk'] at ha; cases ha; exact hok
    · rw [hk a hak] at ha; exact hi.recs a ca ha

theorem Idle.insert (hk : s.calls[k]? = some c) (hv : SameView c c') (hok : Ok c → Ok c')
    (hc : s'.calls = s.calls.insert k c') (hg : s'.grants = s.grants) : Idle s s' := by
  refine ⟨fun a => ?_, fun gid => by rw [hg]; exact Idle.refl.grants gid⟩
  rw [hc]
  by_cases hak : a = k
  · subst hak; rw [Std.ExtTreeMap.getElem?_insert_self, hk]; exact ⟨hv, hok⟩
  · rw [insert_ne hak]; exact Idle.refl.calls a

theorem Idle.modify {f : CallRec → CallRec} (hk : s.calls[k]? = some c) (hv : SameView c (f c))
    (hok : Ok c → Ok (f c)) (hc : s'.calls = s.calls.modify k f) (hg : s'.grants = s.grants) :
    Idle s s' := by
  refine ⟨fun a => ?_, fun gid => by rw [hg]; exact Idle.refl.grants gid⟩
  rw [hc]
  by_cases hak : a = k
  · subst hak; rw [Std.ExtTreeMap.getElem?_modify_self, hk]; exact ⟨hv, hok⟩
  · rw [modify_ne hak]; exact Idle.refl.calls a

theorem calm_insert (hg : s.grants[gid]? = some g) (hs : s'.grants = s.grants.insert gid g')
    (hc : CalmG g g') : Calm s s' := by
  intro x
  rw [hs]
  by_cases hx : x = gid
  · subst hx; rw [Std.ExtTreeMap.getElem?_insert_self, hg]; exact hc
  · rw [insert_ne hx]; exact Idle.refl.calm x

theorem releaseGrant_of (hk : s.calls[k]? = some c) (hc : c.grant = some gid) (ha : c.attempts = 0)
    (hg : s.grants[gid]? = some g) :
    s.releaseGrant k = { s with grants := s.grants.insert gid { g with
      reserved := g.reserved - 1, costReserved := g.costReserved - g.costHeld c.cost } } := by
  unfold State.releaseGrant
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  cases c
  simp only at hc ha
  subst hc ha
  simp [Std.ExtTreeMap.get?_eq_getElem?, hg]

theorem releaseGrant_none (hk : s.calls[k]? = some c) (hc : c.grant = none) :
    s.releaseGrant k = s := by
  unfold State.releaseGrant
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  cases c
  simp only at hc
  subst hc
  rfl

theorem consumeGrant_of (hk : s.calls[k]? = some c) (hc : c.grant = some gid) (ha : c.attempts = 0)
    (hg : s.grants[gid]? = some g) :
    s.consumeGrant k = { s with grants := s.grants.insert gid { g with
      reserved := g.reserved - 1, consumed := g.consumed + 1
      costReserved := g.costReserved - g.costHeld c.cost
      costConsumed := g.costConsumed + g.costHeld c.cost } } := by
  unfold State.consumeGrant
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  cases c
  simp only at hc ha
  subst hc ha
  simp [Std.ExtTreeMap.get?_eq_getElem?, hg]

theorem consumeGrant_none (hk : s.calls[k]? = some c) (hc : c.grant = none) :
    s.consumeGrant k = s := by
  unfold State.consumeGrant
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  cases c
  simp only at hc
  subst hc
  rfl

/-- A status a call ends in without a dispatch. -/
def Settled (st : CallStatus) : Prop :=
  st ≠ .awaiting ∧ st ≠ .authorized ∧ st ≠ .dispatched ∧ st ≠ .unknown

theorem settled_cancelled : Settled .cancelled := ⟨nofun, nofun, nofun, nofun⟩

theorem ok_settled {st : CallStatus} (h : Settled st) : Ok { c with status := st } :=
  ⟨fun ho => (ho.elim h.1 h.2.1).elim, fun hd => (hd.elim h.2.2.1 h.2.2.2).elim,
   fun ha => (h.1 ha).elim⟩

theorem endCall_ne {st : CallStatus} {a : String} (h : a ≠ k) :
    (s.endCall k st).calls[a]? = s.calls[a]? := by
  unfold State.endCall
  dsimp only
  rw [modify_ne h, releaseGrant_calls]

theorem endCall_good {st : CallStatus} (hk : s.calls[k]? = some c)
    (ho : c.status = .awaiting ∨ c.status = .authorized) (hs : Settled st) :
    Good s (s.endCall k st) := by
  intro hi
  obtain ⟨hz, -, haw⟩ := hi.recs k c hk
  have ha := hz ho
  cases hgc : c.grant with
  | none =>
    unfold State.endCall
    rw [releaseGrant_none hk hgc]
    refine Idle.good ?_ hi
    exact Idle.modify (f := fun x => { x with status := st }) hk ⟨rfl, fun h => absurd hgc h⟩
      (fun _ => ok_settled hs) rfl rfl
  | some gid =>
    have hau : c.status = .authorized :=
      ho.resolve_left fun h => by rw [haw h] at hgc; cases hgc
    obtain ⟨g, hg⟩ := hi.known k c gid hk hgc
    unfold State.endCall
    rw [releaseGrant_of hk hgc ha hg]
    refine ⟨shift (c' := { c with status := st }) hi (fun a ha => modify_ne ha)
      (by rw [Std.ExtTreeMap.getElem?_modify_self, hk]; rfl)
      (fun c' h => by rw [hk] at h; cases h; exact hgc) hgc (ok_settled hs) hg
      Std.ExtTreeMap.getElem?_insert_self (fun x hx => insert_ne hx) ?_,
      calm_insert hg rfl ⟨rfl, rfl, rfl, rfl⟩⟩
    intro R C RC CC ⟨h₁, h₂, h₃, h₄⟩
    simp only [optf, hk, Option.map_some, resN, hgc, hau, ha, and_self, ↓reduceIte,
      Option.getD_some, conN, Nat.le_zero_eq, Nat.succ_ne_self, and_false, Nat.add_zero, resC, conC,
      hs.2.1, and_true] at h₁ h₂ h₃ h₄ ⊢
    refine ⟨by dsimp only; omega, h₂, by dsimp only; omega, fun mc hmc => ?_⟩
    dsimp only at hmc ⊢
    obtain ⟨b₁, b₂, b₃⟩ := h₄ mc hmc
    simp only [GrantRec.costHeld, hmc, Option.isSome_some, ite_true, amt] at b₁ ⊢
    exact ⟨by omega, b₂, by omega⟩

theorem fold_good {f : State → String × CallRec → State}
    (hf : ∀ (acc : State) (x : String × CallRec), acc.calls[x.1]? = some x.2 →
      Good acc (f acc x) ∧ ∀ a, a ≠ x.1 → (f acc x).calls[a]? = acc.calls[a]?) :
    ∀ (L : List (String × CallRec)), L.Pairwise (fun a b => a.1 ≠ b.1) → ∀ acc : State,
      (∀ x ∈ L, acc.calls[x.1]? = some x.2) → Good acc (L.foldl f acc)
  | [], _, _, _ => Good.refl
  | x :: L, hL, acc, h => by
    obtain ⟨hg, hne⟩ := hf acc x (h x List.mem_cons_self)
    refine hg.trans (fold_good hf L (List.pairwise_cons.mp hL).2 _ fun y hy => ?_)
    rw [hne y.1 fun he => (List.pairwise_cons.mp hL).1 y hy he.symm]
    exact h y (List.mem_cons_of_mem _ hy)

theorem cancelPending_good : Good s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine fold_good ?_ _ distinct_toList s toList_get
  intro acc ⟨k, c⟩ hk
  dsimp only at hk ⊢
  split <;> rename_i hs
  · exact ⟨endCall_good hk (.inl hs) settled_cancelled, fun a ha => endCall_ne ha⟩
  · exact ⟨endCall_good hk (.inr hs) settled_cancelled, fun a ha => endCall_ne ha⟩
  · exact ⟨Good.refl, fun _ _ => rfl⟩

theorem Idle.maps {fc : String → CallRec → CallRec} {fg : String → GrantRec → GrantRec}
    (hc : ∀ k c, CallMove (some c) (some (fc k c))) (hg : ∀ x g, SameG g (fg x g))
    (hs₁ : s'.calls = s.calls.map fc) (hs₂ : s'.grants = s.grants.map fg) : Idle s s' := by
  refine ⟨fun k => ?_, fun x => ?_⟩
  · rw [hs₁, Std.ExtTreeMap.getElem?_map]
    cases s.calls[k]? with
    | none => trivial
    | some c => exact hc k c
  · rw [hs₂, Std.ExtTreeMap.getElem?_map]
    cases s.grants[x]? with
    | none => trivial
    | some g => exact hg x g

theorem SameG.revoke : SameG g { g with revoked := true } := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CallMove.same (hv : SameView c c') (hok : Ok c → Ok c') : CallMove (some c) (some c') :=
  ⟨hv, hok⟩

theorem view_refl : SameView c c := ⟨rfl, fun _ => ⟨Iff.rfl, Iff.rfl, rfl⟩⟩

theorem interrupt_good : Good s s.interrupt := by
  unfold State.interrupt
  refine cancelPending_good.trans (Idle.good (Idle.maps (fun _ c => ?_) (fun _ _ => .revoke)
    rfl rfl))
  split
  · rename_i hd
    refine CallMove.same ⟨rfl, fun _ => ⟨by simp [hd], Iff.rfl, rfl⟩⟩ fun ho => ?_
    exact ⟨fun h => (by rcases h with h | h <;> simp at h), fun _ => ho.2.1 (.inl hd), nofun⟩
  · exact CallMove.same view_refl id

theorem updateEntries_grants {m : String} {t : Nat} {f : List MeterEntry → List MeterEntry} :
    (s.updateEntries p m t f).grants = s.grants := by
  unfold State.updateEntries; split <;> rfl

theorem foldl_grants {α : Type _} {f : State → α → State}
    (hf : ∀ s a, (f s a).grants = s.grants) (l : List α) (s : State) :
    (l.foldl f s).grants = s.grants :=
  foldl_invariant (fun b => b.grants = s.grants) (fun b a hb => (hf b a).trans hb) l s rfl

theorem settle_grants {ms : List String} {o : Outcome} {a : Option Nat} {ne : Bool} {t : Nat} :
    (s.settle p ms k o a ne t).1.grants = s.grants := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.grants = s.grants) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact updateEntries_grants.trans h
  · split <;> exact updateEntries_grants.trans h

theorem recordSuccess_grants {t : String} : (s.recordSuccess t).grants = s.grants := rfl

theorem recordFailure_grants {t : String} : (s.recordFailure p t).grants = s.grants := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem claim_grants {t : Nat} {rc : CallRec} {r : Requirements} {retry : Bool} {key : String} :
    (claim p s t k rc r retry key).grants =
      if retry then s.grants else (s.consumeGrant k).grants := by
  unfold claim
  dsimp only
  split
  · exact foldl_grants (fun _ _ => updateEntries_grants) _ _
  · exact foldl_grants (fun _ _ => updateEntries_grants) _ _

def claimedRec (rc : CallRec) (key : String) : CallRec :=
  { rc with status := .dispatched, attempts := rc.attempts + 1, idempotencyKey := some key }

theorem claim_calls {t : Nat} {rc : CallRec} {r : Requirements} {retry : Bool} {key : String} :
    (claim p s t k rc r retry key).calls = s.calls.insert k (claimedRec rc key) := by
  unfold claim
  dsimp only
  split
  · rw [foldl_calls (fun _ _ => retime_calls)]; rfl
  · rw [foldl_calls (fun _ _ => reserve_calls), consumeGrant_calls]; rfl

theorem claim_inv {t : Nat} {rc : CallRec} {r : Requirements} {key : String} (hi : Inv s)
    (hk : s.calls[k]? = some rc) (hst : rc.status = .authorized ∨ rc.status = .unknown) :
    Inv (claim p s t k rc r (rc.status == .unknown) key) := by
  obtain ⟨hz, h₁, -⟩ := hi.recs k rc hk
  have hok : Ok (claimedRec rc key) :=
    ⟨fun ho => (by rcases ho with h | h <;> simp [claimedRec] at h), fun _ => Nat.le_add_left _ _,
      fun h => (by simp [claimedRec] at h)⟩
  rcases hst with hst | hst
  · have ha := hz (.inr hst)
    have hr : (rc.status == .unknown) = false := by rw [hst]; rfl
    cases hgc : rc.grant with
    | none =>
      refine (Idle.insert hk ⟨by rfl, fun h => absurd hgc h⟩ (fun _ => hok) claim_calls ?_).inv hi
      rw [claim_grants, hr, consumeGrant_none hk hgc]
      rfl
    | some gid =>
      obtain ⟨g, hg⟩ := hi.known k rc gid hk hgc
      have hgs : (claim p s t k rc r (rc.status == .unknown) key).grants =
          (s.consumeGrant k).grants := by
        rw [claim_grants, hr]; rfl
      rw [consumeGrant_of hk hgc ha hg] at hgs
      refine shift (c' := claimedRec rc key) hi (fun a ha => by rw [claim_calls, insert_ne ha])
        (by rw [claim_calls, Std.ExtTreeMap.getElem?_insert_self])
        (fun c' h => by rw [hk] at h; cases h; exact hgc) hgc hok hg
        (by rw [hgs]; exact Std.ExtTreeMap.getElem?_insert_self)
        (fun x hx => by rw [hgs]; exact insert_ne hx) ?_
      intro R C RC CC ⟨h₁, h₂, h₃, h₄⟩
      simp only [optf, hk, Option.map_some, resN, hgc, hst, ha, and_self, ↓reduceIte,
        Option.getD_some, conN, Nat.le_zero_eq, Nat.succ_ne_self, and_false, Nat.add_zero, resC,
        conC, reduceCtorEq, Nat.zero_add, Std.le_refl, claimedRec] at h₁ h₂ h₃ h₄ ⊢
      refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, fun mc hmc => ?_⟩
      dsimp only at hmc ⊢
      obtain ⟨b₁, b₂, b₃⟩ := h₄ mc hmc
      simp only [GrantRec.costHeld, hmc, Option.isSome_some, ite_true, amt] at b₁ b₂ ⊢
      exact ⟨by omega, by omega, by omega⟩
  · have ha := h₁ (.inr hst)
    have hr : (rc.status == .unknown) = true := by rw [hst]; rfl
    refine (Idle.insert hk ⟨by rfl, fun _ => ⟨by simp [claimedRec, hst], ⟨fun _ => ha, fun _ =>
      Nat.le_add_left _ _⟩, by rfl⟩⟩ (fun _ => hok) claim_calls ?_).inv hi
    rw [claim_grants, hr]
    rfl

theorem Idle.fresh (hk : s.calls[k]? = none) (hg0 : c'.grant = none) (hok : Ok c')
    (hc : s'.calls = s.calls.insert k c') (hg : s'.grants = s.grants) : Idle s s' := by
  refine ⟨fun a => ?_, fun x => by rw [hg]; exact Idle.refl.grants x⟩
  rw [hc]
  by_cases hak : a = k
  · subst hak; rw [Std.ExtTreeMap.getElem?_insert_self, hk]; exact ⟨hg0, hok⟩
  · rw [insert_ne hak]; exact Idle.refl.calls a

theorem calm_modify {F : GrantRec → GrantRec} (hg : s.grants[gid]? = some g)
    (hs : s'.grants = s.grants.modify gid F) (hc : CalmG g (F g)) : Calm s s' := by
  intro x
  rw [hs]
  by_cases hx : x = gid
  · subst hx; rw [Std.ExtTreeMap.getElem?_modify_self, hg]; exact hc
  · rw [modify_ne hx]; exact Idle.refl.calm x

theorem shadowed_grant {mode : Mode} {x : Disposition}
    (h : (x.shadowed mode).1.grant = some gid) : x = .allowedByGrant gid := by
  have hx : (x.shadowed mode).1 = x ∨ (x.shadowed mode).1 = .allowed := by
    cases mode <;> cases x <;> simp only [Disposition.shadowed] <;> try split
    all_goals simp
  rcases hx with hx | hx <;> rw [hx] at h
  · cases x <;> simp_all [Disposition.grant]
  · cases h

theorem findGrant_some {tool dg : String} {cn : Consent} {cs : Option Cost} {t : Nat}
    (h : s.findGrant p tool dg cn cs t = some gid) :
    ∃ gr, s.grants[gid]? = some gr ∧ gr.consumed + gr.reserved < gr.maxUses ∧
      gr.coversCost cs = true := by
  unfold State.findGrant at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨x.2, toList_get x (List.mem_of_find?_eq_some hx), hp.1.1.2, hp.1.2⟩

theorem enforce_grant {tool dg : String} {cs : Option Cost} {t : Nat}
    {gs es : List (String × Bool)}
    (h : (enforceDecision p s t k tool dg cs gs es).1 = .allowedByGrant gid) :
    ∃ cn, s.findGrant p tool dg cn cs t = some gid := by
  unfold enforceDecision at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hg
       split at hg
       · exact ⟨_, hg⟩
       · cases hg)

/-- A new record holds the grant its disposition names, if any, whose use and cost it reserves. -/
theorem propose_good {D : Disposition} {cs : Option Cost}
    (hk : s.calls[k]? = none)
    (hgr : ∀ gid, D.grant = some gid → ∃ gr, s.grants[gid]? = some gr ∧
      gr.consumed + gr.reserved < gr.maxUses ∧ gr.coversCost cs = true)
    (hc : s'.calls = s.calls.insert k c') (h₁ : c'.grant = D.grant) (h₂ : c'.status = D.status)
    (h₃ : c'.attempts = 0) (h₄ : c'.cost = cs)
    (hg : s'.grants = match D.grant with
      | some gid => s.grants.modify gid fun g =>
        { g with reserved := g.reserved + 1, costReserved := g.costReserved + g.costHeld cs }
      | none => s.grants) : Good s s' := by
  intro hi
  have hok : Ok c' := by
    refine ⟨fun _ => h₃, fun hd => ?_, fun ha => ?_⟩
    · rw [h₂] at hd; cases D <;> rcases hd with hd | hd <;> cases hd
    · rw [h₂] at ha; rw [h₁]; cases D <;> first | rfl | cases ha
  cases hD : D.grant with
  | none =>
    rw [hD] at hg h₁
    exact (Idle.fresh hk h₁ hok hc hg).good hi
  | some gid =>
    rw [hD] at hg h₁
    obtain ⟨gr, hgr, huse, hcov⟩ := hgr gid hD
    have hau : c'.status = .authorized := by
      rw [h₂]; cases D <;> first | rfl | cases hD
    refine ⟨shift hi (fun a ha => by rw [hc, insert_ne ha])
      (by rw [hc, Std.ExtTreeMap.getElem?_insert_self]) (fun c h => by rw [hk] at h; cases h)
      h₁ hok hgr (by rw [hg, Std.ExtTreeMap.getElem?_modify_self, hgr]; rfl)
      (fun x hx => by rw [hg, modify_ne hx]) ?_, calm_modify hgr hg ⟨rfl, rfl, rfl, rfl⟩⟩
    intro R C RC CC ⟨a₁, a₂, a₃, a₄⟩
    simp only [optf, hk, Option.map_none, Option.getD_none, Nat.add_zero, resN, h₁, hau, h₃,
      and_self, ↓reduceIte, conN, Nat.le_zero_eq, Nat.succ_ne_self, and_false, resC,
      conC] at a₁ a₂ a₃ a₄ ⊢
    refine ⟨by dsimp only; omega, a₂, by dsimp only; omega, fun mc hmc => ?_⟩
    dsimp only at hmc ⊢
    obtain ⟨b₁, b₂, b₃⟩ := a₄ mc hmc
    unfold GrantRec.coversCost at hcov
    rw [hmc] at hcov
    cases hcs : cs with
    | none => rw [hcs] at hcov; cases hcov
    | some cc =>
      rw [hcs] at hcov
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcov
      simp only [GrantRec.costHeld, hmc, Option.isSome_some, ite_true, amt, h₄, hcs,
        Option.map_some, Option.getD_some] at b₁ ⊢
      exact ⟨by omega, b₂, by omega⟩

variable {t : Nat} {tool dg : String} {cs : Option Cost} {gs es' : List (String × Bool)}

theorem handlePropose_good : Good s (handlePropose p s t k tool dg cs gs es').1 := by
  unfold handlePropose
  split
  · split <;> exact Good.refl
  · rename_i hk
    split
    rename_i dd cc hd
    split
    · exact (Idle.of_eq rfl rfl).good
    · rename_i r hr
      dsimp only
      refine propose_good (D := (dd.shadowed (p.modeOf tool)).1)
        (by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hk) (fun gid hg => ?_) rfl rfl rfl rfl rfl
        rfl
      have hdd := shadowed_grant hg
      rw [hdd] at hd
      obtain ⟨cn, hf⟩ := enforce_grant (by rw [hd])
      exact findGrant_some hf

theorem tot_zero (h : ∀ (a : String) (c : CallRec), m[a]? = some c → f c = 0) : tot m f = 0 := by
  rw [tot_congr (m := ∅) fun a => ?_]
  · unfold tot; rw [Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl]; rfl
  · cases ha : m[a]? with
    | none => simp [optf]
    | some c => simp [optf, h a c ha]

theorem grantCreate_good {g0 : GrantRec} (hc : s.grants[gid]? = none) (hs : s'.calls = s.calls)
    (hg : s'.grants = s.grants.insert gid g0) (h₁ : g0.reserved = 0) (h₂ : g0.consumed = 0)
    (h₃ : g0.costReserved = 0) (h₄ : g0.costConsumed = 0) : Good s s' := by
  intro hi
  have hz : ∀ (a : String) (c : CallRec), s.calls[a]? = some c → c.grant ≠ some gid :=
    fun a c ha hgc => by obtain ⟨_, hx⟩ := hi.known a c gid ha hgc; rw [hc] at hx; cases hx
  refine ⟨Inv.congr (s₁ := { s with grants := s.grants.insert gid g0 }) ?_ hs hg, fun x => ?_⟩
  · refine ⟨fun x gx hx => ?_, fun a ca gx ha hga => ?_, hi.recs⟩
    · by_cases hxg : x = gid
      · subst hxg
        rw [Std.ExtTreeMap.getElem?_insert_self] at hx
        cases hx
        have z : ∀ F : String → CallRec → Nat, (∀ c, c.grant ≠ some x → F x c = 0) →
            tot s.calls (F x) = 0 :=
          fun F hF => tot_zero fun a c ha => hF c (hz a c ha)
        rw [z resN (fun c h => by simp [resN, h]), z conN (fun c h => by simp [conN, h]),
          z resC (fun c h => by simp [resC, h]), z conC (fun c h => by simp [conC, h])]
        exact ⟨h₁, h₂, by omega, fun _ _ => ⟨h₃, h₄, by omega⟩⟩
      · rw [insert_ne hxg] at hx
        exact hi.grants x gx hx
    · obtain ⟨g₀, h₀⟩ := hi.known a ca gx ha hga
      by_cases hxg : gx = gid
      · subst hxg; exact ⟨g0, Std.ExtTreeMap.getElem?_insert_self⟩
      · exact ⟨g₀, by rw [insert_ne hxg]; exact h₀⟩
  · rw [hg]
    by_cases hxg : x = gid
    · subst hxg; rw [Std.ExtTreeMap.getElem?_insert_self, hc]; exact ⟨h₂, h₄⟩
    · rw [insert_ne hxg]; exact Idle.refl.calm x

theorem grantDenial_fresh {t : Nat} {a tool : String} {dg : Option String} {sc : GrantScope}
    {n : Nat} {mc : Option Cost} {ex : Option Nat}
    (h : grantDenial p s t gid a tool dg sc n mc ex = none) : s.grants[gid]? = none := by
  unfold grantDenial at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · rename_i hc
      exact Std.ExtTreeMap.getElem?_eq_none (by simpa using hc)

theorem handleGrantCreate_good {t : Nat} {a tool rv : String} {dg : Option String}
    {sc : GrantScope} {n : Nat} {mc : Option Cost} {nb ex : Option Nat} :
    Good s (handleGrantCreate p s t gid a tool dg sc n mc nb ex rv).1 := by
  unfold handleGrantCreate
  split
  · exact Good.refl
  · rename_i hd
    exact grantCreate_good (grantDenial_fresh hd) rfl rfl rfl rfl rfl rfl

theorem Idle.grants_map {F : String → GrantRec → GrantRec} (hc : s'.calls = s.calls)
    (hF : ∀ x g, SameG g (F x g)) (hg : s'.grants = s.grants.map F) : Idle s s' := by
  refine ⟨fun a => by rw [hc]; exact Idle.refl.calls a, fun x => ?_⟩
  rw [hg, Std.ExtTreeMap.getElem?_map]
  cases s.grants[x]? with
  | none => trivial
  | some g => exact hF x g

theorem SameG.refl : SameG g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem handleTurnEnd_good : Good s (handleTurnEnd s).1 := by
  unfold handleTurnEnd
  split
  · exact Good.refl
  · refine Idle.good ?_
    refine Idle.grants_map rfl (fun _ _ => ?_) rfl
    split
    · exact .revoke
    · exact .refl

theorem handleGrantRevoke_good : Good s (handleGrantRevoke s gid).1 := by
  unfold handleGrantRevoke
  split
  · exact Good.refl
  · rename_i g hg
    rw [Std.ExtTreeMap.get?_eq_getElem?] at hg
    refine Idle.good ⟨fun a => Idle.refl.calls a, fun x => ?_⟩
    by_cases hx : x = gid
    · subst hx; rw [Std.ExtTreeMap.getElem?_insert_self, hg]; exact .revoke
    · rw [insert_ne hx]; exact Idle.refl.grants x

local macro "good" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Good.refl
      | exact (Idle.of_eq rfl rfl).good
      | exact cancelPending_good
      | exact cancelPending_good.congr rfl rfl
      | exact interrupt_good.congr rfl rfl)

theorem handleSessionStart_good {i pd r : String} {ps : List String}
    {as : List (String × ApproverInfo)} {l : Ledger} :
    Good s (handleSessionStart s i pd r ps as l).1 := by
  unfold handleSessionStart; good

theorem handleSessionEnd_good : Good s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; good

theorem handleTurnStart_good {u : Bool} : Good s (handleTurnStart s u).1 := by
  unfold handleTurnStart; good

theorem handleStepStart_good : Good s (handleStepStart p s).1 := by
  unfold handleStepStart; good

theorem handleApproverAttest_good {a : String} {i : ApproverInfo} :
    Good s (handleApproverAttest s a i).1 := by
  unfold handleApproverAttest; good

theorem handlePermissionRevoke_good {a : String} : Good s (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; good

theorem handleReset_good : Good s (handleReset s).1 := by
  unfold handleReset; good

theorem handleKill_good : Good s (handleKill p s).1 := by
  unfold handleKill; good

theorem handlePermissionAdd_good {a b : String} : Good s (handlePermissionAdd p s a b).1 := by
  unfold handlePermissionAdd; good

theorem handleEscalationAck_good {a : String} {n : Nat} :
    Good s (handleEscalationAck p s a n).1 := by
  unfold handleEscalationAck; good

theorem handleLedgerSync_good {l : Ledger} : Good s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; good

theorem callCheck_awaiting {rid : RequestId} {rc : CallRec} (h : callCheck s k rid = .ok rc) :
    s.calls[k]? = some rc ∧ rc.status = .awaiting := by
  unfold callCheck at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hk hs _
       exact ⟨by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hk, Classical.not_not.mp hs⟩)

theorem awaitingCheck_awaiting {rid : RequestId} {w : String} {rc : CallRec}
    (h : awaitingCheck p s k rid w = .ok rc) : s.calls[k]? = some rc ∧ rc.status = .awaiting := by
  unfold awaitingCheck at h
  cases hc : callCheck s k rid with
  | error => simp [hc, bind, Except.bind] at h
  | ok rc' =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    · cases h; exact callCheck_awaiting hc

theorem applyApprove_good {rc : CallRec} {t : Nat} {w pr dg : String} {cs : Option Cost}
    {ed : Option Edit} {r : State × Verdict} (hk : s.calls[k]? = some rc)
    (hst : rc.status = .awaiting) (ha : applyApprove p s t k rc w pr dg cs ed = .ok r) :
    Good s r.1 := by
  intro hi
  have hg : rc.grant = none := (hi.recs k rc hk).2.2 hst
  have hz : rc.attempts = 0 := (hi.recs k rc hk).1 (.inl hst)
  have hok : ∀ c' : CallRec, c'.grant = rc.grant → c'.attempts = rc.attempts →
      (c'.status = .awaiting ∨ c'.status = .authorized) → CallMove (some rc) (some c') :=
    fun c' h₁ h₂ h₃ => ⟨⟨h₁, fun h => absurd hg h⟩, fun _ => ⟨fun _ => h₂.trans hz,
      fun h => (by rcases h with h | h <;> rcases h₃ with h' | h' <;> rw [h] at h' <;> cases h'),
      fun _ => h₁.trans hg⟩⟩
  unfold applyApprove at ha
  repeat' (first | (dsimp only at ha) | split at ha)
  all_goals first
    | cases ha; done
    | (cases ha
       rename_i rc' hn _
       have hf : rc'.grant = rc.grant ∧ rc'.attempts = rc.attempts ∧ rc'.status = rc.status := by
         revert hn
         repeat' split
         all_goals (intro hn; cases hn <;> exact ⟨rfl, rfl, rfl⟩)
       refine Idle.good ?_ hi
       first
         | exact Idle.insert hk (hok _ hf.1 hf.2.1 (.inl (hf.2.2.trans hst))).1
             (hok _ hf.1 hf.2.1 (.inl (hf.2.2.trans hst))).2 rfl rfl
         | (have h := hok { rc' with status := .authorized, authorizedAt := some t } hf.1 hf.2.1
              (.inr rfl)
            exact Idle.insert hk h.1 h.2 rfl rfl))

theorem handleApprove_good {t : Nat} {rid : RequestId} {w dg : String} {cs : Option Cost}
    {ed : Option Edit} : Good s (handleApprove p s t k rid w dg cs ed).1 := by
  unfold handleApprove
  split
  · exact Good.refl
  · rename_i rc hc
    obtain ⟨hk, hst⟩ := awaitingCheck_awaiting hc
    dsimp only
    split
    · exact Good.refl
    · exact applyApprove_good hk hst (by assumption)

theorem vetoCheck_open {rid : RequestId} {w : String} {rc : CallRec}
    (h : vetoCheck p s k rid w = .ok rc) :
    s.calls[k]? = some rc ∧ (rc.status = .awaiting ∨ rc.status = .authorized) := by
  unfold vetoCheck at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hk hs _ _
       refine ⟨by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hk, ?_⟩
       simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at hs
       rcases hs with h | h
       · exact .inl h
       · exact .inr h.1)

theorem handleReject_good {rid : RequestId} {w : String} :
    Good s (handleReject p s k rid w).1 := by
  unfold handleReject
  split
  · exact Good.refl
  · rename_i rc hv
    obtain ⟨hk, ho⟩ := vetoCheck_open hv
    exact (endCall_good (st := .rejected) hk ho ⟨nofun, nofun, nofun, nofun⟩).congr rfl rfl

theorem handleApprovalExpire_good {rid : RequestId} : Good s (handleApprovalExpire s k rid).1 := by
  unfold handleApprovalExpire
  split
  · exact Good.refl
  · rename_i rc hc
    obtain ⟨hk, hst⟩ := callCheck_awaiting hc
    exact endCall_good (st := .expired) hk (.inl hst) ⟨nofun, nofun, nofun, nofun⟩

theorem handleCancel_good : Good s (handleCancel s k).1 := by
  unfold handleCancel
  split
  · exact Good.refl
  · rename_i rc hrc
    rw [Std.ExtTreeMap.get?_eq_getElem?] at hrc
    split <;> rename_i hs
    · exact endCall_good hrc (.inl hs) settled_cancelled
    · exact endCall_good hrc (.inr hs) settled_cancelled
    · exact Good.refl

theorem withStatus_idle {rc : CallRec} {st : CallStatus} (hk : s.calls[k]? = some rc)
    (hd : rc.status = .dispatched ∨ rc.status = .unknown) (ha : st ≠ .awaiting)
    (hb : st ≠ .authorized) : Idle s (withStatus s k rc st) := by
  refine Idle.insert (c' := { rc with status := st }) hk ⟨rfl, fun _ => ⟨?_, Iff.rfl, rfl⟩⟩
    (fun ho => ?_) rfl rfl
  · simp only [hb, false_and, false_iff, not_and]
    intro h; rcases hd with hd | hd <;> rw [hd] at h <;> cases h
  · exact ⟨fun h => (h.elim ha hb).elim, fun _ => ho.2.1 hd, fun h => (ha h).elim⟩

theorem outcome_status (o : Outcome) : o.status ≠ .awaiting ∧ o.status ≠ .authorized := by
  cases o <;> exact ⟨nofun, nofun⟩

theorem handleResult_good {t : Nat} {o : Outcome} {a : Option Nat} {n : Bool} :
    Good s (handleResult p s t k o a n).1 := by
  unfold handleResult
  split
  · exact Good.refl
  · rename_i rc hrc
    rw [Std.ExtTreeMap.get?_eq_getElem?] at hrc
    split
    · exact Good.refl
    · rename_i hd
      have hf := withStatus_idle (st := o.status) hrc (.inl (Classical.not_not.mp hd))
        (outcome_status o).1 (outcome_status o).2
      repeat' (first | (dsimp only) | split)
      all_goals
        exact hf.good.congr (by simp only [recordFailure_calls, recordSuccess_calls, settle_calls])
          (by simp only [recordFailure_grants, recordSuccess_grants, settle_grants])

theorem handleOutcomeUnknown_good : Good s (handleOutcomeUnknown p s k).1 := by
  unfold handleOutcomeUnknown
  split
  · exact Good.refl
  · rename_i rc hrc
    rw [Std.ExtTreeMap.get?_eq_getElem?] at hrc
    split
    · exact Good.refl
    · rename_i hd
      exact (withStatus_idle (st := .unknown) hrc (.inl (Classical.not_not.mp hd)) nofun
        nofun).good.congr
        recordFailure_calls recordFailure_grants

theorem handleReconcile_good {t : Nat} {o : Outcome} {a : Option Nat} {n : Bool} :
    Good s (handleReconcile p s t k o a n).1 := by
  unfold handleReconcile
  split
  · exact Good.refl
  · rename_i rc hrc
    rw [Std.ExtTreeMap.get?_eq_getElem?] at hrc
    have hf : Idle s { s with calls := s.calls.insert k { rc with reconciled := some o } } :=
      Idle.insert (c' := { rc with reconciled := some o }) hrc
        ⟨rfl, fun _ => ⟨Iff.rfl, Iff.rfl, rfl⟩⟩ id rfl rfl
    repeat' (first | (dsimp only) | split)
    all_goals first
      | exact Good.refl
      | exact hf.good.congr (by simp only [recordFailure_calls, settle_calls])
            (by simp only [recordFailure_grants, settle_grants])

theorem settled_of_denial {st : CallStatus}
    (h : st = .expired ∨ ∃ x, st = .deniedAtDispatch x) : Settled st := by
  rcases h with rfl | ⟨_, rfl⟩ <;> exact ⟨nofun, nofun, nofun, nofun⟩

/-- Like `Good`, except that a claim may consume. -/
def Stepped (s : State) (r : State × Verdict) : Prop :=
  Inv s → Inv r.1 ∧ (r.2.claimed = false → Calm s r.1)

theorem Good.stepped {r : State × Verdict} (h : Good s r.1) : Stepped s r :=
  fun hi => ⟨(h hi).1, fun _ => (h hi).2⟩

theorem stepped_refl {v : Verdict} : Stepped s (s, v) := fun hi => ⟨hi, fun _ => Idle.refl.calm⟩

theorem handleDispatch_stepped {t n : Nat} {dg key : String} {cs : Option Cost}
    {g : List (String × Bool)} : Stepped s (handleDispatch p s t k n dg cs g key) := by
  intro hi
  cases hcl : (handleDispatch p s t k n dg cs g key).2.claimed
  · rcases Dispatch.handle_unclaimed hcl with he | ⟨c, st, hk, ha, hst, he⟩ <;> rw [he]
    · exact ⟨hi, fun _ => Idle.refl.calm⟩
    · exact (endCall_good hk (.inr ha) (settled_of_denial hst) hi).imp_right fun h _ => h
  · obtain ⟨c, hk, hs, -⟩ := Dispatch.handle_claimed.mp hcl
    rw [Dispatch.handle_post hcl hk]
    exact ⟨claim_inv hi hk (Dispatch.stage_active hs), nofun⟩

theorem stepHandle_stepped : Stepped s (stepHandle p s e) := by
  unfold Writ.stepHandle
  split <;> first
    | with_reducible exact Good.stepped handleSessionStart_good
    | with_reducible exact Good.stepped handleSessionEnd_good
    | with_reducible exact Good.stepped handleTurnStart_good
    | with_reducible exact Good.stepped handleTurnEnd_good
    | with_reducible exact Good.stepped handleStepStart_good
    | with_reducible exact Good.stepped handleApproverAttest_good
    | with_reducible exact Good.stepped handlePermissionRevoke_good
    | with_reducible exact Good.stepped handlePropose_good
    | with_reducible exact Good.stepped handleApprove_good
    | with_reducible exact Good.stepped handleReject_good
    | with_reducible exact Good.stepped handleApprovalExpire_good
    | with_reducible exact Good.stepped handleGrantCreate_good
    | with_reducible exact Good.stepped handleGrantRevoke_good
    | with_reducible exact handleDispatch_stepped
    | with_reducible exact Good.stepped handleResult_good
    | with_reducible exact Good.stepped handleOutcomeUnknown_good
    | with_reducible exact Good.stepped handleReconcile_good
    | with_reducible exact Good.stepped handleCancel_good
    | with_reducible exact Good.stepped handleReset_good
    | with_reducible exact Good.stepped handleKill_good
    | with_reducible exact Good.stepped handlePermissionAdd_good
    | with_reducible exact Good.stepped handleEscalationAck_good
    | with_reducible exact Good.stepped handleLedgerSync_good

theorem step_stepped : Stepped s (step p s e) := by
  have hh := stepHandle_stepped (p := p) (s := s) (e := e)
  unfold Writ.step
  split
  · exact stepped_refl
  · split
    · rename_i hs
      rw [hs] at hh
      exact fun hi => ⟨(hh hi).1.congr rfl rfl, fun hc => ((hh hi).2 hc).congr rfl⟩
    · exact stepped_refl

theorem inv_reachable (hr : Reachable p d s) : Inv s := by
  induction hr with
  | init => exact ⟨fun _ _ h => by simp [State.initial] at h, fun _ _ _ h => by
      simp [State.initial] at h, fun _ _ h => by simp [State.initial] at h⟩
  | step _ ih => exact (step_stepped ih).1

def claimEntry (gid : String) (x : State × Event × Verdict) : Option (Option Cost) :=
  match x.2.1.body with
  | .dispatch k _ _ cost _ _ =>
    match x.1.calls[k]? with
    | some c =>
      if x.2.2.claimed = true ∧ c.status = .authorized ∧ c.grant = some gid then some cost
      else none
    | none => none
  | _ => none

def costSum (l : List (Option Cost)) : Nat := (l.map fun c => (c.map (·.amount)).getD 0).sum

theorem grantClaims_snoc : grantClaims p d (es ++ [e]) gid = grantClaims p d es gid ++
    (claimEntry gid (after p d es, e, (step p (after p d es) e).2)).toList := by
  unfold grantClaims
  rw [trace_snoc, List.filterMap_append]
  congr 1

theorem claimEntry_unclaimed {x : State × Event × Verdict} (h : x.2.2.claimed = false) :
    claimEntry gid x = none := by
  unfold claimEntry
  split
  · split
    · rw [h]; simp
    · rfl
  · rfl

/-- What `grantClaims` counts so far is the grant's consumed counters. -/
def Tracks (s : State) (l : List (Option Cost)) (gid : String) : Prop :=
  (∀ g, s.grants[gid]? = some g →
    l.length = g.consumed ∧ (g.maxCost.isSome = true → costSum l = g.costConsumed)) ∧
  (s.grants[gid]? = none → l = [])

theorem Tracks.calm {l : List (Option Cost)} (h : Tracks s l gid) (hc : Calm s s') :
    Tracks s' l gid := by
  have hm := hc gid
  refine ⟨fun g' hg' => ?_, fun hn => ?_⟩
  · rw [hg'] at hm
    cases hg : s.grants[gid]? with
    | none =>
      rw [hg] at hm
      rw [h.2 hg]
      exact ⟨hm.1.symm, fun _ => hm.2.symm⟩
    | some g =>
      rw [hg] at hm
      obtain ⟨h₁, h₂, -, h₄⟩ := hm
      obtain ⟨a₁, a₂⟩ := h.1 g hg
      exact ⟨a₁.trans h₁.symm, fun hs => (a₂ (h₄ ▸ hs)).trans h₂.symm⟩
  · rw [hn] at hm
    cases hg : s.grants[gid]? with
    | none => exact h.2 hg
    | some g => rw [hg] at hm; exact hm.elim

theorem Tracks.same {l : List (Option Cost)} (h : Tracks s l gid)
    (he : s'.grants[gid]? = s.grants[gid]?) : Tracks s' l gid := by
  unfold Tracks; rw [he]; exact h

theorem tracks (p : Policy) (d : String) (es : List Event) (gid : String) :
    Tracks (after p d es) (grantClaims p d es gid) gid := by
  refine snoc_induction (P := fun es => Tracks (after p d es) (grantClaims p d es gid) gid)
    ⟨fun g hg => by simp [after_nil, State.initial] at hg, fun _ => rfl⟩ (fun es e ih => ?_) es
  rw [after_snoc, grantClaims_snoc]
  have hr : Reachable p d (after p d es) := reachable_after
  have hi := inv_reachable hr
  generalize hs : after p d es = s at hr hi ih ⊢
  cases hcl : (step p s e).2.claimed with
  | false =>
    rw [claimEntry_unclaimed hcl, Option.toList_none, List.append_nil]
    exact ih.calm ((step_stepped hi).2 hcl)
  | true =>
    obtain ⟨k, n, dg, cs, g, key, he⟩ := claimed_dispatch hr hcl
    obtain ⟨-, c, hc, ⟨hst, -, -, -, hcs, -⟩, -⟩ := (dispatch_claimed_iff he).mp hcl
    have hgr : (step p s e).1.grants =
        if (c.status == .unknown) = true then s.grants else (s.consumeGrant k).grants := by
      rw [claim_post hcl he hc]; exact claim_grants (key := key)
    have hentry : claimEntry gid (s, e, (step p s e).2) =
        if c.status = .authorized ∧ c.grant = some gid then some cs else none := by
      unfold claimEntry; simp only [he, hc, hcl, true_and]
    by_cases hx : c.status = .authorized ∧ c.grant = some gid
    · obtain ⟨hau, hgc⟩ := hx
      rw [hentry, ite_eq_left ⟨hau, hgc⟩, Option.toList_some]
      have ha := (hi.recs k c hc).1 (.inr hau)
      obtain ⟨g₀, hg₀⟩ := hi.known k c gid hc hgc
      have hu : (c.status == .unknown) = false := by rw [hau]; rfl
      simp only [hu, Bool.false_eq_true, ite_false, consumeGrant_of hc hgc ha hg₀] at hgr
      obtain ⟨t₁, t₂⟩ := ih.1 g₀ hg₀
      refine ⟨fun g' hg' => ?_, fun hn => ?_⟩
      · rw [hgr, Std.ExtTreeMap.getElem?_insert_self] at hg'
        cases hg'
        refine ⟨by simp [t₁], fun hm => ?_⟩
        simp only [costSum, List.map_append, List.sum_append_nat, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil] at t₂ ⊢
        rw [t₂ hm]
        simp only [GrantRec.costHeld, hm, ite_true, hcs]
        omega
      · rw [hgr, Std.ExtTreeMap.getElem?_insert_self] at hn; cases hn
    · rw [hentry, ite_eq_right hx, Option.toList_none, List.append_nil]
      refine ih.same ?_
      rw [hgr]
      split
      · rfl
      · rename_i hu
        have hau : c.status = .authorized := hst.resolve_right fun h => hu (by simp [h])
        cases hgc : c.grant with
        | none => rw [consumeGrant_none hc hgc]
        | some x =>
          have hx' : x ≠ gid := fun h => hx ⟨hau, h ▸ hgc⟩
          obtain ⟨g₀, hg₀⟩ := hi.known k c x hc hgc
          rw [consumeGrant_of hc hgc ((hi.recs k c hc).1 (.inr hau)) hg₀]
          exact insert_ne (Ne.symm hx')

theorem mem_reservedCalls : k ∈ reservedCalls s gid ↔ ∃ c, s.calls[k]? = some c ∧
    c.grant = some gid ∧ c.status = .authorized ∧ c.attempts = 0 := by
  simp only [reservedCalls, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', c⟩, ⟨hm, hc⟩, rfl⟩; exact ⟨c, toList_get _ hm, hc⟩
  · rintro ⟨c, hk, hc⟩
    exact ⟨(k, c), ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, hc⟩, rfl⟩

theorem mem_consumedCalls : k ∈ consumedCalls s gid ↔ ∃ c, s.calls[k]? = some c ∧
    c.grant = some gid ∧ 1 ≤ c.attempts := by
  simp only [consumedCalls, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', c⟩, ⟨hm, hc⟩, rfl⟩; exact ⟨c, toList_get _ hm, hc⟩
  · rintro ⟨c, hk, hc⟩
    exact ⟨(k, c), ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, hc⟩, rfl⟩

end Grants

open Grants

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event} {k gid : String}
  {c : CallRec} {g : GrantRec}

/-- Section 8, theorem 2: at every reachable state each grant's reserved and consumed uses and
cost are exactly those of its calls, so a call that ends without dispatch returns its use, and
they stay within `max_uses` and `max_cost`. -/
theorem grantInv_reachable : Reachable p d s → GrantInv s :=
  fun h => (inv_reachable h).grantInv

/-- Section 8, theorem 2: at most `max_uses` claimed first attempts use a grant. -/
theorem grant_uses (hg : (after p d es).grants[gid]? = some g) :
    (grantClaims p d es gid).length ≤ g.maxUses := by
  rw [((tracks p d es gid).1 g hg).1]
  have := (grantInv_reachable (reachable_after (p := p) (d := d) (es := es))).uses gid g hg
  omega

/-- Section 8, theorem 2: the costs of the claimed first attempts that use a grant with
`max_cost` sum to at most `max_cost`. -/
theorem grant_cost {mc : Cost} (hg : (after p d es).grants[gid]? = some g)
    (hmc : g.maxCost = some mc) :
    ((grantClaims p d es gid).map fun c => (c.map (·.amount)).getD 0).sum ≤ mc.amount := by
  have h := ((tracks p d es gid).1 g hg).2 (by rw [hmc]; rfl)
  unfold costSum at h
  rw [h]
  have := (grantInv_reachable (reachable_after (p := p) (d := d) (es := es))).cost gid g mc hg hmc
  omega

/-- Section 8, theorem 2: a claimed retry of an Unknown call leaves every grant as it was. -/
theorem retry_no_use {n : Nat} {dg key : String} {cost : Option Cost} {gs : List (String × Bool)}
    (h : (step p s e).2.claimed = true) (he : e.body = .dispatch k n dg cost gs key)
    (hc : s.calls[k]? = some c) (hst : c.status = .unknown) : (step p s e).1.grants = s.grants := by
  rw [claim_post h he hc]
  show (claim p s e.time k c _ _ key).grants = s.grants
  rw [claim_grants, hst]
  rfl

/-- Section 8, theorems 1 and 2: grant `gid`, read against its record `g`, was created by an
accepted `grant_create` of the trace, at a state with no grant `gid`, that carried `g`'s approver,
tool, digest, scope, `max_uses`, `max_cost`, `not_before`, `expires_at` and reviewed scope digest;
`g`'s epoch and turn are the session's at that event and its principal is the approver's attested
principal. The create left `g` with zero counters and unrevoked, so every later step changed only
the use and cost counters and `revoked`. -/
def GrantOrigin (p : Policy) (d : String) (es : List Event) (gid : String) (g : GrantRec) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    s₀.grants[gid]? = none ∧
    e₀.body = .grantCreate gid g.approver g.tool g.digest g.scope g.maxUses g.maxCost g.notBefore
      g.expiresAt g.reviewedScopeDigest ∧
    g.epoch = s₀.epoch ∧ g.turn = s₀.turnIndex ∧
    (∃ info, s₀.approvers[g.approver]? = some info ∧ info.principal = g.principal) ∧
    (step p s₀ e₀).1.grants[gid]? =
      some { g with consumed := 0, reserved := 0, costConsumed := 0, costReserved := 0
                    revoked := false }

namespace Grants

def asCreated (g : GrantRec) : GrantRec :=
  { g with consumed := 0, reserved := 0, costConsumed := 0, costReserved := 0, revoked := false }

/-- What a step leaves of each grant: a record from before the step, changed at most in its
counters and `revoked`. -/
def Fixed (s s' : State) : Prop :=
  ∀ (gid : String) (g' : GrantRec), s'.grants[gid]? = some g' →
    ∃ g, s.grants[gid]? = some g ∧ asCreated g' = asCreated g

theorem Fixed.of_grants (h : s'.grants = s.grants) : Fixed s s' :=
  fun _ g' hg => ⟨g', h ▸ hg, rfl⟩

theorem Fixed.trans (h : Fixed s s₁) (h' : Fixed s₁ s₂) : Fixed s s₂ := fun gid g₂ hg => by
  obtain ⟨g₁, h₁, e₁⟩ := h' gid g₂ hg
  obtain ⟨g₀, h₀, e₀⟩ := h gid g₁ h₁
  exact ⟨g₀, h₀, e₁.trans e₀⟩

theorem Fixed.insert (hg : s.grants[gid]? = some g) (he : asCreated g' = asCreated g)
    (hs : s'.grants = s.grants.insert gid g') : Fixed s s' := fun x gx hx => by
  rw [hs, Std.ExtTreeMap.getElem?_insert] at hx
  split at hx
  next h =>
    cases Std.LawfulEqCmp.eq_of_compare h
    cases hx
    exact ⟨g, hg, he⟩
  · exact ⟨gx, hx, rfl⟩

theorem Fixed.modify {F : GrantRec → GrantRec} (hF : ∀ g, asCreated (F g) = asCreated g)
    (hs : s'.grants = s.grants.modify gid F) : Fixed s s' := fun x gx hx => by
  rw [hs, Std.ExtTreeMap.getElem?_modify] at hx
  split at hx
  next h =>
    cases Std.LawfulEqCmp.eq_of_compare h
    cases hk : s.grants[gid]? with
    | none => simp [hk] at hx
    | some g =>
      simp only [hk, Option.map_some, Option.some.injEq] at hx
      subst hx
      exact ⟨g, rfl, hF g⟩
  · exact ⟨gx, hx, rfl⟩

theorem Fixed.map {F : String → GrantRec → GrantRec} (hF : ∀ x g, asCreated (F x g) = asCreated g)
    (hs : s'.grants = s.grants.map F) : Fixed s s' := fun x gx hx => by
  rw [hs, Std.ExtTreeMap.getElem?_map] at hx
  cases hk : s.grants[x]? with
  | none => simp [hk] at hx
  | some g =>
    simp only [hk, Option.map_some, Option.some.injEq] at hx
    subst hx
    exact ⟨g, rfl, hF x g⟩

theorem releaseGrant_fixed : Fixed s (s.releaseGrant k) := by
  unfold State.releaseGrant
  repeat' split
  all_goals first
    | exact Fixed.of_grants rfl
    | (rename_i hg
       exact Fixed.insert (by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hg) (by rfl) rfl)

theorem consumeGrant_fixed : Fixed s (s.consumeGrant k) := by
  unfold State.consumeGrant
  repeat' split
  all_goals first
    | exact Fixed.of_grants rfl
    | (rename_i hg
       exact Fixed.insert (by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hg) (by rfl) rfl)

theorem endCall_fixed {st : CallStatus} : Fixed s (s.endCall k st) := by
  unfold State.endCall
  exact releaseGrant_fixed.trans (Fixed.of_grants rfl)

theorem cancelPending_fixed : Fixed s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (Fixed s) ?_ _ _ (Fixed.of_grants rfl)
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact ha.trans endCall_fixed
  · exact ha.trans endCall_fixed
  · exact ha

theorem interrupt_fixed : Fixed s s.interrupt := by
  unfold State.interrupt
  dsimp only
  exact cancelPending_fixed.trans (Fixed.map (fun _ _ => by rfl) rfl)

theorem claim_fixed {t : Nat} {rc : CallRec} {r : Requirements} {retry : Bool} {key : String} :
    Fixed s (claim p s t k rc r retry key) := by
  have h := claim_grants (p := p) (s := s) (t := t) (k := k) (rc := rc) (r := r) (retry := retry)
    (key := key)
  split at h
  · exact Fixed.of_grants h
  · exact consumeGrant_fixed.trans (Fixed.of_grants h)

theorem applyApprove_grants {t : Nat} {rc : CallRec} {w pr dg : String} {cs : Option Cost}
    {ed : Option Edit} {r : State × Verdict} (h : applyApprove p s t k rc w pr dg cs ed = .ok r) :
    r.1.grants = s.grants := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

local macro "fixed" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Fixed.of_grants rfl
      | exact cancelPending_fixed.trans (Fixed.of_grants rfl)
      | exact interrupt_fixed.trans (Fixed.of_grants rfl)
      | exact endCall_fixed.trans (Fixed.of_grants rfl)
      | exact Fixed.modify (fun _ => by rfl) rfl
      | exact Fixed.of_grants (applyApprove_grants (by assumption))
      | exact Fixed.of_grants (by simp only [recordFailure_grants, recordSuccess_grants,
          settle_grants, withStatus]; done)
      | exact Fixed.of_grants settle_grants)

/-- What step `e` leaves of each grant: a record from before it, changed at most in its counters and
`revoked`, or a record the step's `grant_create` made from its own fields. -/
def Made (s : State) (e : Event) (s' : State) : Prop :=
  ∀ (gid : String) (g' : GrantRec), s'.grants[gid]? = some g' →
    (∃ g, s.grants[gid]? = some g ∧ asCreated g' = asCreated g) ∨
      (s.grants[gid]? = none ∧
        e.body = .grantCreate gid g'.approver g'.tool g'.digest g'.scope g'.maxUses g'.maxCost
          g'.notBefore g'.expiresAt g'.reviewedScopeDigest ∧
        g'.epoch = s.epoch ∧ g'.turn = s.turnIndex ∧
        (∃ info, s.approvers[g'.approver]? = some info ∧ info.principal = g'.principal) ∧
        g' = asCreated g')

theorem Made.of_fixed (h : Fixed s s') : Made s e s' := fun gid g' hg => .inl (h gid g' hg)

theorem eligibleAll_attested {cs : Consent} {a : String} (h : s.eligibleAll p cs a = none) :
    ∃ info, s.approvers[a]? = some info := by
  unfold State.eligibleAll at h
  split at h
  · cases h
  · rename_i hc
    have hm : a ∈ s.approvers := Std.ExtTreeMap.contains_iff_mem.mp (by simpa using hc)
    exact Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hm)

theorem grantDenial_attested {t : Nat} {a tool : String} {dg : Option String} {sc : GrantScope}
    {n : Nat} {mc : Option Cost} {ex : Option Nat}
    (h : grantDenial p s t gid a tool dg sc n mc ex = none) :
    ∃ info, s.approvers[a]? = some info := by
  revert h
  unfold grantDenial
  repeat' split
  all_goals intro h
  all_goals first
    | exact eligibleAll_attested (by assumption)
    | cases h

theorem made_grantCreate {t : Nat} {a tool rv : String} {dg : Option String} {sc : GrantScope}
    {n : Nat} {mc : Option Cost} {nb ex : Option Nat}
    (hb : e.body = .grantCreate gid a tool dg sc n mc nb ex rv) :
    Made s e (handleGrantCreate p s t gid a tool dg sc n mc nb ex rv).1 := by
  unfold handleGrantCreate
  split
  · exact .of_fixed (Fixed.of_grants rfl)
  · rename_i hd
    have hfresh := grantDenial_fresh hd
    obtain ⟨info, hi⟩ := grantDenial_attested hd
    intro x gx hx
    dsimp only at hx
    rw [Std.ExtTreeMap.getElem?_insert] at hx
    split at hx
    next he =>
      cases Std.LawfulEqCmp.eq_of_compare he
      cases hx
      refine .inr ⟨hfresh, hb, rfl, rfl, ⟨info, hi, ?_⟩, rfl⟩
      rw [Std.ExtTreeMap.get?_eq_getElem?, hi]
      rfl
    · exact .inl ⟨gx, hx, rfl⟩

theorem made_grantRevoke : Fixed s (handleGrantRevoke s gid).1 := by
  unfold handleGrantRevoke
  split
  · exact Fixed.of_grants rfl
  · rename_i g hg
    exact Fixed.insert (by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hg) (by rfl) rfl

theorem made_turnEnd : Fixed s (handleTurnEnd s).1 := by
  unfold handleTurnEnd
  split
  · exact Fixed.of_grants rfl
  · exact Fixed.map (fun _ _ => by split <;> rfl) rfl

theorem made_dispatch {t n : Nat} {dg key : String} {cs : Option Cost}
    {g : List (String × Bool)} : Fixed s (handleDispatch p s t k n dg cs g key).1 := by
  rcases Dispatch.handle_cases with he | ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he]
  · exact Fixed.of_grants rfl
  · exact endCall_fixed
  · exact claim_fixed

theorem made_sessionStart {i pd r : String} {ps : List String}
    {as : List (String × ApproverInfo)} {l : Ledger} :
    Fixed s (handleSessionStart s i pd r ps as l).1 := by
  unfold handleSessionStart; fixed

theorem made_sessionEnd : Fixed s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; fixed

theorem made_turnStart {u : Bool} : Fixed s (handleTurnStart s u).1 := by
  unfold handleTurnStart; fixed

theorem made_stepStart : Fixed s (handleStepStart p s).1 := by
  unfold handleStepStart; fixed

theorem made_approverAttest {a : String} {i : ApproverInfo} :
    Fixed s (handleApproverAttest s a i).1 := by
  unfold handleApproverAttest; fixed

theorem made_permissionRevoke {a : String} : Fixed s (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; fixed

theorem made_propose {t : Nat} {tool dg : String} {cs : Option Cost}
    {gs xs : List (String × Bool)} :
    Fixed s (handlePropose p s t k tool dg cs gs xs).1 := by
  unfold handlePropose; fixed

theorem made_approve {t : Nat} {rid : RequestId} {w dg : String} {cs : Option Cost}
    {ed : Option Edit} :
    Fixed s (handleApprove p s t k rid w dg cs ed).1 := by
  unfold handleApprove; fixed

theorem made_reject {rid : RequestId} {w : String} : Fixed s (handleReject p s k rid w).1 := by
  unfold handleReject
  split
  · exact Fixed.of_grants rfl
  · exact endCall_fixed.trans (Fixed.of_grants (s := s.endCall k .rejected) rfl)

theorem made_approvalExpire {rid : RequestId} : Fixed s (handleApprovalExpire s k rid).1 := by
  unfold handleApprovalExpire; fixed

theorem made_result {t : Nat} {o : Outcome} {a : Option Nat} {ne : Bool} :
    Fixed s (handleResult p s t k o a ne).1 := by
  unfold handleResult; fixed

theorem made_outcomeUnknown : Fixed s (handleOutcomeUnknown p s k).1 := by
  unfold handleOutcomeUnknown; fixed

theorem made_reconcile {t : Nat} {o : Outcome} {a : Option Nat} {ne : Bool} :
    Fixed s (handleReconcile p s t k o a ne).1 := by
  unfold handleReconcile; fixed

theorem made_cancel : Fixed s (handleCancel s k).1 := by
  unfold handleCancel; fixed

theorem made_reset : Fixed s (handleReset s).1 := by
  unfold handleReset; fixed

theorem made_kill : Fixed s (handleKill p s).1 := by
  unfold handleKill; fixed

theorem made_permissionAdd {a b : String} : Fixed s (handlePermissionAdd p s a b).1 := by
  unfold handlePermissionAdd; fixed

theorem made_escalationAck {a : String} {n : Nat} : Fixed s (handleEscalationAck p s a n).1 := by
  unfold handleEscalationAck; fixed

theorem made_ledgerSync {l : Ledger} : Fixed s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; fixed

theorem made_stepHandle : Made s e (stepHandle p s e).1 := by
  unfold Writ.stepHandle
  split <;> rename_i hb
  · exact .of_fixed made_sessionStart
  · exact .of_fixed made_sessionEnd
  · exact .of_fixed made_turnStart
  · exact .of_fixed made_turnEnd
  · exact .of_fixed made_stepStart
  · exact .of_fixed made_approverAttest
  · exact .of_fixed made_permissionRevoke
  · exact .of_fixed made_propose
  · exact .of_fixed made_approve
  · exact .of_fixed made_reject
  · exact .of_fixed made_approvalExpire
  · exact made_grantCreate hb
  · exact .of_fixed made_grantRevoke
  · exact .of_fixed made_dispatch
  · exact .of_fixed made_result
  · exact .of_fixed made_outcomeUnknown
  · exact .of_fixed made_reconcile
  · exact .of_fixed made_cancel
  · exact .of_fixed made_reset
  · exact .of_fixed made_kill
  · exact .of_fixed made_permissionAdd
  · exact .of_fixed made_escalationAck
  · exact .of_fixed made_ledgerSync

theorem origin_mono (h : GrantOrigin p d es gid g) : GrantOrigin p d (es ++ [e]) gid g := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem origin_congr (h : GrantOrigin p d es gid g) (he : asCreated g' = asCreated g) :
    GrantOrigin p d es gid g' := by
  have h₁ : g'.approver = g.approver :=
    show (asCreated g').approver = (asCreated g).approver from congrArg (·.approver) he
  have h₂ : g'.tool = g.tool :=
    show (asCreated g').tool = (asCreated g).tool from congrArg (·.tool) he
  have h₃ : g'.digest = g.digest :=
    show (asCreated g').digest = (asCreated g).digest from congrArg (·.digest) he
  have h₄ : g'.scope = g.scope :=
    show (asCreated g').scope = (asCreated g).scope from congrArg (·.scope) he
  have h₅ : g'.maxUses = g.maxUses :=
    show (asCreated g').maxUses = (asCreated g).maxUses from congrArg (·.maxUses) he
  have h₆ : g'.maxCost = g.maxCost :=
    show (asCreated g').maxCost = (asCreated g).maxCost from congrArg (·.maxCost) he
  have h₇ : g'.notBefore = g.notBefore :=
    show (asCreated g').notBefore = (asCreated g).notBefore from congrArg (·.notBefore) he
  have h₈ : g'.expiresAt = g.expiresAt :=
    show (asCreated g').expiresAt = (asCreated g).expiresAt from congrArg (·.expiresAt) he
  have h₉ : g'.reviewedScopeDigest = g.reviewedScopeDigest :=
    show (asCreated g').reviewedScopeDigest = (asCreated g).reviewedScopeDigest from
      congrArg (·.reviewedScopeDigest) he
  have h₁₀ : g'.epoch = g.epoch :=
    show (asCreated g').epoch = (asCreated g).epoch from congrArg (·.epoch) he
  have h₁₁ : g'.turn = g.turn :=
    show (asCreated g').turn = (asCreated g).turn from congrArg (·.turn) he
  have h₁₂ : g'.principal = g.principal :=
    show (asCreated g').principal = (asCreated g).principal from congrArg (·.principal) he
  obtain ⟨s₀, e₀, v₀, hm, ha, hn, hb, hep, htu, hpr, hst⟩ := h
  refine ⟨s₀, e₀, v₀, hm, ha, hn, ?_, h₁₀.trans hep, h₁₁.trans htu, ?_, ?_⟩
  · rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]; exact hb
  · rw [h₁, h₁₂]; exact hpr
  · exact hst.trans (congrArg some he.symm)

end Grants

/-- Section 8, theorems 1 and 2: every grant record holds the limits of the accepted `grant_create`
that created it (`max_uses`, `max_cost`, `not_before`, `expires_at`, scope, digest or any
arguments, tool, approver and reviewed scope digest), with its epoch, turn and the approver's
attested principal at that event; only the use and cost counters and `revoked` change afterwards. -/
theorem grant_origin (hg : (after p d es).grants[gid]? = some g) : GrantOrigin p d es gid g := by
  refine snoc_induction (P := fun es => ∀ gid g, (after p d es).grants[gid]? = some g →
    GrantOrigin p d es gid g) (fun gid g h => by simp [after_nil, State.initial] at h) ?_ es
    gid g hg
  intro es e ih gid g' h
  rw [after_snoc] at h
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at h
    exact origin_mono (ih gid g' h)
  · have hst := accepted_step ha
    rw [hst] at h
    rcases made_stepHandle (p := p) gid g' h with ⟨g, hg, he⟩ | ⟨hn, hb, hep, htu, hpr, hc⟩
    · exact origin_mono (origin_congr (ih gid g hg) he)
    · refine ⟨_, _, _, trace_mem_last, ha, hn, hb, hep, htu, hpr, ?_⟩
      rw [hst]
      exact h.trans (congrArg some hc)

namespace Grants

def usePolicy : Policy :=
  { approverRoles := ["owner"]
    actions :=
      [("pay", { consent := .perCall, grantable := some { scope := .session, maxUses := 1 } })] }

def useApprovers : List (String × ApproverInfo) := [("a1", ⟨"alice", .human, ["owner"]⟩)]

def useOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] useApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .grantCreate "g1" "a1" "pay" (some "d1") .session 1 none none none "r1"⟩
  , ⟨4, 4, 3, none, .propose "c1" "pay" "d1" none [] []⟩ ]

def useCancel : List Event := useOpen ++ [⟨5, 5, 4, none, .cancel "c1"⟩]

def proposeC2 (seq : Nat) : Event := ⟨seq, seq, seq - 1, none, .propose "c2" "pay" "d1" none [] []⟩

def useReuse : List Event :=
  useCancel ++ [proposeC2 6, ⟨7, 7, 6, none, .dispatch "c2" 1 "d1" none [] "k2"⟩]

def counts (s : State) (gid : String) : Option (Nat × Nat × Nat × Nat) :=
  (s.grants[gid]?).map fun g =>
    (g.reserved, (reservedCalls s gid).length, g.consumed, (consumedCalls s gid).length)

#guard decide usePolicy.WF
#guard (trace usePolicy (State.initial "pd") useReuse).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .none none, .ok (.allowedByGrant "g1") none,
       .ok .none none, .ok (.allowedByGrant "g1") none, .ok .dispatchClaimed none ]
#guard counts (after usePolicy "pd" useOpen) "g1" == some (1, 1, 0, 0)
#guard (step usePolicy (after usePolicy "pd" useOpen) (proposeC2 5)).2
  == .ok (.needsApproval ⟨"s1", "c2", 0⟩) none
#guard counts (after usePolicy "pd" useCancel) "g1" == some (0, 0, 0, 0)
#guard counts (after usePolicy "pd" useReuse) "g1" == some (0, 0, 1, 1)
#guard grantClaims usePolicy "pd" useReuse "g1" == [none]
#guard ((after usePolicy "pd" useReuse).grants["g1"]?).map (·.maxUses) == some 1

def costPolicy : Policy :=
  { approverRoles := ["owner"]
    actions :=
      [("pay", { consent := .perCall, grantable := some { scope := .session, maxUses := 5 } })] }

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩

/-- `c2` would bring the grant's cost to 12 of 10, so it needs an approval; `c3` fits exactly. -/
def costEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] useApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .grantCreate "g1" "a1" "pay" (some "d1") .session 5 (usd 10) none none "r1"⟩
  , ⟨4, 4, 3, none, .propose "c1" "pay" "d1" (usd 6) [] []⟩
  , ⟨5, 5, 4, none, .propose "c2" "pay" "d1" (usd 6) [] []⟩
  , ⟨6, 6, 5, none, .propose "c3" "pay" "d1" (usd 4) [] []⟩
  , ⟨7, 7, 6, none, .dispatch "c1" 1 "d1" (usd 6) [] "k1"⟩ ]

#guard decide costPolicy.WF
#guard (trace costPolicy (State.initial "pd") costEvents).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .none none, .ok (.allowedByGrant "g1") none,
       .ok (.needsApproval ⟨"s1", "c2", 0⟩) none, .ok (.allowedByGrant "g1") none,
       .ok .dispatchClaimed none ]
#guard ((after costPolicy "pd" costEvents).grants["g1"]?).any fun g =>
  g.maxCost == usd 10 && g.costReserved == 4 && g.costConsumed == 6 &&
    g.costReserved == costOf (after costPolicy "pd" costEvents)
      (reservedCalls (after costPolicy "pd" costEvents) "g1") &&
    g.costConsumed == costOf (after costPolicy "pd" costEvents)
      (consumedCalls (after costPolicy "pd" costEvents) "g1")
#guard grantClaims costPolicy "pd" costEvents "g1" == [usd 6]

/-- `GrantOrigin` as a check. -/
def createdBy (p : Policy) (d : String) (es : List Event) (gid : String) (g : GrantRec) : Bool :=
  (trace p (State.initial d) es).any fun (s₀, e₀, v₀) =>
    v₀.accepted && s₀.grants[gid]?.isNone &&
      e₀.body == .grantCreate gid g.approver g.tool g.digest g.scope g.maxUses g.maxCost
        g.notBefore g.expiresAt g.reviewedScopeDigest &&
      g.epoch == s₀.epoch && g.turn == s₀.turnIndex &&
      (s₀.approvers[g.approver]?).any (·.principal == g.principal) &&
      (step p s₀ e₀).1.grants[gid]? == some (asCreated g)

/-- `pay` allows grants of up to 5 uses; `g2` asks for one use inside a window and is revoked. -/
def limitEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] useApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .grantCreate "g2" "a1" "pay" (some "d2") .session 1 none (some 2) (some 100)
      "r2"⟩
  , ⟨4, 4, 3, none, .grantRevoke "g2"⟩ ]

#guard ((after costPolicy "pd" costEvents).grants["g1"]?).any fun g =>
  createdBy costPolicy "pd" costEvents "g1" g && g.principal == "alice" && g.maxUses == 5 &&
    g.consumed == 1 && g.reserved == 1 && g.costConsumed == 6 && g.costReserved == 4
#guard (trace costPolicy (State.initial "pd") limitEvents).all (·.2.2.accepted)
#guard ((after costPolicy "pd" limitEvents).grants["g2"]?).any fun g =>
  createdBy costPolicy "pd" limitEvents "g2" g && g.maxUses == 1 && g.notBefore == some 2 &&
    g.expiresAt == some 100 && g.revoked
#guard ((costPolicy.action? "pay").bind (·.grantable)).map (·.maxUses) == some 5

def retryGrantPolicy : Policy :=
  { approverRoles := ["owner"]
    actions :=
      [("pay", { consent := .perCall, idempotent := true, retryAfterUnknown := true
                 maxAttempts := 2, grantable := some { scope := .session, maxUses := 1 } })] }

def retryGrantOpen : List Event :=
  useOpen ++
    [⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩, ⟨6, 6, 5, none, .outcomeUnknown "c1"⟩]

def retryGrantEvent : Event := ⟨7, 7, 6, none, .dispatch "c1" 2 "d1" none [] "k1"⟩

#guard decide retryGrantPolicy.WF
#guard (trace retryGrantPolicy (State.initial "pd") (retryGrantOpen ++ [retryGrantEvent])).map
  (·.2.2) == [ .ok .none none, .ok .none none, .ok .none none, .ok (.allowedByGrant "g1") none,
    .ok .dispatchClaimed none, .ok .none none, .ok .dispatchClaimed none ]
#guard ((after retryGrantPolicy "pd" retryGrantOpen).calls["c1"]?).any (·.status == .unknown)
#guard (step retryGrantPolicy (after retryGrantPolicy "pd" retryGrantOpen) retryGrantEvent).1.grants
  == (after retryGrantPolicy "pd" retryGrantOpen).grants
#guard counts (after retryGrantPolicy "pd" (retryGrantOpen ++ [retryGrantEvent])) "g1"
  == some (0, 0, 1, 1)
#guard grantClaims retryGrantPolicy "pd" (retryGrantOpen ++ [retryGrantEvent]) "g1" == [none]

end Grants

end Writ.Proofs
