import Writ.Author.Join

namespace Writ.Proofs

open Writ

namespace Join

section Generic

variable {α : Type} {le : α → α → Prop} {j : α → α → α}

theorem comm_of (hl : ∀ a b, le a (j a b)) (hr : ∀ a b, le b (j a b))
    (hlub : ∀ {a b c}, le a c → le b c → le (j a b) c) (a b : α) :
    le (j a b) (j b a) ∧ le (j b a) (j a b) :=
  ⟨hlub (hr b a) (hl b a), hlub (hr a b) (hl a b)⟩

theorem assoc_of (htrans : ∀ {a b c}, le a b → le b c → le a c) (hl : ∀ a b, le a (j a b))
    (hr : ∀ a b, le b (j a b)) (hlub : ∀ {a b c}, le a c → le b c → le (j a b) c) (a b c : α) :
    le (j (j a b) c) (j a (j b c)) ∧ le (j a (j b c)) (j (j a b) c) :=
  ⟨hlub (hlub (hl _ _) (htrans (hl b c) (hr _ _))) (htrans (hr b c) (hr _ _)),
    hlub (htrans (hl a b) (hl _ _)) (hlub (htrans (hr a b) (hl _ _)) (hr _ _))⟩

theorem idem_of (hrefl : ∀ a, le a a) (hl : ∀ a b, le a (j a b))
    (hlub : ∀ {a b c}, le a c → le b c → le (j a b) c) (a : α) :
    le (j a a) a ∧ le a (j a a) :=
  ⟨hlub (hrefl a) (hrefl a), hl a a⟩

theorem mono_of (htrans : ∀ {a b c}, le a b → le b c → le a c) (hl : ∀ a b, le a (j a b))
    (hr : ∀ a b, le b (j a b)) (hlub : ∀ {a b c}, le a c → le b c → le (j a b) c) {a a' b b' : α}
    (ha : le a a') (hb : le b b') : le (j a b) (j a' b') :=
  hlub (htrans ha (hl _ _)) (htrans hb (hr _ _))

end Generic

theorem mem_foldl_step [DecidableEq α] {x : α} : ∀ (l acc : List α),
    x ∈ l.foldl (fun acc y => if y ∈ acc then acc else acc ++ [y]) acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc => by simp
  | y :: l, acc => by
    rw [List.foldl_cons, mem_foldl_step l]
    by_cases h : y ∈ acc
    · simp only [h, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (hx | hx) <;> simp [hx]
      · rintro (hx | rfl | hx) <;> simp [*]
    · simp only [h, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false]
      constructor
      · rintro ((hx | hx) | hx) <;> simp [hx]
      · rintro (hx | hx | hx) <;> simp [hx]

theorem nodup_foldl_step [DecidableEq α] : ∀ (l acc : List α), acc.Nodup →
    (l.foldl (fun acc y => if y ∈ acc then acc else acc ++ [y]) acc).Nodup
  | [], _, h => h
  | y :: l, acc, h => by
    rw [List.foldl_cons]
    apply nodup_foldl_step l
    by_cases hy : y ∈ acc
    · simp only [hy, ↓reduceIte]; exact h
    · simp only [hy, ↓reduceIte]
      refine List.nodup_append.mpr ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb heq
      rw [List.mem_singleton] at hb
      exact hy (hb ▸ heq ▸ ha)

theorem mem_listJoin [DecidableEq α] {x : α} {a b : List α} :
    x ∈ listJoin a b ↔ x ∈ a ∨ x ∈ b := by
  unfold listJoin
  rw [mem_foldl_step]
  simp

theorem nodup_listJoin [DecidableEq α] (a b : List α) : (listJoin a b).Nodup :=
  nodup_foldl_step _ _ List.nodup_nil

theorem mem_guardJoin {x : String} {a b : List String} :
    x ∈ guardJoin a b ↔ x ∈ a ∨ x ∈ b := by
  unfold guardJoin
  rw [List.mem_mergeSort, mem_listJoin]

theorem mem_flagJoin {x : Flag} {a b : List Flag} :
    x ∈ flagJoin a b ↔ x ∈ a ∨ x ∈ b := by
  unfold flagJoin
  rw [List.mem_mergeSort, mem_listJoin]

theorem eq_of_sorted {α : Type} {le : α → α → Bool} (antisymm : ∀ a b, le a b → le b a → a = b) :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise (fun a b => le a b = true) →
      l₂.Pairwise (fun a b => le a b = true) → l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) →
      l₁ = l₂
  | [], [], _, _, _, _, _ => rfl
  | [], b :: _, _, _, _, _, hm => absurd ((hm b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, _, _, hm => absurd ((hm a).mp List.mem_cons_self) List.not_mem_nil
  | a :: t₁, b :: t₂, hs₁, hs₂, hn₁, hn₂, hm => by
    have hab : a = b := by
      rcases List.mem_cons.mp ((hm a).mp List.mem_cons_self) with h | h
      · exact h
      rcases List.mem_cons.mp ((hm b).mpr List.mem_cons_self) with h' | h'
      · exact h'.symm
      exact antisymm a b (List.rel_of_pairwise_cons hs₁ h') (List.rel_of_pairwise_cons hs₂ h)
    subst hab
    have hn₁' := List.nodup_cons.mp hn₁
    have hn₂' := List.nodup_cons.mp hn₂
    congr 1
    refine eq_of_sorted antisymm hs₁.of_cons hs₂.of_cons hn₁'.2 hn₂'.2 fun x =>
      ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem _ hx)) with h | h
      · subst h; exact absurd hx hn₁'.1
      · exact h
    · rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem _ hx)) with h | h
      · subst h; exact absurd hx hn₂'.1
      · exact h

theorem guardJoin_eq {a b c d : List String} (h : ∀ x, x ∈ a ∨ x ∈ b ↔ x ∈ c ∨ x ∈ d) :
    guardJoin a b = guardJoin c d := by
  have hs : ∀ l : List String, (l.mergeSort fun x y => decide (x ≤ y)).Pairwise
      (fun x y => decide (x ≤ y) = true) :=
    List.pairwise_mergeSort
      (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact String.le_trans h₁ h₂)
      (fun x y => by simpa using String.le_total x y)
  refine eq_of_sorted
    (fun x y h₁ h₂ => String.le_antisymm (of_decide_eq_true h₁) (of_decide_eq_true h₂))
    (hs _) (hs _) ((List.mergeSort_perm _ _).nodup_iff.mpr (nodup_listJoin _ _))
    ((List.mergeSort_perm _ _).nodup_iff.mpr (nodup_listJoin _ _)) fun x => ?_
  rw [mem_guardJoin, mem_guardJoin]; exact h x

theorem flagJoin_eq {a b c d : List Flag} (h : ∀ x, x ∈ a ∨ x ∈ b ↔ x ∈ c ∨ x ∈ d) :
    flagJoin a b = flagJoin c d := by
  have hs : ∀ l : List Flag, (l.mergeSort fun x y => decide (x.rank ≤ y.rank)).Pairwise
      (fun x y => decide (x.rank ≤ y.rank) = true) :=
    List.pairwise_mergeSort (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
      (fun x y => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
  have hanti : ∀ x y : Flag, decide (x.rank ≤ y.rank) = true → decide (y.rank ≤ x.rank) = true →
      x = y := by
    intro x y; cases x <;> cases y <;> decide
  refine eq_of_sorted hanti (hs _) (hs _) ((List.mergeSort_perm _ _).nodup_iff.mpr (nodup_listJoin _ _))
    ((List.mergeSort_perm _ _).nodup_iff.mpr (nodup_listJoin _ _)) fun x => ?_
  rw [mem_flagJoin, mem_flagJoin]; exact h x

theorem consent_join_groups (a b : Consent) :
    (a.join b).groups = listJoin a.groups b.groups := rfl

theorem rolesLe_refl : ∀ r : Option (List String), RolesLe r r
  | none => trivial
  | some _ => fun _ h => h

theorem rolesLe_trans : ∀ {a b c : Option (List String)}, RolesLe a b → RolesLe b c → RolesLe a c
  | none, _, _, _, _ => trivial
  | some _, none, _, h, _ => h.elim
  | some _, some _, none, _, h => h.elim
  | some _, some _, some _, h₁, h₂ => fun r hr => h₁ r (h₂ r hr)

theorem clause_le_refl (x : Clause) : x.le x :=
  ⟨Nat.le_refl _, rolesLe_refl _, id, id⟩

theorem clause_le_trans {x y z : Clause} (h₁ : x.le y) (h₂ : y.le z) : x.le z :=
  ⟨Nat.le_trans h₁.1 h₂.1, rolesLe_trans h₁.2.1 h₂.2.1, h₂.2.2.1 ∘ h₁.2.2.1,
    h₂.2.2.2 ∘ h₁.2.2.2⟩

theorem matches_refl : ∀ xs : List Clause, Clause.Matches xs xs
  | [] => trivial
  | x :: xs => ⟨x, List.mem_cons_self, clause_le_refl x, by
      rw [List.erase_cons_head]; exact matches_refl xs⟩

theorem matches_swap {a b : Clause} {l zs : List Clause} :
    Clause.Matches (a :: b :: l) zs → Clause.Matches (b :: a :: l) zs := by
  rintro ⟨z₁, h₁, ha, z₂, h₂, hb, hl⟩
  refine ⟨z₂, List.mem_of_mem_erase h₂, hb, z₁, ?_, ha, ?_⟩
  · by_cases h : z₁ = z₂
    · subst h; exact h₂
    · exact (List.mem_erase_of_ne h).mpr h₁
  · rw [List.erase_comm]; exact hl

theorem matches_perm {l₁ l₂ : List Clause} (hp : l₁.Perm l₂) :
    ∀ {zs}, Clause.Matches l₁ zs → Clause.Matches l₂ zs := by
  induction hp with
  | nil => exact id
  | cons x _ ih => rintro zs ⟨y, hy, hx, hm⟩; exact ⟨y, hy, hx, ih hm⟩
  | swap a b l => exact matches_swap
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

theorem matches_trans : ∀ {xs ys zs : List Clause}, Clause.Matches xs ys →
    Clause.Matches ys zs → Clause.Matches xs zs
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, ⟨_, hy, hxy, hm⟩, hyz => by
    obtain ⟨z, hz, hyz', hm'⟩ := matches_perm (List.perm_cons_erase hy) hyz
    exact ⟨z, hz, clause_le_trans hxy hyz', matches_trans hm hm'⟩

theorem group_le_refl (g : Group) : g.le g :=
  ⟨id, fun _ => matches_refl _, fun x hx => ⟨x, hx, clause_le_refl x⟩⟩

theorem group_le_trans {g h i : Group} (h₁ : g.le h) (h₂ : h.le i) : g.le i := by
  refine ⟨h₂.1 ∘ h₁.1, fun hd => matches_trans (h₁.2.1 hd) (h₂.2.1 (h₁.1 hd)), fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := h₁.2.2 x hx
  obtain ⟨z, hz, hyz⟩ := h₂.2.2 y hy
  exact ⟨z, hz, clause_le_trans hxy hyz⟩

theorem durLe_refl : ∀ d : Option Nat, DurLe d d
  | none => trivial
  | some n => Nat.le_refl n

theorem durLe_trans : ∀ {a b c : Option Nat}, DurLe a b → DurLe b c → DurLe a c
  | none, _, _, _, _ => trivial
  | some _, none, _, h, _ => h.elim
  | some _, some _, none, _, h => h.elim
  | some _, some _, some _, h₁, h₂ => Nat.le_trans h₂ h₁

theorem durLe_meet_left : ∀ a b : Option Nat, DurLe a (durMeet a b)
  | none, _ => trivial
  | some _, none => Nat.le_refl _
  | some _, some _ => Nat.min_le_left _ _

theorem durLe_meet_right : ∀ a b : Option Nat, DurLe b (durMeet a b)
  | _, none => trivial
  | none, some _ => Nat.le_refl _
  | some _, some _ => Nat.min_le_right _ _

theorem durMeet_le : ∀ {a b c : Option Nat}, DurLe a c → DurLe b c → DurLe (durMeet a b) c
  | none, _, _, _, h => h
  | some _, none, _, h, _ => h
  | some _, some _, none, h, _ => h.elim
  | some _, some _, some _, h₁, h₂ => Nat.le_min.mpr ⟨h₁, h₂⟩

theorem durMeet_comm : ∀ a b : Option Nat, durMeet a b = durMeet b a
  | none, none | none, some _ | some _, none => rfl
  | some m, some n => by simp only [durMeet, Nat.min_comm]

theorem durMeet_assoc : ∀ a b c : Option Nat, durMeet (durMeet a b) c = durMeet a (durMeet b c)
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl
  | some m, some n, some k => by simp only [durMeet, Nat.min_assoc]

theorem durMeet_idem : ∀ a : Option Nat, durMeet a a = a
  | none => rfl
  | some m => by simp only [durMeet, Nat.min_self]

theorem scope_le_refl : ∀ s : GrantScope, GrantScope.le s s = true
  | .turn | .session => rfl

theorem scope_le_trans : ∀ {a b c : GrantScope}, GrantScope.le a b = true →
    GrantScope.le b c = true → GrantScope.le a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem scopeMeet_le_left : ∀ a b : GrantScope, GrantScope.le (scopeMeet a b) a = true := by
  intro a b; cases a <;> cases b <;> decide

theorem scopeMeet_le_right : ∀ a b : GrantScope, GrantScope.le (scopeMeet a b) b = true := by
  intro a b; cases a <;> cases b <;> decide

theorem le_scopeMeet : ∀ {a b c : GrantScope}, GrantScope.le c a = true →
    GrantScope.le c b = true → GrantScope.le c (scopeMeet a b) = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem scopeMeet_comm : ∀ a b : GrantScope, scopeMeet a b = scopeMeet b a := by
  intro a b; cases a <;> cases b <;> rfl

theorem scopeMeet_assoc : ∀ a b c : GrantScope,
    scopeMeet (scopeMeet a b) c = scopeMeet a (scopeMeet b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem scopeMeet_idem : ∀ a : GrantScope, scopeMeet a a = a := by
  intro a; cases a <;> rfl

theorem boolLe_and_left (a b : Bool) : BoolLe a (a && b) := by cases a <;> cases b <;> decide

theorem boolLe_and_right (a b : Bool) : BoolLe b (a && b) := by cases a <;> cases b <;> decide

theorem and_boolLe {a b c : Bool} (h₁ : BoolLe a c) (h₂ : BoolLe b c) : BoolLe (a && b) c := by
  revert h₁ h₂; cases a <;> cases b <;> cases c <;> decide

theorem boolLe_trans {a b c : Bool} (h₁ : BoolLe a b) (h₂ : BoolLe b c) : BoolLe a c :=
  h₁ ∘ h₂

theorem grantable_le_refl (a : Grantable) : a.le a :=
  ⟨scope_le_refl _, Nat.le_refl _, durLe_refl _, id, id⟩

theorem grantable_le_trans {a b c : Grantable} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  ⟨scope_le_trans h₂.1 h₁.1, Nat.le_trans h₂.2.1 h₁.2.1, durLe_trans h₁.2.2.1 h₂.2.2.1,
    h₁.2.2.2.1 ∘ h₂.2.2.2.1, h₁.2.2.2.2 ∘ h₂.2.2.2.2⟩

theorem grantable_le_meet_left (a b : Grantable) : a.le (a.meet b) :=
  ⟨scopeMeet_le_left _ _, Nat.min_le_left _ _, durLe_meet_left _ _, boolLe_and_left _ _,
    boolLe_and_left _ _⟩

theorem grantable_le_meet_right (a b : Grantable) : b.le (a.meet b) :=
  ⟨scopeMeet_le_right _ _, Nat.min_le_right _ _, durLe_meet_right _ _, boolLe_and_right _ _,
    boolLe_and_right _ _⟩

theorem grantable_meet_le {a b c : Grantable} (h₁ : a.le c) (h₂ : b.le c) : (a.meet b).le c :=
  ⟨le_scopeMeet h₁.1 h₂.1, Nat.le_min.mpr ⟨h₁.2.1, h₂.2.1⟩, durMeet_le h₁.2.2.1 h₂.2.2.1,
    and_boolLe h₁.2.2.2.1 h₂.2.2.2.1, and_boolLe h₁.2.2.2.2 h₂.2.2.2.2⟩

theorem grantable_meet_comm (a b : Grantable) : a.meet b = b.meet a := by
  simp only [Grantable.meet, scopeMeet_comm a.scope, Nat.min_comm a.maxUses,
    durMeet_comm a.maxDurationMs, Bool.and_comm a.anyArgs, Bool.and_comm a.allowAnyArgsMetered]

theorem grantable_meet_assoc (a b c : Grantable) : (a.meet b).meet c = a.meet (b.meet c) := by
  simp only [Grantable.meet, scopeMeet_assoc, Nat.min_assoc, durMeet_assoc, Bool.and_assoc]

theorem grantable_meet_idem (a : Grantable) : a.meet a = a := by
  simp only [Grantable.meet, scopeMeet_idem, Nat.min_self, durMeet_idem, Bool.and_self]

theorem capBy_le (x : Grantable) (s : Option GrantScope) (u d : Option Nat) (a : Option Bool) :
    x.le (x.capBy s u d a) := by
  refine ⟨?_, ?_, durLe_meet_left _ _, boolLe_and_left _ _, id⟩
  · cases s <;> simp only [Grantable.capBy, scope_le_refl, scopeMeet_le_left]
  · cases u <;> simp only [Grantable.capBy, Nat.le_refl, Nat.min_le_left]

theorem cap_le_capBy (x : Grantable) (s : Option GrantScope) (u d : Option Nat) (a : Option Bool) :
    (GrantCap.cap s u d a).le (some (x.capBy s u d a)) := by
  refine ⟨?_, ?_, durLe_meet_right _ _, boolLe_and_right _ _⟩
  · cases s <;> simp only [Grantable.capBy, Option.all, scopeMeet_le_right]
  · cases u
    · trivial
    · exact Nat.min_le_right _ _

theorem capBy_le_of {x y : Grantable} {s : Option GrantScope} {u d : Option Nat} {a : Option Bool}
    (hxy : x.le y) (hc : (GrantCap.cap s u d a).le (some y)) : (x.capBy s u d a).le y := by
  obtain ⟨hs, hu, hd, ha⟩ := hc
  refine ⟨?_, ?_, durMeet_le hxy.2.2.1 hd, and_boolLe hxy.2.2.2.1 ha, hxy.2.2.2.2⟩
  · cases s with
    | none => exact hxy.1
    | some t => exact le_scopeMeet hxy.1 (by simpa [Option.all] using hs)
  · cases u with
    | none => exact hxy.2.1
    | some n => exact Nat.le_min.mpr ⟨hxy.2.1, hu⟩

theorem cap_le_mono : ∀ {c : GrantCap} {g h : Option Grantable}, c.le g → GrantLe g h → c.le h
  | .forbid, _, none, _, _ => rfl
  | .forbid, none, some _, _, h => h.elim
  | .forbid, some _, some _, hc, _ => by cases hc
  | .cap .., _, none, _, _ => trivial
  | .cap .., none, some _, _, h => h.elim
  | .cap s u d a, some x, some y, hc, hxy => by
    obtain ⟨hs, hu, hd, ha⟩ := hc
    refine ⟨?_, durLe_trans hu hxy.2.1, durLe_trans hd hxy.2.2.1, boolLe_trans ha hxy.2.2.2.1⟩
    cases s with
    | none => rfl
    | some t => exact scope_le_trans hxy.1 (by simpa [Option.all] using hs)

end Join

open Join

/-- `Consent.le` is reflexive. -/
theorem consent_le_refl (c : Consent) : c.le c :=
  fun g hg => ⟨g, hg, group_le_refl g⟩

/-- `Consent.le` is transitive. -/
theorem consent_le_trans {a b c : Consent} (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  intro g hg
  obtain ⟨h, hh, hgh⟩ := h₁ g hg
  obtain ⟨i, hi, hhi⟩ := h₂ h hh
  exact ⟨i, hi, group_le_trans hgh hhi⟩

/-- `Consent.none` (no groups) is the least strict consent. -/
theorem consent_none_le (c : Consent) : Consent.none.le c :=
  fun _ hg => nomatch hg

/-- The join keeps equal groups once: its groups have no duplicates. -/
theorem consent_join_nodup (a b : Consent) : (a.join b).groups.Nodup :=
  nodup_listJoin _ _

/-- A group is in the join exactly when it is a group of either argument. -/
theorem consent_mem_join {g : Group} {a b : Consent} :
    g ∈ (a.join b).groups ↔ g ∈ a.groups ∨ g ∈ b.groups := mem_listJoin

/-- Upper bound: the join is at least as strict as its left argument. -/
theorem consent_le_join_left (a b : Consent) : a.le (a.join b) :=
  fun g hg => ⟨g, consent_mem_join.mpr (.inl hg), group_le_refl g⟩

/-- Upper bound: the join is at least as strict as its right argument. -/
theorem consent_le_join_right (a b : Consent) : b.le (a.join b) :=
  fun g hg => ⟨g, consent_mem_join.mpr (.inr hg), group_le_refl g⟩

/-- Least upper bound: a consent at least as strict as both arguments is at least as strict as
their join. -/
theorem consent_join_le {a b c : Consent} (h₁ : a.le c) (h₂ : b.le c) : (a.join b).le c := by
  intro g hg
  rcases consent_mem_join.mp hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

/-- Commutative up to the order's equivalence (`Consent.le` both ways): the groups are the same,
in a different order. -/
theorem consent_join_comm (a b : Consent) : (a.join b).le (b.join a) ∧ (b.join a).le (a.join b) :=
  comm_of consent_le_join_left consent_le_join_right consent_join_le a b

/-- Associative up to the order's equivalence (`Consent.le` both ways). -/
theorem consent_join_assoc (a b c : Consent) :
    ((a.join b).join c).le (a.join (b.join c)) ∧ (a.join (b.join c)).le ((a.join b).join c) :=
  assoc_of (le := Consent.le) (j := Consent.join) consent_le_trans consent_le_join_left
    consent_le_join_right consent_join_le a b c

/-- Idempotent up to the order's equivalence (`Consent.le` both ways). -/
theorem consent_join_idem (a : Consent) : (a.join a).le a ∧ a.le (a.join a) :=
  idem_of consent_le_refl consent_le_join_left consent_join_le a

/-- `GrantLe` is reflexive. -/
theorem grant_le_refl : ∀ g : Option Grantable, GrantLe g g
  | none => trivial
  | some a => grantable_le_refl a

/-- `GrantLe` is transitive. -/
theorem grant_le_trans : ∀ {a b c : Option Grantable}, GrantLe a b → GrantLe b c → GrantLe a c
  | _, _, none, _, _ => trivial
  | _, none, some _, _, h => h.elim
  | none, some _, some _, h, _ => h.elim
  | some _, some _, some _, h₁, h₂ => grantable_le_trans h₁ h₂

/-- Upper bound: the grantable meet is at least as strict as its left argument. -/
theorem grant_le_join_left : ∀ a b : Option Grantable, GrantLe a (grantJoin a b)
  | some a, some b => grantable_le_meet_left a b
  | none, _ | some _, none => trivial

/-- Upper bound: the grantable meet is at least as strict as its right argument. -/
theorem grant_le_join_right : ∀ a b : Option Grantable, GrantLe b (grantJoin a b)
  | some a, some b => grantable_le_meet_right a b
  | none, _ | some _, none => trivial

/-- Least upper bound for the grantable meet. -/
theorem grant_join_le : ∀ {a b c : Option Grantable}, GrantLe a c → GrantLe b c →
    GrantLe (grantJoin a b) c
  | _, _, none, _, _ => trivial
  | none, _, some _, h, _ => h.elim
  | some _, none, some _, _, h => h.elim
  | some _, some _, some _, h₁, h₂ => grantable_meet_le h₁ h₂

/-- Commutative, as an equality. -/
theorem grant_join_comm : ∀ a b : Option Grantable, grantJoin a b = grantJoin b a
  | some a, some b => by simp only [grantJoin, grantable_meet_comm a b]
  | none, none | none, some _ | some _, none => rfl

/-- Associative, as an equality. -/
theorem grant_join_assoc : ∀ a b c : Option Grantable,
    grantJoin (grantJoin a b) c = grantJoin a (grantJoin b c)
  | some a, some b, some c => by simp only [grantJoin, grantable_meet_assoc]
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl

/-- Idempotent, as an equality. -/
theorem grant_join_idem : ∀ a : Option Grantable, grantJoin a a = a
  | some a => by simp only [grantJoin, grantable_meet_idem]
  | none => rfl

/-- A rule's `grantable` limit never loosens: the capped value is at least as strict. -/
theorem grant_le_apply : ∀ (c : GrantCap) (g : Option Grantable), GrantLe g (c.apply g)
  | .forbid, _ => trivial
  | .cap .., none => trivial
  | .cap s u d a, some x => capBy_le x s u d a

/-- The capped value is within the cap; with `GrantCap.forbid` it is absent. -/
theorem cap_le_apply : ∀ (c : GrantCap) (g : Option Grantable), c.le (c.apply g)
  | .forbid, _ => rfl
  | .cap .., none => trivial
  | .cap s u d a, some x => cap_le_capBy x s u d a

/-- Least upper bound for a cap: a value at least as strict as `g` and within the cap is at least
as strict as the capped value. -/
theorem cap_apply_le : ∀ {c : GrantCap} {g h : Option Grantable}, GrantLe g h → c.le h →
    GrantLe (c.apply g) h
  | _, _, none, _, _ => trivial
  | _, none, some _, h, _ => h.elim
  | .forbid, some _, some _, _, hc => by cases hc
  | .cap .., some _, some _, hxy, hc => capBy_le_of hxy hc

/-- A value within a cap stays within it when it gets stricter. -/
theorem cap_le_trans {c : GrantCap} {g h : Option Grantable} (hc : c.le g) (hgh : GrantLe g h) :
    c.le h :=
  cap_le_mono hc hgh

/-- `BoolLe` (false stricter) is reflexive. -/
theorem bool_le_refl (a : Bool) : BoolLe a a := id

/-- `BoolLe` (false stricter) is transitive. -/
theorem bool_le_trans {a b c : Bool} (h₁ : BoolLe a b) (h₂ : BoolLe b c) : BoolLe a c :=
  boolLe_trans h₁ h₂

/-- Upper bound: `a && b` is at least as strict as `a`. -/
theorem bool_le_join_left (a b : Bool) : BoolLe a (a && b) := boolLe_and_left a b

/-- Upper bound: `a && b` is at least as strict as `b`. -/
theorem bool_le_join_right (a b : Bool) : BoolLe b (a && b) := boolLe_and_right a b

/-- Least upper bound for `&&`. -/
theorem bool_join_le {a b c : Bool} (h₁ : BoolLe a c) (h₂ : BoolLe b c) : BoolLe (a && b) c :=
  and_boolLe h₁ h₂

/-- Commutative, as an equality. -/
theorem bool_join_comm (a b : Bool) : (a && b) = (b && a) := Bool.and_comm a b

/-- Associative, as an equality. -/
theorem bool_join_assoc (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := Bool.and_assoc a b c

/-- Idempotent, as an equality. -/
theorem bool_join_idem (a : Bool) : (a && a) = a := Bool.and_self a

/-- `ModeLe` is reflexive. -/
theorem mode_le_refl (a : Option Mode) : ModeLe a a := Nat.le_refl _

/-- `ModeLe` is transitive. -/
theorem mode_le_trans {a b c : Option Mode} (h₁ : ModeLe a b) (h₂ : ModeLe b c) : ModeLe a c :=
  Nat.le_trans h₁ h₂

/-- Upper bound: the mode join is at least as strict as its left argument. -/
theorem mode_le_join_left : ∀ a b : Option Mode, ModeLe a (modeJoin a b) := by
  intro a b; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> decide

/-- Upper bound: the mode join is at least as strict as its right argument. -/
theorem mode_le_join_right : ∀ a b : Option Mode, ModeLe b (modeJoin a b) := by
  intro a b; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> decide

/-- Least upper bound for the mode join. -/
theorem mode_join_le : ∀ {a b c : Option Mode}, ModeLe a c → ModeLe b c → ModeLe (modeJoin a b) c := by
  intro a b c; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rcases c with _ | _ | _ <;>
    decide

/-- Commutative, as an equality. -/
theorem mode_join_comm : ∀ a b : Option Mode, modeJoin a b = modeJoin b a := by
  intro a b; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rfl

/-- Associative, as an equality. -/
theorem mode_join_assoc : ∀ a b c : Option Mode,
    modeJoin (modeJoin a b) c = modeJoin a (modeJoin b c) := by
  intro a b c; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rcases c with _ | _ | _ <;> rfl

/-- Idempotent, as an equality. -/
theorem mode_join_idem : ∀ a : Option Mode, modeJoin a a = a := by
  intro a; rcases a with _ | _ | _ <;> rfl

/-- `ListLe` (inclusion of members) is reflexive. -/
theorem list_le_refl {α : Type} (a : List α) : ListLe a a := fun _ h => h

/-- `ListLe` (inclusion of members) is transitive. -/
theorem list_le_trans {α : Type} {a b c : List α} (h₁ : ListLe a b) (h₂ : ListLe b c) : ListLe a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- Upper bound: the guard union contains the left argument. -/
theorem guard_le_join_left (a b : List String) : ListLe a (guardJoin a b) :=
  fun _ hx => mem_guardJoin.mpr (.inl hx)

/-- Upper bound: the guard union contains the right argument. -/
theorem guard_le_join_right (a b : List String) : ListLe b (guardJoin a b) :=
  fun _ hx => mem_guardJoin.mpr (.inr hx)

/-- Least upper bound for the guard union. -/
theorem guard_join_le {a b c : List String} (h₁ : ListLe a c) (h₂ : ListLe b c) :
    ListLe (guardJoin a b) c :=
  fun x hx => (mem_guardJoin.mp hx).elim (h₁ x) (h₂ x)

/-- The guard union has no duplicates. -/
theorem guard_join_nodup (a b : List String) : (guardJoin a b).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (nodup_listJoin a b)

/-- Commutative, as an equality: the join is sorted and deduplicated. -/
theorem guard_join_comm (a b : List String) : guardJoin a b = guardJoin b a :=
  guardJoin_eq fun _ => Or.comm

/-- Associative, as an equality. -/
theorem guard_join_assoc (a b c : List String) :
    guardJoin (guardJoin a b) c = guardJoin a (guardJoin b c) :=
  guardJoin_eq fun _ => by rw [mem_guardJoin, mem_guardJoin, or_assoc]

/-- Idempotent, as an equality, on the canonical (sorted, deduplicated) form every join returns. -/
theorem guard_join_idem (a b : List String) :
    guardJoin (guardJoin a b) (guardJoin a b) = guardJoin a b :=
  guardJoin_eq fun _ => by rw [mem_guardJoin, or_self]

/-- Upper bound: the flag union contains the left argument. -/
theorem flag_le_join_left (a b : List Flag) : ListLe a (flagJoin a b) :=
  fun _ hx => mem_flagJoin.mpr (.inl hx)

/-- Upper bound: the flag union contains the right argument. -/
theorem flag_le_join_right (a b : List Flag) : ListLe b (flagJoin a b) :=
  fun _ hx => mem_flagJoin.mpr (.inr hx)

/-- Least upper bound for the flag union. -/
theorem flag_join_le {a b c : List Flag} (h₁ : ListLe a c) (h₂ : ListLe b c) :
    ListLe (flagJoin a b) c :=
  fun x hx => (mem_flagJoin.mp hx).elim (h₁ x) (h₂ x)

/-- The flag union has no duplicates. -/
theorem flag_join_nodup (a b : List Flag) : (flagJoin a b).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (nodup_listJoin a b)

/-- Commutative, as an equality: the join is sorted and deduplicated. -/
theorem flag_join_comm (a b : List Flag) : flagJoin a b = flagJoin b a :=
  flagJoin_eq fun _ => Or.comm

/-- Associative, as an equality. -/
theorem flag_join_assoc (a b c : List Flag) :
    flagJoin (flagJoin a b) c = flagJoin a (flagJoin b c) :=
  flagJoin_eq fun _ => by rw [mem_flagJoin, mem_flagJoin, or_assoc]

/-- Idempotent, as an equality, on the canonical (sorted, deduplicated) form every join returns. -/
theorem flag_join_idem (a b : List Flag) :
    flagJoin (flagJoin a b) (flagJoin a b) = flagJoin a b :=
  flagJoin_eq fun _ => by rw [mem_flagJoin, or_self]

namespace Join

theorem filter_map_nodup (f : String → Escalator) (n : String) :
    ∀ l : List String, l.Nodup →
      (l.map fun m => (m, f m)).filter (·.1 == n) = if n ∈ l then [(n, f n)] else []
  | [], _ => rfl
  | m :: l, hl => by
    have ⟨hm, hl'⟩ := List.nodup_cons.mp hl
    have ih := filter_map_nodup f n l hl'
    by_cases h : m = n
    · subst h
      simp only [List.map_cons, List.filter_cons, beq_self_eq_true, ↓reduceIte, ih, hm,
        List.mem_cons, true_or]
    · have : (m == n) = false := by simpa using h
      simp only [List.map_cons, List.filter_cons, this, ih, List.mem_cons]
      by_cases hn : n ∈ l
      · simp [hn]
      · simp [hn, Ne.symm h]

theorem escAt_nil_of (l : List (String × Escalator)) (n : String) (h : n ∉ l.map (·.1)) :
    escAt l n = ⟨.none, true⟩ := by
  have : l.filter (·.1 == n) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx hb
    exact h (List.mem_map.mpr ⟨x, hx, by simpa using hb⟩)
  simp only [escAt, this, List.foldl_nil]

theorem escAt_escJoin (a b : List (String × Escalator)) (n : String) :
    escAt (escJoin a b) n =
      if n ∈ listJoin (a.map (·.1)) (b.map (·.1))
      then (⟨.none, true⟩ : Escalator).join ((escAt a n).join (escAt b n)) else ⟨.none, true⟩ := by
  show ((escJoin a b).filter (·.1 == n)).foldl _ _ = _
  rw [escJoin, filter_map_nodup _ _ _ (nodup_listJoin _ _)]
  split <;> rfl

theorem bot_esc_le (e : Escalator) : (⟨.none, true⟩ : Escalator).le e :=
  ⟨consent_none_le _, fun _ => rfl⟩

theorem escalator_le_refl (e : Escalator) : e.le e := ⟨consent_le_refl _, id⟩

theorem escalator_le_trans {e f g : Escalator} (h₁ : e.le f) (h₂ : f.le g) : e.le g :=
  ⟨consent_le_trans h₁.1 h₂.1, h₁.2 ∘ h₂.2⟩

theorem escalator_le_join_left (e f : Escalator) : e.le (e.join f) :=
  ⟨consent_le_join_left _ _, boolLe_and_left _ _⟩

theorem escalator_le_join_right (e f : Escalator) : f.le (e.join f) :=
  ⟨consent_le_join_right _ _, boolLe_and_right _ _⟩

theorem escalator_join_le {e f g : Escalator} (h₁ : e.le g) (h₂ : f.le g) : (e.join f).le g :=
  ⟨consent_join_le h₁.1 h₂.1, and_boolLe h₁.2 h₂.2⟩

theorem escAt_join_ge (a b : List (String × Escalator)) (n : String) :
    ((escAt a n).join (escAt b n)).le (escAt (escJoin a b) n) := by
  rw [escAt_escJoin]
  split
  · exact escalator_le_join_right _ _
  · rename_i h
    rw [mem_listJoin, not_or] at h
    rw [escAt_nil_of a n h.1, escAt_nil_of b n h.2]
    exact escalator_join_le (escalator_le_refl _) (escalator_le_refl _)

theorem escAt_join_le (a b : List (String × Escalator)) (n : String) :
    (escAt (escJoin a b) n).le ((escAt a n).join (escAt b n)) := by
  rw [escAt_escJoin]
  split
  · exact escalator_join_le (bot_esc_le _) (escalator_le_refl _)
  · exact bot_esc_le _

end Join

open Join

/-- `EscLe` read over every reason: a reason `a` does not name adds nothing there. -/
theorem escLe_iff {a b : List (String × Escalator)} :
    EscLe a b ↔ ∀ n, (escAt a n).le (escAt b n) :=
  ⟨fun h n => if hn : n ∈ a.map (·.1) then h n hn else by
      rw [escAt_nil_of a n hn]; exact bot_esc_le _,
    fun h n _ => h n⟩

/-- `EscLe` is reflexive. -/
theorem esc_le_refl (a : List (String × Escalator)) : EscLe a a := fun _ _ => escalator_le_refl _

/-- `EscLe` is transitive. -/
theorem esc_le_trans {a b c : List (String × Escalator)} (h₁ : EscLe a b) (h₂ : EscLe b c) :
    EscLe a c :=
  escLe_iff.mpr fun n => escalator_le_trans (escLe_iff.mp h₁ n) (escLe_iff.mp h₂ n)

/-- Upper bound: the escalator union is at least as strict as its left argument. -/
theorem esc_le_join_left (a b : List (String × Escalator)) : EscLe a (escJoin a b) :=
  escLe_iff.mpr fun n => escalator_le_trans (escalator_le_join_left _ _) (escAt_join_ge a b n)

/-- Upper bound: the escalator union is at least as strict as its right argument. -/
theorem esc_le_join_right (a b : List (String × Escalator)) : EscLe b (escJoin a b) :=
  escLe_iff.mpr fun n => escalator_le_trans (escalator_le_join_right _ _) (escAt_join_ge a b n)

/-- Least upper bound for the escalator union. -/
theorem esc_join_le {a b c : List (String × Escalator)} (h₁ : EscLe a c) (h₂ : EscLe b c) :
    EscLe (escJoin a b) c :=
  escLe_iff.mpr fun n =>
    escalator_le_trans (escAt_join_le a b n) (escalator_join_le (escLe_iff.mp h₁ n) (escLe_iff.mp h₂ n))

/-- Commutative up to the order's equivalence (`EscLe` both ways): consent groups and reasons
keep their order of first appearance. -/
theorem esc_join_comm (a b : List (String × Escalator)) :
    EscLe (escJoin a b) (escJoin b a) ∧ EscLe (escJoin b a) (escJoin a b) :=
  comm_of esc_le_join_left esc_le_join_right esc_join_le a b

/-- Associative up to the order's equivalence (`EscLe` both ways). -/
theorem esc_join_assoc (a b c : List (String × Escalator)) :
    EscLe (escJoin (escJoin a b) c) (escJoin a (escJoin b c)) ∧
      EscLe (escJoin a (escJoin b c)) (escJoin (escJoin a b) c) :=
  assoc_of (le := EscLe) (j := escJoin) esc_le_trans esc_le_join_left esc_le_join_right
    esc_join_le a b c

/-- Idempotent up to the order's equivalence (`EscLe` both ways). -/
theorem esc_join_idem (a : List (String × Escalator)) :
    EscLe (escJoin a a) a ∧ EscLe a (escJoin a a) :=
  idem_of esc_le_refl esc_le_join_left esc_join_le a

/-- `CostLe` is reflexive. -/
theorem cost_le_refl : ∀ a : Option Cost, CostLe a a
  | none => trivial
  | some _ => ⟨rfl, Nat.le_refl _⟩

/-- `CostLe` is transitive. -/
theorem cost_le_trans : ∀ {a b c : Option Cost}, CostLe a b → CostLe b c → CostLe a c
  | _, _, none, _, _ => trivial
  | _, none, some _, _, h => h.elim
  | none, some _, some _, h, _ => h.elim
  | some _, some _, some _, h₁, h₂ => ⟨h₁.1.trans h₂.1, Nat.le_trans h₂.2 h₁.2⟩

namespace Join

theorem costJoin_same {x y : Cost} (h : x.currency = y.currency) :
    costJoin (some x) (some y) = some ⟨min x.amount y.amount, x.currency⟩ := by
  simp [costJoin, h]

theorem costJoin_diff {x y : Cost} (h : ¬x.currency = y.currency) :
    costJoin (some x) (some y) = none := by
  simp [costJoin, h]

end Join

/-- Upper bound: the threshold join is at least as strict as its left argument. -/
theorem cost_le_join_left : ∀ a b : Option Cost, CostLe a (costJoin a b)
  | some x, some y => by
    by_cases h : x.currency = y.currency
    · rw [costJoin_same h]; exact ⟨rfl, Nat.min_le_left _ _⟩
    · rw [costJoin_diff h]; trivial
  | none, _ | some _, none => trivial

/-- Upper bound: the threshold join is at least as strict as its right argument. -/
theorem cost_le_join_right : ∀ a b : Option Cost, CostLe b (costJoin a b)
  | some x, some y => by
    by_cases h : x.currency = y.currency
    · rw [costJoin_same h]; exact ⟨h.symm, Nat.min_le_right _ _⟩
    · rw [costJoin_diff h]; trivial
  | none, _ | some _, none => trivial

/-- Least upper bound for the threshold join. -/
theorem cost_join_le : ∀ {a b c : Option Cost}, CostLe a c → CostLe b c → CostLe (costJoin a b) c
  | _, _, none, _, _ => trivial
  | none, _, some _, h, _ => h.elim
  | some _, none, some _, _, h => h.elim
  | some _, some _, some _, h₁, h₂ => by
    rw [costJoin_same (h₁.1.trans h₂.1.symm)]
    exact ⟨h₁.1, Nat.le_min.mpr ⟨h₁.2, h₂.2⟩⟩

/-- Commutative up to the order's equivalence (`CostLe` both ways). -/
theorem cost_join_comm (a b : Option Cost) :
    CostLe (costJoin a b) (costJoin b a) ∧ CostLe (costJoin b a) (costJoin a b) :=
  comm_of cost_le_join_left cost_le_join_right cost_join_le a b

/-- Associative up to the order's equivalence (`CostLe` both ways). -/
theorem cost_join_assoc (a b c : Option Cost) :
    CostLe (costJoin (costJoin a b) c) (costJoin a (costJoin b c)) ∧
      CostLe (costJoin a (costJoin b c)) (costJoin (costJoin a b) c) :=
  assoc_of (le := CostLe) (j := costJoin) cost_le_trans cost_le_join_left cost_le_join_right
    cost_join_le a b c

/-- Idempotent up to the order's equivalence (`CostLe` both ways). -/
theorem cost_join_idem (a : Option Cost) :
    CostLe (costJoin a a) a ∧ CostLe a (costJoin a a) :=
  idem_of cost_le_refl cost_le_join_left cost_join_le a

/-- `max_attempts`: fewer is stricter, so `b ≤ a` reads "`b` is at least as strict as `a`" and the
join is `min`. Upper bound on the left. -/
theorem attempts_le_join_left (a b : Nat) : min a b ≤ a := Nat.min_le_left a b

/-- Upper bound on the right. -/
theorem attempts_le_join_right (a b : Nat) : min a b ≤ b := Nat.min_le_right a b

/-- Least upper bound: a count at most both is at most their `min`. -/
theorem attempts_join_le {a b c : Nat} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
  Nat.le_min.mpr ⟨h₁, h₂⟩

/-- Commutative, as an equality. -/
theorem attempts_join_comm (a b : Nat) : min a b = min b a := Nat.min_comm a b

/-- Associative, as an equality. -/
theorem attempts_join_assoc (a b c : Nat) : min (min a b) c = min a (min b c) := Nat.min_assoc a b c

/-- Idempotent, as an equality. -/
theorem attempts_join_idem (a : Nat) : min a a = a := Nat.min_self a

/-- TTLs (`DurLe`, no TTL the least strict, a shorter one stricter) are reflexive. -/
theorem ttl_le_refl (a : Option Nat) : DurLe a a := durLe_refl a

/-- `DurLe` is transitive. -/
theorem ttl_le_trans {a b c : Option Nat} (h₁ : DurLe a b) (h₂ : DurLe b c) : DurLe a c :=
  durLe_trans h₁ h₂

/-- Upper bound: the TTL meet is at least as strict as its left argument. -/
theorem ttl_le_join_left (a b : Option Nat) : DurLe a (durMeet a b) := durLe_meet_left a b

/-- Upper bound: the TTL meet is at least as strict as its right argument. -/
theorem ttl_le_join_right (a b : Option Nat) : DurLe b (durMeet a b) := durLe_meet_right a b

/-- Least upper bound for the TTL meet. -/
theorem ttl_join_le {a b c : Option Nat} (h₁ : DurLe a c) (h₂ : DurLe b c) : DurLe (durMeet a b) c :=
  durMeet_le h₁ h₂

/-- Commutative, as an equality. -/
theorem ttl_join_comm (a b : Option Nat) : durMeet a b = durMeet b a := durMeet_comm a b

/-- Associative, as an equality. -/
theorem ttl_join_assoc (a b c : Option Nat) : durMeet (durMeet a b) c = durMeet a (durMeet b c) :=
  durMeet_assoc a b c

/-- Idempotent, as an equality. -/
theorem ttl_join_idem (a : Option Nat) : durMeet a a = a := durMeet_idem a

/-- `Requirements.le` is reflexive. -/
theorem req_le_refl (a : Requirements) : a.le a :=
  ⟨consent_le_refl _, grant_le_refl _, id, id, id, fun _ h => h, fun _ h => h, Nat.le_refl _,
    cost_le_refl _, esc_le_refl _, Nat.le_refl _, durLe_refl _, durLe_refl _⟩

/-- `Requirements.le` is transitive. -/
theorem req_le_trans {a b c : Requirements} (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  obtain ⟨c₁, g₁, e₁, i₁, r₁, u₁, f₁, m₁, k₁, s₁, n₁, p₁, q₁⟩ := h₁
  obtain ⟨c₂, g₂, e₂, i₂, r₂, u₂, f₂, m₂, k₂, s₂, n₂, p₂, q₂⟩ := h₂
  exact ⟨consent_le_trans c₁ c₂, grant_le_trans g₁ g₂, e₁ ∘ e₂, i₁ ∘ i₂, r₁ ∘ r₂,
    list_le_trans u₁ u₂, list_le_trans f₁ f₂, mode_le_trans m₁ m₂, cost_le_trans k₁ k₂,
    esc_le_trans s₁ s₂, Nat.le_trans n₂ n₁, durLe_trans p₁ p₂, durLe_trans q₁ q₂⟩

/-- Upper bound: `joinStrict a b` is at least as strict as `a`. -/
theorem req_le_joinStrict_left (a b : Requirements) : a.le (a.joinStrict b) :=
  ⟨consent_le_join_left _ _, grant_le_join_left _ _, bool_le_join_left _ _,
    bool_le_join_left _ _, bool_le_join_left _ _, guard_le_join_left _ _, flag_le_join_left _ _,
    mode_le_join_left _ _, cost_le_join_left _ _, esc_le_join_left _ _, Nat.min_le_left _ _,
    durLe_meet_left _ _, durLe_meet_left _ _⟩

/-- Upper bound: `joinStrict a b` is at least as strict as `b`. -/
theorem req_le_joinStrict_right (a b : Requirements) : b.le (a.joinStrict b) :=
  ⟨consent_le_join_right _ _, grant_le_join_right _ _, bool_le_join_right _ _,
    bool_le_join_right _ _, bool_le_join_right _ _, guard_le_join_right _ _,
    flag_le_join_right _ _, mode_le_join_right _ _, cost_le_join_right _ _,
    esc_le_join_right _ _, Nat.min_le_right _ _, durLe_meet_right _ _, durLe_meet_right _ _⟩

/-- Least upper bound: requirements at least as strict as `a` and `b` are at least as strict as
`joinStrict a b`. -/
theorem joinStrict_le {a b c : Requirements} (h₁ : a.le c) (h₂ : b.le c) :
    (a.joinStrict b).le c := by
  obtain ⟨c₁, g₁, e₁, i₁, r₁, u₁, f₁, m₁, k₁, s₁, n₁, p₁, q₁⟩ := h₁
  obtain ⟨c₂, g₂, e₂, i₂, r₂, u₂, f₂, m₂, k₂, s₂, n₂, p₂, q₂⟩ := h₂
  exact ⟨consent_join_le c₁ c₂, grant_join_le g₁ g₂, bool_join_le e₁ e₂, bool_join_le i₁ i₂,
    bool_join_le r₁ r₂, guard_join_le u₁ u₂, flag_join_le f₁ f₂, mode_join_le m₁ m₂,
    cost_join_le k₁ k₂, esc_join_le s₁ s₂, Nat.le_min.mpr ⟨n₁, n₂⟩, durMeet_le p₁ p₂,
    durMeet_le q₁ q₂⟩

/-- Commutative up to the order's equivalence (`Requirements.le` both ways); `permission` and
`meters` are the left argument's, so they differ. -/
theorem joinStrict_comm (a b : Requirements) :
    (a.joinStrict b).le (b.joinStrict a) ∧ (b.joinStrict a).le (a.joinStrict b) :=
  comm_of req_le_joinStrict_left req_le_joinStrict_right joinStrict_le a b

/-- Associative up to the order's equivalence (`Requirements.le` both ways). -/
theorem joinStrict_assoc (a b c : Requirements) :
    ((a.joinStrict b).joinStrict c).le (a.joinStrict (b.joinStrict c)) ∧
      (a.joinStrict (b.joinStrict c)).le ((a.joinStrict b).joinStrict c) :=
  assoc_of (le := Requirements.le) (j := Requirements.joinStrict) req_le_trans
    req_le_joinStrict_left req_le_joinStrict_right joinStrict_le a b c

/-- Idempotent up to the order's equivalence (`Requirements.le` both ways). -/
theorem joinStrict_idem (a : Requirements) : (a.joinStrict a).le a ∧ a.le (a.joinStrict a) :=
  idem_of req_le_refl req_le_joinStrict_left joinStrict_le a

/-- Monotone in both arguments. -/
theorem joinStrict_mono {a a' b b' : Requirements} (ha : a.le a') (hb : b.le b') :
    (a.joinStrict b).le (a'.joinStrict b') :=
  mono_of (le := Requirements.le) (j := Requirements.joinStrict) req_le_trans
    req_le_joinStrict_left req_le_joinStrict_right joinStrict_le ha hb

/-- Requirements at least as strict as everything rule requirements `r` ask stay so when they get
stricter. -/
theorem require_le_trans {r : Require} {a b : Requirements} (h₁ : r.le a) (h₂ : a.le b) : r.le b :=
  ⟨consent_le_trans h₁.1 h₂.1,
    by
      obtain ⟨-, hg, -⟩ := h₁
      cases hr : r.grantable with
      | none => trivial
      | some c =>
        simp only [hr, CapLe] at hg
        exact cap_le_trans hg h₂.2.1,
    h₁.2.2.1 ∘ h₂.2.2.1, h₁.2.2.2.1 ∘ h₂.2.2.2.1, h₁.2.2.2.2.1 ∘ h₂.2.2.2.2.1,
    list_le_trans h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1, list_le_trans h₁.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.1,
    mode_le_trans h₁.2.2.2.2.2.2.2 h₂.2.2.2.2.2.2.2.1⟩

/-- Upper bound: `joinReq a r` is at least as strict as `a`. -/
theorem req_le_joinReq (a : Requirements) (r : Require) : a.le (a.joinReq r) := by
  refine ⟨?_, ?_, bool_le_join_left _ _, bool_le_join_left _ _, bool_le_join_left _ _,
    guard_le_join_left _ _, flag_le_join_left _ _, mode_le_join_left _ _, cost_le_refl _,
    esc_le_refl _, Nat.le_refl _, durLe_refl _, durLe_refl _⟩
  · cases hc : r.consent with
    | none => simp only [Requirements.joinReq, hc]; exact consent_le_refl _
    | some c => simp only [Requirements.joinReq, hc]; exact consent_le_join_left _ _
  · cases hg : r.grantable with
    | none => simp only [Requirements.joinReq, hg]; exact grant_le_refl _
    | some c => simp only [Requirements.joinReq, hg]; exact grant_le_apply _ _

/-- Upper bound: `joinReq a r` is at least as strict as everything `r` requires. -/
theorem require_le_joinReq (a : Requirements) (r : Require) : r.le (a.joinReq r) := by
  refine ⟨?_, ?_, bool_le_join_right _ _, bool_le_join_right _ _, bool_le_join_right _ _,
    guard_le_join_right _ _, flag_le_join_right _ _, mode_le_join_right _ _⟩
  · cases hc : r.consent with
    | none => exact consent_none_le _
    | some c => simp only [Requirements.joinReq, hc, Option.getD]; exact consent_le_join_right _ _
  · cases hg : r.grantable with
    | none => trivial
    | some c => simp only [Requirements.joinReq, hg, CapLe]; exact cap_le_apply _ _

/-- Least upper bound: requirements at least as strict as `a` and as everything `r` requires are
at least as strict as `joinReq a r`. -/
theorem joinReq_le {a c : Requirements} {r : Require} (h₁ : a.le c) (h₂ : r.le c) :
    (a.joinReq r).le c := by
  refine ⟨?_, ?_, bool_join_le h₁.2.2.1 h₂.2.2.1, bool_join_le h₁.2.2.2.1 h₂.2.2.2.1,
    bool_join_le h₁.2.2.2.2.1 h₂.2.2.2.2.1, guard_join_le h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1,
    flag_join_le h₁.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.1, mode_join_le h₁.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2,
    h₁.2.2.2.2.2.2.2.2⟩
  · have hc := h₂.1
    cases hr : r.consent with
    | none => simp only [Requirements.joinReq, hr]; exact h₁.1
    | some d =>
      simp only [hr, Option.getD] at hc
      simp only [Requirements.joinReq, hr]
      exact consent_join_le h₁.1 hc
  · have hg := h₂.2.1
    cases hr : r.grantable with
    | none => simp only [Requirements.joinReq, hr]; exact h₁.2.1
    | some d =>
      simp only [hr, CapLe] at hg
      simp only [Requirements.joinReq, hr]
      exact cap_apply_le h₁.2.1 hg

/-- Monotone: stricter requirements stay stricter after joining the same rule requirements. -/
theorem joinReq_mono {a b : Requirements} (h : a.le b) (r : Require) :
    (a.joinReq r).le (b.joinReq r) :=
  joinReq_le (req_le_trans h (req_le_joinReq b r)) (require_le_joinReq b r)

/-- Rules apply in any order, up to the order's equivalence (`Requirements.le` both ways). -/
theorem joinReq_swap (a : Requirements) (r₁ r₂ : Require) :
    ((a.joinReq r₁).joinReq r₂).le ((a.joinReq r₂).joinReq r₁) ∧
      ((a.joinReq r₂).joinReq r₁).le ((a.joinReq r₁).joinReq r₂) := by
  have h : ∀ r r' : Require, ((a.joinReq r).joinReq r').le ((a.joinReq r').joinReq r) := by
    intro r r'
    refine joinReq_le (joinReq_le ?_ (require_le_joinReq _ _)) ?_
    · exact req_le_trans (req_le_joinReq a r') (req_le_joinReq _ _)
    · exact require_le_trans (require_le_joinReq a r') (req_le_joinReq _ _)
  exact ⟨h r₁ r₂, h r₂ r₁⟩

/-- Applying the same rule requirements twice is the same as once, up to the order's equivalence
(`Requirements.le` both ways). -/
theorem joinReq_idem (a : Requirements) (r : Require) :
    ((a.joinReq r).joinReq r).le (a.joinReq r) ∧ (a.joinReq r).le ((a.joinReq r).joinReq r) :=
  ⟨joinReq_le (req_le_refl _) (require_le_joinReq a r), req_le_joinReq _ _⟩

end Writ.Proofs
