import WritProofs.Meters
import WritProofs.AtMostOnce

namespace Writ.Proofs

open Writ Usage Meters AtMostOnce Basic Calls

/-- Section 8, theorem 8: a call that holds its reservation, Dispatched or Unknown and not
reconciled. -/
def Holds (c : CallRec) : Prop :=
  c.status = .dispatched ∨ (c.status = .unknown ∧ c.reconciled = none)

/-- Section 8, theorem 8's accounting invariant, for this session's entries. -/
structure Accounting (p : Policy) (s : State) : Prop where
  unique : ∀ m k, (ownEntries p s m k).length ≤ 1
  owner : ∀ m en, en ∈ entriesOf p s m → en.meter = m → en.session = s.sessionId →
    ∃ c r, s.calls[en.call]? = some c ∧ 1 ≤ c.attempts ∧ p.action? c.tool = some r ∧ m ∈ r.meters
  held : ∀ k c r m spec, s.calls[k]? = some c → p.action? c.tool = some r → m ∈ r.meters →
    p.meter? m = some spec → 1 ≤ c.attempts → Holds c →
      ∃ en, ownEntries p s m k = [en] ∧ en.committed = false ∧ en.excess = 0 ∧
        en.amount = draw spec c.cost
  settled : ∀ k c m en, s.calls[k]? = some c → en ∈ ownEntries p s m k → ¬ Holds c →
    en.committed = true

variable {p : Policy} {d : String} {s s' s₁ s₂ acc : State} {e : Event} {k k' m m' : String}
  {t a : Nat} {c c' c'' c₁ : CallRec} {l l' l₁ l₂ l₃ : List MeterEntry} {x : MeterEntry}
  {f : List MeterEntry → List MeterEntry} {sc : MeterScope} {spec : MeterSpec}
  {es : List MeterEntry} {a' b' gid tool dg w pr : String} {sc' : GrantScope} {n : Nat}
  {mc cs : Option Cost} {nb ex : Option Nat} {rv : String} {ed : Option Edit}

namespace Accounting

/-- An entry that section 6's pruning at `t` may drop. -/
def Pruned (p : Policy) (t : Nat) (x : MeterEntry) : Prop :=
  x.committed = true ∧ ∃ spec w, p.meter? x.meter = some spec ∧ spec.windowMs = some w ∧
    x.time + w ≤ t ∧ (x.excess = 0 ∨ x.excessAt + w ≤ t)

def Prunes (p : Policy) (t : Nat) (l l' : List MeterEntry) : Prop :=
  ∃ q : MeterEntry → Bool, (∀ x ∈ l, q x = false → Pruned p t x) ∧ l' = l.filter q

theorem Prunes.refl : Prunes p t l l :=
  ⟨fun _ => true, ⟨fun _ _ h => (by cases h), (List.filter_eq_self.mpr fun _ _ => rfl).symm⟩⟩

theorem Prunes.trans (h₁ : Prunes p t l₁ l₂) (h₂ : Prunes p t l₂ l₃) : Prunes p t l₁ l₃ := by
  obtain ⟨q₁, hq₁, rfl⟩ := h₁
  obtain ⟨q₂, hq₂, rfl⟩ := h₂
  refine ⟨fun x => q₂ x && q₁ x, ⟨fun x hx hq => ?_, List.filter_filter⟩⟩
  cases h1 : q₁ x
  · exact hq₁ x hx h1
  · simp only [h1, Bool.and_true] at hq
    exact hq₂ x (List.mem_filter.mpr ⟨hx, h1⟩) hq

theorem Prunes.mem (h : Prunes p t l l') (hx : x ∈ l') : x ∈ l := by
  obtain ⟨q, -, rfl⟩ := h
  exact (List.mem_filter.mp hx).1

theorem Prunes.gone (h : Prunes p t l l') (hx : x ∈ l) (hn : x ∉ l') : Pruned p t x := by
  obtain ⟨q, hq, rfl⟩ := h
  cases hqx : q x
  · exact hq x hx hqx
  · exact absurd (List.mem_filter.mpr ⟨hx, hqx⟩) hn

theorem Prunes.keep (h : Prunes p t l l') (hx : x ∈ l) (hc : x.committed = false) : x ∈ l' :=
  Classical.byContradiction fun hn => by
    have := (h.gone hx hn).1
    rw [hc] at this
    cases this

theorem Prunes.length (h : Prunes p t l l') : l'.length ≤ l.length := by
  obtain ⟨q, -, rfl⟩ := h
  exact List.length_filter_le _ _

theorem Prunes.filter (h : Prunes p t l l') (g : MeterEntry → Bool) :
    Prunes p t (l.filter g) (l'.filter g) := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q, ⟨fun x hx => hq x (List.mem_filter.mp hx).1, ?_⟩⟩
  rw [List.filter_filter, List.filter_filter]
  exact List.filter_congr fun _ _ => Bool.and_comm ..

theorem Prunes.nil (h : Prunes p t [] l) : l = [] := by
  obtain ⟨q, -, rfl⟩ := h
  rfl

theorem Prunes.single (h : Prunes p t [x] l) (hc : x.committed = false) : l = [x] := by
  have hk := h.keep List.mem_cons_self hc
  have hl := h.length
  match l, hk, hl with
  | [y], hk, _ => rw [List.mem_singleton.mp hk]

theorem expired_pruned (hs : p.meter? x.meter = some spec) (h : spec.expired x t = true) :
    Pruned p t x := by
  unfold MeterSpec.expired MeterSpec.inWindow MeterSpec.inWindowAt at h
  cases hw : spec.windowMs with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.isSome_some, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.or_eq_true, beq_iff_eq, Nat.not_lt] at h
    exact ⟨h.1.1, spec, w, hs, hw, by omega, h.2.imp id fun h => by omega⟩

theorem prune_prunes : Prunes p t es (p.prune sc t es) := by
  refine ⟨_, ⟨fun x _ hq => ?_, rfl⟩⟩
  cases hs : p.meter? x.meter with
  | none => simp [hs] at hq
  | some spec =>
    simp only [hs, Option.any_some, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hq
    exact expired_pruned hs hq.2

theorem upd_prunes : Prunes p t (f es) (upd p sc t f es) := by
  unfold upd
  split
  · rename_i h; rw [eq_of_beq h]; exact Prunes.refl
  · exact prune_prunes

theorem own_eq : ownEntries p s m k = (entriesOf p s m).filter (·.isFor m s.sessionId k) :=
  List.filter_congr fun _ _ => isFor_decide.symm

theorem own_update_other
    (hf : ∀ L, (f L).filter (·.isFor m s.sessionId k) = L.filter (·.isFor m s.sessionId k)) :
    Prunes p t (ownEntries p s m k) (ownEntries p (s.updateEntries p m' t f) m k) := by
  rw [own_eq, own_eq, updateEntries_sessionId]
  rcases entriesOf_update (p := p) (s := s) (m' := m') (t := t) (f := f) (m := m) with
    h | ⟨sc, h⟩ <;> rw [h]
  · exact Prunes.refl
  · rw [← hf]; exact upd_prunes.filter _

theorem own_update_self :
    Prunes p t ((f (entriesOf p s m)).filter (·.isFor m s.sessionId k))
      (ownEntries p (s.updateEntries p m t f) m k) := by
  rw [own_eq, updateEntries_sessionId]
  obtain ⟨sc, h⟩ := entriesOf_update_self (p := p) (s := s) (m := m) (t := t) (f := f)
  rw [h]
  exact upd_prunes.filter _

theorem isFor_other {sid : String} (hx : x.isFor m sid k' = true) (hne : m' ≠ m ∨ k' ≠ k) :
    x.isFor m' sid k = false := by
  rw [isFor_iff] at hx
  cases h : x.isFor m' sid k
  · rfl
  · rw [isFor_iff] at h
    rcases hne with hne | hne
    · exact absurd (h.1.symm.trans hx.1) hne
    · exact absurd (hx.2.2.symm.trans h.2.2) hne

theorem own_reserve_other (hne : m' ≠ m ∨ k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (s.reserve p m' k a t) m k') := by
  unfold State.reserve
  refine own_update_other fun L => ?_
  rw [List.filter_append]
  have hx :
      (⟨m', s.sessionId, k, t, a, false, 0, 0⟩ : MeterEntry).isFor m s.sessionId k' = false := by
    rcases hne with h | h <;> simp [MeterEntry.isFor, h, Ne.symm h]
  simp [hx]

theorem own_reserve_self :
    Prunes p t (ownEntries p s m k ++ [⟨m, s.sessionId, k, t, a, false, 0, 0⟩])
      (ownEntries p (s.reserve p m k a t) m k) := by
  have h := own_update_self (p := p) (s := s) (m := m) (t := t) (k := k)
    (f := (· ++ [⟨m, s.sessionId, k, t, a, false, 0, 0⟩]))
  have hx : [(⟨m, s.sessionId, k, t, a, false, 0, 0⟩ : MeterEntry)].filter
      (·.isFor m s.sessionId k) = [⟨m, s.sessionId, k, t, a, false, 0, 0⟩] := by
    simp [MeterEntry.isFor]
  rw [List.filter_append, hx] at h
  rw [own_eq]
  exact h

theorem filter_map_keys {g : MeterEntry → MeterEntry} {sid : String}
    (hg : ∀ x, (g x).meter = x.meter ∧ (g x).session = x.session ∧ (g x).call = x.call)
    (L : List MeterEntry) :
    (L.map g).filter (·.isFor m sid k) = (L.filter (·.isFor m sid k)).map g := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun x _ => ?_
  simp only [Function.comp, MeterEntry.isFor, (hg x).1, (hg x).2.1, (hg x).2.2]

theorem own_map_other {g : MeterEntry → MeterEntry}
    (hg : ∀ x, (g x).meter = x.meter ∧ (g x).session = x.session ∧ (g x).call = x.call)
    (hfix : ∀ x, x.isFor m' s.sessionId k = false → g x = x) (hne : m' ≠ m ∨ k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (s.updateEntries p m' t (List.map g)) m k') := by
  refine own_update_other fun L => ?_
  rw [filter_map_keys hg]
  exact (List.map_congr_left fun x hx => hfix x (isFor_other (List.mem_filter.mp hx).2 hne)).trans
    (List.map_id _)

theorem own_map_self {g : MeterEntry → MeterEntry}
    (hg : ∀ x, (g x).meter = x.meter ∧ (g x).session = x.session ∧ (g x).call = x.call) :
    Prunes p t ((ownEntries p s m k).map g)
      (ownEntries p (s.updateEntries p m t (List.map g)) m k) := by
  have h := own_update_self (p := p) (s := s) (m := m) (t := t) (k := k) (f := List.map g)
  rw [filter_map_keys hg] at h
  rw [own_eq]
  exact h

theorem own_isFor (hx : x ∈ ownEntries p s m k) : x.isFor m s.sessionId k = true := by
  rw [own_eq] at hx
  exact (List.mem_filter.mp hx).2

theorem own_retime_other (hne : m' ≠ m ∨ k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (s.retime p m' k t) m k') := by
  unfold State.retime
  exact own_map_other (fun x => by split <;> exact ⟨rfl, rfl, rfl⟩) (fun x hx => by simp [hx]) hne

theorem own_retime_self :
    Prunes p t ((ownEntries p s m k).map fun x => { x with time := t })
      (ownEntries p (s.retime p m k t) m k) := by
  unfold State.retime
  have h := own_map_self (p := p) (s := s) (m := m) (t := t) (k := k)
    (g := fun x => if x.isFor m s.sessionId k then { x with time := t } else x)
    (fun x => by split <;> exact ⟨rfl, rfl, rfl⟩)
  have he : (ownEntries p s m k).map (fun x => if x.isFor m s.sessionId k then
      { x with time := t } else x) = (ownEntries p s m k).map fun x => { x with time := t } :=
    List.map_congr_left fun x hx => by simp [own_isFor hx]
  rw [he] at h
  exact h

theorem own_commit_other (hne : m' ≠ m ∨ k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (s.commit p m' k a t) m k') := by
  unfold State.commit
  refine own_map_other (fun x => ?_) (fun x hx => by simp [hx]) hne
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- What a commit leaves of a list of own entries: no more of them, each committed and no larger
than one before it. -/
def Closes (l l' : List MeterEntry) : Prop :=
  l'.length ≤ l.length ∧ ∀ y ∈ l', y.committed = true ∧ ∃ x ∈ l, y.amount ≤ x.amount

theorem own_commit_self :
    ∃ l'', Closes (ownEntries p s m k) l'' ∧
      Prunes p t l'' (ownEntries p (s.commit p m k a t) m k) := by
  unfold State.commit
  refine ⟨_, ⟨Nat.le_of_eq (List.length_map _), fun y hy => ?_⟩, own_map_self (fun x => by
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl⟩)⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simp only [own_isFor hx, Bool.not_true, Bool.false_eq_true, ite_false]
  split
  · exact ⟨rfl, x, hx, Nat.le_refl _⟩
  · rename_i hlt
    exact ⟨rfl, x, hx, show a ≤ x.amount by omega⟩

def commitAs (a t : Nat) (x : MeterEntry) : MeterEntry :=
  if a > x.amount then { x with excess := a - x.amount, excessAt := t, committed := true }
  else { x with amount := a, committed := true }

/-- What committing `x` at `t` leaves: committed, same meter and time, no larger, and an overrun's
excess dated at `t`. -/
def Commits (t : Nat) (x y : MeterEntry) : Prop :=
  y.committed = true ∧ y.meter = x.meter ∧ y.time = x.time ∧ y.amount ≤ x.amount ∧
    ((y.excess = x.excess ∧ y.excessAt = x.excessAt) ∨ (y.amount = x.amount ∧ y.excessAt = t))

theorem commitAs_commits : Commits t x (commitAs a t x) := by
  unfold commitAs
  split
  · exact ⟨rfl, rfl, rfl, Nat.le_refl _, .inr ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, show a ≤ x.amount by omega, .inl ⟨rfl, rfl⟩⟩

theorem own_commit_map :
    Prunes p t ((ownEntries p s m k).map (commitAs a t))
      (ownEntries p (s.commit p m k a t) m k) := by
  unfold State.commit
  have h := own_map_self (p := p) (s := s) (m := m) (t := t) (k := k)
    (g := fun x => if !x.isFor m s.sessionId k then x else if a > x.amount then
      { x with excess := a - x.amount, excessAt := t, committed := true }
      else { x with amount := a, committed := true })
    (fun x => by
      repeat' split
      all_goals exact ⟨rfl, rfl, rfl⟩)
  have he : (ownEntries p s m k).map (fun x => if !x.isFor m s.sessionId k then x
      else if a > x.amount then { x with excess := a - x.amount, excessAt := t, committed := true }
      else { x with amount := a, committed := true }) = (ownEntries p s m k).map (commitAs a t) :=
    List.map_congr_left fun x hx => by simp [own_isFor hx, commitAs]
  rw [he] at h
  exact h

theorem own_release_other (hne : m' ≠ m ∨ k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (s.release p m' k t) m k') := by
  unfold State.release
  refine own_update_other fun L => ?_
  rw [List.filter_filter]
  refine List.filter_congr fun x _ => ?_
  cases hx : x.isFor m s.sessionId k'
  · rfl
  · simp [isFor_other hx hne]

theorem own_release_self : ownEntries p (s.release p m k t) m k = [] := by
  unfold State.release
  have h := own_update_self (p := p) (s := s) (m := m) (t := t) (k := k)
    (f := (·.filter (!·.isFor m s.sessionId k)))
  rw [List.filter_filter] at h
  refine Prunes.nil ((List.filter_eq_nil_iff.mpr fun x _ => ?_) ▸ h)
  cases x.isFor m s.sessionId k <;> simp

theorem fold_prunes {β : Type _} (V : β → List MeterEntry) {g : β → String → β}
    {ms : List String} (hg : ∀ b m', m' ∈ ms → Prunes p t (V b) (V (g b m'))) (b₀ : β) :
    Prunes p t (V b₀) (V (ms.foldl g b₀)) :=
  foldl_invariant_mem (fun b => Prunes p t (V b₀) (V b)) ms
    (fun b m' hm h => h.trans (hg b m' hm)) b₀ Prunes.refl

theorem fold_focus {β : Type _} (V : β → List MeterEntry) {g : β → String → β}
    {R : List MeterEntry → List MeterEntry → Prop} {pre post : List String}
    (hpre : ∀ b m', m' ∈ pre → Prunes p t (V b) (V (g b m')))
    (hpost : ∀ b m', m' ∈ post → Prunes p t (V b) (V (g b m')))
    (hm : ∀ b, ∃ l, R (V b) l ∧ Prunes p t l (V (g b m))) (b₀ : β) :
    ∃ l₁ l₂, Prunes p t (V b₀) l₁ ∧ R l₁ l₂ ∧
      Prunes p t l₂ (V ((pre ++ m :: post).foldl g b₀)) := by
  rw [List.foldl_append, List.foldl_cons]
  obtain ⟨l, hR, hl⟩ := hm (pre.foldl g b₀)
  exact ⟨_, l, fold_prunes V hpre b₀, hR, hl.trans (fold_prunes V hpost _)⟩

/-- The parts of a state the invariant reads. -/
structure Same (s s' : State) : Prop where
  calls : s'.calls = s.calls
  sid : s'.sessionId = s.sessionId
  sm : s'.sessionMeters = s.sessionMeters
  led : s'.ledger.entries = s.ledger.entries
  started : s'.started = s.started

theorem Same.refl : Same s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans (h : Same s s₁) (h' : Same s₁ s₂) : Same s s₂ :=
  ⟨h'.calls.trans h.calls, h'.sid.trans h.sid, h'.sm.trans h.sm, h'.led.trans h.led,
   h'.started.trans h.started⟩

theorem entriesOf_same (h : Same s s') : entriesOf p s' m = entriesOf p s m := by
  unfold entriesOf; rw [h.sm, h.led]

theorem own_same (h : Same s s') : ownEntries p s' m k = ownEntries p s m k := by
  unfold ownEntries; rw [entriesOf_same h, h.sid]

theorem releaseGrant_same : Same s (s.releaseGrant k) := by
  unfold State.releaseGrant; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem consumeGrant_same : Same s (s.consumeGrant k) := by
  unfold State.consumeGrant; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem recordFailure_same {tool : String} : Same s (s.recordFailure p tool) := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem recordSuccess_same {tool : String} : Same s (s.recordSuccess tool) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem updateEntries_keeps :
    (s.updateEntries p m t f).calls = s.calls ∧ (s.updateEntries p m t f).started = s.started := by
  unfold State.updateEntries; split <;> exact ⟨rfl, rfl⟩

theorem own_claim_first {r : Requirements} {key : String} :
    ownEntries p (claim p s t k c r false key) m k' =
      ownEntries p (r.meters.foldl (fun s m' => s.reserve p m' k (p.callAmount m' c.cost) t)
        (s.consumeGrant k)) m k' := rfl

theorem own_claim_retry {r : Requirements} {key : String} :
    ownEntries p (claim p s t k c r true key) m k' =
      ownEntries p ((s.staleMeters p t r.meters k).foldl (fun s m' => s.retime p m' k t) s) m k' :=
  rfl

theorem claim_other {r : Requirements} {key : String} {retry : Bool} (hk : k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (claim p s t k c r retry key) m k') := by
  cases retry
  · rw [own_claim_first]
    have h := fold_prunes (fun b => ownEntries p b m k')
      (g := fun s m' => s.reserve p m' k (p.callAmount m' c.cost) t) (ms := r.meters)
      (fun _ _ _ => own_reserve_other (.inr hk)) (s.consumeGrant k)
    rwa [own_same consumeGrant_same] at h
  · rw [own_claim_retry]
    exact fold_prunes (fun b => ownEntries p b m k') (fun _ _ _ => own_retime_other (.inr hk)) s

theorem claim_started {r : Requirements} {key : String} {retry : Bool} :
    (claim p s t k c r retry key).started = s.started := by
  unfold claim
  dsimp only
  split
  · exact foldl_invariant (fun b : State => b.started = s.started)
      (fun b _ h => updateEntries_keeps.2.trans h) _ s rfl
  · exact foldl_invariant (fun b : State => b.started = s.started)
      (fun b _ h => updateEntries_keeps.2.trans h) _ (s.consumeGrant k) consumeGrant_same.started

theorem claim_first_self {r : Requirements} {key : String} (hnd : r.meters.Nodup)
    (hm : m ∈ r.meters) (h0 : ownEntries p s m k = []) :
    ∃ x, ownEntries p (claim p s t k c r false key) m k = [x] ∧ x.committed = false ∧
      x.excess = 0 ∧ x.amount = p.callAmount m c.cost ∧ x.time = t := by
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup hnd hm
  rw [own_claim_first, hsplit]
  obtain ⟨l₁, l₂, h₁, ⟨x, rfl, hx₁, hx₂, hx₃, hx₄⟩, h₃⟩ := fold_focus (fun b => ownEntries p b m k)
    (t := t) (g := fun s m' => s.reserve p m' k (p.callAmount m' c.cost) t)
    (R := fun l l' => ∃ x, l' = l ++ [x] ∧ x.committed = false ∧ x.excess = 0 ∧
      x.amount = p.callAmount m c.cost ∧ x.time = t)
    (fun _ m' hm' => own_reserve_other (.inl fun he => hpre (he ▸ hm')))
    (fun _ m' hm' => own_reserve_other (.inl fun he => hpost (he ▸ hm')))
    (fun _ => ⟨_, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, own_reserve_self⟩) (s.consumeGrant k)
  rw [own_same consumeGrant_same, h0] at h₁
  rw [h₁.nil, List.nil_append] at h₃
  exact ⟨x, h₃.single hx₁, hx₁, hx₂, hx₃, hx₄⟩

theorem claim_first_out {r : Requirements} {key : String} (hm : m ∉ r.meters) :
    Prunes p t (ownEntries p s m k) (ownEntries p (claim p s t k c r false key) m k) := by
  rw [own_claim_first]
  have h := fold_prunes (fun b => ownEntries p b m k)
    (g := fun s m' => s.reserve p m' k (p.callAmount m' c.cost) t) (ms := r.meters)
    (fun _ m' hm' => own_reserve_other (.inl fun he => hm (he ▸ hm'))) (s.consumeGrant k)
  rwa [own_same consumeGrant_same] at h

theorem claim_retry_in {r : Requirements} {key : String}
    (hnd : (s.staleMeters p t r.meters k).Nodup) (hm : m ∈ s.staleMeters p t r.meters k) :
    ∃ l₁, Prunes p t (ownEntries p s m k) l₁ ∧
      Prunes p t (l₁.map fun x => { x with time := t })
        (ownEntries p (claim p s t k c r true key) m k) := by
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup hnd hm
  rw [own_claim_retry, hsplit]
  obtain ⟨l₁, l₂, h₁, rfl, h₃⟩ := fold_focus (fun b => ownEntries p b m k)
    (t := t) (g := fun s m' => s.retime p m' k t)
    (R := fun l l' => l' = l.map fun x => { x with time := t })
    (fun _ m' hm' => own_retime_other (.inl fun he => hpre (he ▸ hm')))
    (fun _ m' hm' => own_retime_other (.inl fun he => hpost (he ▸ hm')))
    (fun _ => ⟨_, rfl, own_retime_self⟩) s
  exact ⟨l₁, h₁, h₃⟩

theorem claim_retry_out {r : Requirements} {key : String}
    (hm : m ∉ s.staleMeters p t r.meters k) :
    Prunes p t (ownEntries p s m k) (ownEntries p (claim p s t k c r true key) m k) := by
  rw [own_claim_retry]
  exact fold_prunes (fun b => ownEntries p b m k)
    (fun _ m' hm' => own_retime_other (.inl fun he => hm (he ▸ hm'))) s

variable {ms : List String} {o : Outcome} {act : Option Nat} {ne : Bool}

theorem settle_other (hk : k' ≠ k) :
    Prunes p t (ownEntries p s m k') (ownEntries p (s.settle p ms k o act ne t).1 m k') := by
  unfold State.settle
  dsimp only
  refine fold_prunes (fun b : State × List String => ownEntries p b.1 m k') (fun b m' _ => ?_)
    (s, [])
  obtain ⟨acc, over⟩ := b
  dsimp only
  split
  · exact own_release_other (.inr hk)
  · split <;> exact own_commit_other (.inr hk)

theorem settle_in (hnd : ms.Nodup) (hm : m ∈ ms) :
    ∃ l₁ l₂, Prunes p t (ownEntries p s m k) l₁ ∧ Closes l₁ l₂ ∧
      Prunes p t l₂ (ownEntries p (s.settle p ms k o act ne t).1 m k) := by
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup hnd hm
  unfold State.settle
  dsimp only
  rw [hsplit]
  refine fold_focus (fun b : State × List String => ownEntries p b.1 m k) (R := Closes)
    (fun b m' hm' => ?_) (fun b m' hm' => ?_) (fun b => ?_) (s, [])
  all_goals obtain ⟨acc, over⟩ := b
  all_goals dsimp only
  all_goals split
  · exact own_release_other (.inl fun he => hpre (he ▸ hm'))
  · split <;> exact own_commit_other (.inl fun he => hpre (he ▸ hm'))
  · exact own_release_other (.inl fun he => hpost (he ▸ hm'))
  · split <;> exact own_commit_other (.inl fun he => hpost (he ▸ hm'))
  · refine ⟨[], ⟨Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩, ?_⟩
    rw [own_release_self]
    exact Prunes.refl
  · split <;> exact own_commit_self

theorem settle_out (hm : m ∉ ms) :
    Prunes p t (ownEntries p s m k) (ownEntries p (s.settle p ms k o act ne t).1 m k) := by
  unfold State.settle
  dsimp only
  refine fold_prunes (fun b : State × List String => ownEntries p b.1 m k) (fun b m' hm' => ?_)
    (s, [])
  obtain ⟨acc, over⟩ := b
  dsimp only
  split
  · exact own_release_other (.inl fun he => hm (he ▸ hm'))
  · split <;> exact own_commit_other (.inl fun he => hm (he ▸ hm'))

theorem Prunes.single_or (h : Prunes p t [x] l) : l = [x] ∨ (l = [] ∧ Pruned p t x) := by
  obtain ⟨q, hq, rfl⟩ := h
  cases hqx : q x
  · exact .inr ⟨by simp [hqx], hq x List.mem_cons_self hqx⟩
  · exact .inl (by simp [hqx])

theorem fold_commit {β : Type _} (V : β → List MeterEntry) {g : β → String → β}
    {pre post : List String} {en : MeterEntry}
    (hpre : ∀ b m', m' ∈ pre → Prunes p t (V b) (V (g b m')))
    (hpost : ∀ b m', m' ∈ post → Prunes p t (V b) (V (g b m')))
    (hm : ∀ b, ∃ l, (∀ x, V b = [x] → ∃ y, l = [y] ∧ Commits t x y) ∧ Prunes p t l (V (g b m)))
    (b₀ : β) (h1 : V b₀ = [en]) (hu : en.committed = false) :
    ∃ y, Commits t en y ∧ (V ((pre ++ m :: post).foldl g b₀) = [y] ∨
      (V ((pre ++ m :: post).foldl g b₀) = [] ∧ Pruned p t y)) := by
  obtain ⟨l₁, l₂, h₁, hR, h₃⟩ := fold_focus V
    (R := fun l l' => ∀ x, l = [x] → ∃ y, l' = [y] ∧ Commits t x y) hpre hpost hm b₀
  rw [h1] at h₁
  obtain ⟨y, rfl, hy⟩ := hR en (h₁.single hu)
  exact ⟨y, hy, h₃.single_or⟩

/-- A settle that does not release commits a single uncommitted own entry, which then stays unless
pruning drops it at `t`. -/
theorem settle_commit {en : MeterEntry} (hnd : ms.Nodup) (hm : m ∈ ms)
    (hrel : (ne || o == .declined) = false) (h1 : ownEntries p s m k = [en])
    (hu : en.committed = false) :
    ∃ y, Commits t en y ∧ (ownEntries p (s.settle p ms k o act ne t).1 m k = [y] ∨
      (ownEntries p (s.settle p ms k o act ne t).1 m k = [] ∧ Pruned p t y)) := by
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup hnd hm
  unfold State.settle
  dsimp only
  rw [hsplit]
  refine fold_commit (fun b : State × List String => ownEntries p b.1 m k)
    (fun b m' hm' => ?_) (fun b m' hm' => ?_) (fun b => ?_) (s, []) h1 hu
  all_goals obtain ⟨acc, over⟩ := b
  all_goals dsimp only
  all_goals split
  · exact own_release_other (.inl fun he => hpre (he ▸ hm'))
  · split <;> exact own_commit_other (.inl fun he => hpre (he ▸ hm'))
  · exact own_release_other (.inl fun he => hpost (he ▸ hm'))
  · split <;> exact own_commit_other (.inl fun he => hpost (he ▸ hm'))
  · rename_i hr; rw [hrel] at hr; cases hr
  · split
    all_goals exact ⟨_, fun x hx => ⟨_, by rw [hx]; rfl, commitAs_commits⟩, own_commit_map⟩

theorem settle_started : (s.settle p ms k o act ne t).1.started = s.started := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.started = s.started) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact updateEntries_keeps.2.trans h
  · split <;> exact updateEntries_keeps.2.trans h

/-- What every stored call record satisfies: only an Unknown call is reconciled, a call not yet
dispatched has no attempt, and a Dispatched or Unknown one has one. -/
def Ok (c : CallRec) : Prop :=
  (c.reconciled ≠ none → c.status = .unknown) ∧ (Open c.status → c.attempts = 0) ∧
    (c.status = .dispatched ∨ c.status = .unknown → 1 ≤ c.attempts)

/-- What a step other than a claim, a settle or a session start may do to a call record. -/
structure Rec (c c' : CallRec) : Prop where
  tool : c'.tool = c.tool
  attempts : c'.attempts = c.attempts
  reconciled : c'.reconciled = c.reconciled
  ok : Ok c → Ok c'
  holds : Ok c → 1 ≤ c.attempts → (Holds c' ↔ Holds c)
  cost : Ok c → 1 ≤ c.attempts → c'.cost = c.cost

theorem Rec.refl : Rec c c := ⟨rfl, rfl, rfl, id, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem Rec.trans (h : Rec c c') (h' : Rec c' c'') : Rec c c'' where
  tool := h'.tool.trans h.tool
  attempts := h'.attempts.trans h.attempts
  reconciled := h'.reconciled.trans h.reconciled
  ok o := h'.ok (h.ok o)
  holds o ha := (h'.holds (h.ok o) (by rw [h.attempts]; exact ha)).trans (h.holds o ha)
  cost o ha := (h'.cost (h.ok o) (by rw [h.attempts]; exact ha)).trans (h.cost o ha)

theorem open_ne {st : CallStatus} (h : Open st) : st ≠ .dispatched ∧ st ≠ .unknown := by
  rcases h with h | h <;> rw [h] <;> exact ⟨nofun, nofun⟩

theorem Rec.opened (ho : Open c.status) (ht : c'.tool = c.tool) (ha : c'.attempts = c.attempts)
    (hr : c'.reconciled = c.reconciled) (hs : c'.status ≠ .dispatched ∧ c'.status ≠ .unknown) :
    Rec c c' where
  tool := ht
  attempts := ha
  reconciled := hr
  ok o := ⟨fun hn => absurd (o.1 (hr ▸ hn)) (open_ne ho).2, fun _ => ha.trans (o.2.1 ho),
    fun h => (h.elim hs.1 hs.2).elim⟩
  holds o h := absurd (o.2.1 ho) (by omega)
  cost o h := absurd (o.2.1 ho) (by omega)

theorem Rec.unknown (hd : c.status = .dispatched) : Rec c { c with status := .unknown } where
  tool := rfl
  attempts := rfl
  reconciled := rfl
  ok o := ⟨fun _ => rfl, fun h => (by rcases h with h | h <;> cases h), fun _ => o.2.2 (.inl hd)⟩
  holds o _ := by
    have hr : c.reconciled = none := Classical.byContradiction fun hn => by
      rw [o.1 hn] at hd; cases hd
    exact ⟨fun _ => .inl hd, fun _ => .inr ⟨rfl, hr⟩⟩
  cost _ _ := rfl

def RecStep : Option CallRec → Option CallRec → Prop
  | some c, some c' => Rec c c'
  | some _, none => False
  | none, some c' => c'.attempts = 0 ∧ Ok c'
  | none, none => True

theorem RecStep.refl : ∀ o, RecStep o o
  | some _ => Rec.refl
  | none => trivial

theorem RecStep.trans : ∀ {a b c : Option CallRec}, RecStep a b → RecStep b c → RecStep a c
  | some _, some _, some _, h₁, h₂ => Rec.trans h₁ h₂
  | none, some _, some _, ⟨ha, ho⟩, h₂ => ⟨h₂.attempts.trans ha, h₂.ok ho⟩
  | some _, none, _, h₁, _ => h₁.elim
  | _, some _, none, _, h₂ => h₂.elim
  | none, none, _, _, h₂ => h₂

/-- A step that touches no meter entry and changes call records only as `Rec` allows. -/
structure Plain (s s' : State) : Prop where
  calls : ∀ k : String, RecStep s.calls[k]? s'.calls[k]?
  sid : s'.sessionId = s.sessionId
  sm : s'.sessionMeters = s.sessionMeters
  led : s'.ledger.entries = s.ledger.entries
  started : s'.started = s.started

theorem Plain.refl : Plain s s := ⟨fun _ => RecStep.refl _, rfl, rfl, rfl, rfl⟩

theorem Plain.trans (h : Plain s s₁) (h' : Plain s₁ s₂) : Plain s s₂ :=
  ⟨fun k => (h.calls k).trans (h'.calls k), h'.sid.trans h.sid, h'.sm.trans h.sm,
   h'.led.trans h.led, h'.started.trans h.started⟩

theorem Same.plain (h : Same s s') : Plain s s' :=
  ⟨fun k => by rw [h.calls]; exact RecStep.refl _, h.sid, h.sm, h.led, h.started⟩

theorem Plain.same (h : Plain s s₁) (h' : Same s₁ s₂) : Plain s s₂ := h.trans h'.plain

theorem Plain.ofInsert (hk : s.calls[k]? = some c) (hr : Rec c c')
    (he : s'.calls = s.calls.insert k c') (h₁ : s'.sessionId = s.sessionId)
    (h₂ : s'.sessionMeters = s.sessionMeters) (h₃ : s'.ledger.entries = s.ledger.entries)
    (h₄ : s'.started = s.started) : Plain s s' := by
  refine ⟨fun a => ?_, h₁, h₂, h₃, h₄⟩
  rw [he, Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i heq
    cases Std.LawfulEqCmp.eq_of_compare heq
    rw [hk]
    exact hr
  · exact RecStep.refl _

theorem Plain.ofNew (hk : s.calls[k]? = none) (ha : c'.attempts = 0) (ho : Ok c')
    (he : s'.calls = s.calls.insert k c') (h₁ : s'.sessionId = s.sessionId)
    (h₂ : s'.sessionMeters = s.sessionMeters) (h₃ : s'.ledger.entries = s.ledger.entries)
    (h₄ : s'.started = s.started) : Plain s s' := by
  refine ⟨fun a => ?_, h₁, h₂, h₃, h₄⟩
  rw [he, Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i heq
    cases Std.LawfulEqCmp.eq_of_compare heq
    rw [hk]
    exact ⟨ha, ho⟩
  · exact RecStep.refl _

theorem Plain.endCall {st : CallStatus} (h : Plain s acc) (hk : s.calls[k]? = some c)
    (ho : Open c.status) (hst : st ≠ .dispatched ∧ st ≠ .unknown) : Plain s (acc.endCall k st) := by
  unfold State.endCall
  dsimp only
  have h₁ := h.same (releaseGrant_same (k := k))
  refine ⟨fun a => ?_, h₁.sid, h₁.sm, h₁.led, h₁.started⟩
  rw [Std.ExtTreeMap.getElem?_modify]
  split
  · rename_i heq
    cases Std.LawfulEqCmp.eq_of_compare heq
    have hc := h₁.calls k
    rw [hk] at hc ⊢
    cases hb : (acc.releaseGrant k).calls[k]? with
    | none => rw [hb] at hc; exact hc.elim
    | some b =>
      rw [hb] at hc
      exact Rec.opened ho hc.tool hc.attempts hc.reconciled hst
  · exact h₁.calls a

theorem cancelPending_plain : Plain s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant_mem (Plain s) _ ?_ _ Plain.refl
  intro acc ⟨k, c⟩ hm ha
  have hk := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm
  dsimp only
  split <;> rename_i hs
  · exact ha.endCall hk (.inl hs) ⟨nofun, nofun⟩
  · exact ha.endCall hk (.inr hs) ⟨nofun, nofun⟩
  · exact ha

theorem interrupt_plain : Plain s s.interrupt := by
  unfold State.interrupt
  dsimp only
  have h := cancelPending_plain (s := s)
  refine ⟨fun a => ?_, h.sid, h.sm, h.led, h.started⟩
  rw [Std.ExtTreeMap.getElem?_map]
  have ha := h.calls a
  cases hb : (cancelPending s).calls[a]? with
  | none => rw [hb] at ha; exact ha
  | some b =>
    rw [hb] at ha
    refine RecStep.trans (b := some b) ha ?_
    show Rec b _
    dsimp only
    split
    · exact Rec.unknown ‹_›
    · exact Rec.refl

local macro "plain" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Plain.refl
      | exact Same.plain ⟨rfl, rfl, rfl, rfl, rfl⟩
      | exact cancelPending_plain.same ⟨rfl, rfl, rfl, rfl, rfl⟩
      | exact interrupt_plain.same ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem handleSessionEnd_plain : Plain s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; plain

theorem handleTurnStart_plain {u : Bool} : Plain s (handleTurnStart s u).1 := by
  unfold handleTurnStart; plain

theorem handleTurnEnd_plain : Plain s (handleTurnEnd s).1 := by
  unfold handleTurnEnd; plain

theorem handleStepStart_plain : Plain s (handleStepStart p s).1 := by
  unfold handleStepStart; plain

theorem handleApproverAttest_plain {i : ApproverInfo} :
    Plain s (handleApproverAttest s a' i).1 := by
  unfold handleApproverAttest; plain

theorem handlePermissionRevoke_plain : Plain s (handlePermissionRevoke s a').1 := by
  unfold handlePermissionRevoke; plain

theorem handleGrantCreate_plain {dgo : Option String} :
    Plain s (handleGrantCreate p s t gid a' tool dgo sc' n mc nb ex rv).1 := by
  unfold handleGrantCreate; plain

theorem handleGrantRevoke_plain : Plain s (handleGrantRevoke s gid).1 := by
  unfold handleGrantRevoke; plain

theorem handleReset_plain : Plain s (handleReset s).1 := by
  unfold handleReset; plain

theorem handleKill_plain : Plain s (handleKill p s).1 := by
  unfold handleKill; plain

theorem handlePermissionAdd_plain : Plain s (handlePermissionAdd p s a' b').1 := by
  unfold handlePermissionAdd; plain

theorem handleEscalationAck_plain {n : Nat} : Plain s (handleEscalationAck p s a' n).1 := by
  unfold handleEscalationAck; plain

theorem handleCancel_plain : Plain s (handleCancel s k).1 := by
  unfold handleCancel
  split
  · exact Plain.refl
  · rename_i rc hrc
    split <;> rename_i hst
    · exact Plain.refl.endCall (get?_some hrc) (.inl hst) ⟨nofun, nofun⟩
    · exact Plain.refl.endCall (get?_some hrc) (.inr hst) ⟨nofun, nofun⟩
    · exact Plain.refl

theorem callCheck_open {rid : RequestId} {rc : CallRec} (h : callCheck s k rid = .ok rc) :
    s.calls[k]? = some rc ∧ Open rc.status := by
  unfold callCheck at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hrc hst _
       exact ⟨get?_some hrc, .inl (Classical.not_not.mp hst)⟩)

theorem vetoCheck_open {rid : RequestId} {rc : CallRec} (h : vetoCheck p s k rid a' = .ok rc) :
    s.calls[k]? = some rc ∧ Open rc.status := by
  unfold vetoCheck at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hrc hst _ _
       refine ⟨get?_some hrc, ?_⟩
       simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at hst
       exact hst.imp id (·.1))

theorem handleReject_plain {rid : RequestId} : Plain s (handleReject p s k rid a').1 := by
  unfold handleReject
  split
  · exact Plain.refl
  · rename_i rc hv
    obtain ⟨hk, ho⟩ := vetoCheck_open hv
    exact (Plain.refl.endCall (st := .rejected) hk ho ⟨nofun, nofun⟩).same ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem handleApprovalExpire_plain {rid : RequestId} :
    Plain s (handleApprovalExpire s k rid).1 := by
  unfold handleApprovalExpire
  split
  · exact Plain.refl
  · rename_i rc hv
    obtain ⟨hk, ho⟩ := callCheck_open hv
    exact Plain.refl.endCall (st := .expired) hk ho ⟨nofun, nofun⟩

theorem applyApprove_plain {rc : CallRec} {res : State × Verdict} (hk : s.calls[k]? = some rc)
    (ho : Open rc.status) (ha : applyApprove p s t k rc w pr dg cs ed = .ok res) :
    Plain s res.1 := by
  unfold applyApprove at ha
  repeat' (first | (dsimp only at ha) | split at ha)
  all_goals first
    | cases ha; done
    | (cases ha
       rename_i rc' hn _
       have hf : rc'.tool = rc.tool ∧ rc'.attempts = rc.attempts ∧ rc'.reconciled = rc.reconciled ∧
           rc'.status = rc.status := by
         revert hn
         repeat' split
         all_goals (intro hn; cases hn <;> exact ⟨rfl, rfl, rfl, rfl⟩)
       refine Plain.ofInsert hk ?_ rfl rfl rfl rfl rfl
       first
         | exact .opened ho hf.1 hf.2.1 hf.2.2.1 (hf.2.2.2 ▸ open_ne ho)
         | exact .opened ho hf.1 hf.2.1 hf.2.2.1 ⟨nofun, nofun⟩)

theorem handleApprove_plain {rid : RequestId} :
    Plain s (handleApprove p s t k rid w dg cs ed).1 := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact Plain.refl
    | (rename_i hck _ _ ha
       exact applyApprove_plain (awaitingCheck_open hck).1 (awaitingCheck_open hck).2 ha)

theorem Disposition.status_ne (x : Disposition) :
    x.status ≠ .dispatched ∧ x.status ≠ .unknown := by
  cases x <;> exact ⟨nofun, nofun⟩

theorem handlePropose_plain {tool : String} {gs xs : List (String × Bool)} :
    Plain s (handlePropose p s t k tool dg cs gs xs).1 := by
  unfold handlePropose
  split
  · repeat' (first | (dsimp only) | split)
    all_goals exact Plain.refl
  · rename_i hk
    split
    split
    · exact Same.plain ⟨rfl, rfl, rfl, rfl, rfl⟩
    · dsimp only
      refine Plain.ofNew (get?_none hk) rfl ⟨fun h => absurd rfl h, fun _ => rfl, fun h => ?_⟩
        rfl rfl rfl rfl rfl
      exact (h.elim (Disposition.status_ne _).1 (Disposition.status_ne _).2).elim

theorem handleOutcomeUnknown_plain : Plain s (handleOutcomeUnknown p s k).1 := by
  unfold handleOutcomeUnknown
  split
  · exact Plain.refl
  · rename_i rc hrc
    split
    · exact Plain.refl
    · rename_i hd
      dsimp only
      exact Plain.same (s₁ := withStatus s k rc .unknown)
        (Plain.ofInsert (get?_some hrc) (Rec.unknown (Classical.not_not.mp hd)) rfl rfl rfl rfl rfl)
        recordFailure_same

theorem handleDispatch_plain {n : Nat} {g : List (String × Bool)} {key : String}
    (h : (handleDispatch p s t k n dg cs g key).2.claimed = false) :
    Plain s (handleDispatch p s t k n dg cs g key).1 := by
  rcases Dispatch.handle_unclaimed h with he | ⟨c, st, hk, ha, hst, he⟩ <;> rw [he]
  · exact Plain.refl
  · exact Plain.refl.endCall hk (.inr ha)
      (by rcases hst with rfl | ⟨_, rfl⟩ <;> exact ⟨nofun, nofun⟩)

/-- A `result` or `reconcile` that settles call `k`: its record stops holding the reservation and
its meters are settled. -/
def SettleStep (p : Policy) (s : State) (t : Nat) (s' : State) : Prop :=
  ∃ k c c' o act ne, s.calls[k]? = some c ∧ Holds c ∧ ¬Holds c' ∧ c'.tool = c.tool ∧
    c'.attempts = c.attempts ∧ (Ok c → Ok c') ∧
    Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).1 s'

theorem handleResult_kind {o : Outcome} {act : Option Nat} {ne : Bool} :
    Plain s (handleResult p s t k o act ne).1 ∨
      SettleStep p s t (handleResult p s t k o act ne).1 := by
  unfold handleResult
  split
  · exact .inl Plain.refl
  · rename_i rc hrc
    split
    · exact .inl Plain.refl
    · rename_i hd
      have hd' : rc.status = .dispatched := Classical.not_not.mp hd
      refine .inr ⟨k, rc, { rc with status := o.status }, o, act, ne, get?_some hrc, .inl hd', ?_,
        rfl, rfl, fun hok => ⟨fun hn => absurd (hok.1 hn) (by rw [hd']; nofun), fun ho => ?_,
          fun h => ?_⟩, ?_⟩
      · cases o <;> simp [Holds, Outcome.status]
      · cases o <;> simp [Open, Outcome.status] at ho
      · cases o <;> simp [Outcome.status] at h
      · repeat' (first | (dsimp only) | split)
        all_goals first | exact recordFailure_same | exact recordSuccess_same | exact Same.refl

theorem handleReconcile_kind {o : Outcome} {act : Option Nat} {ne : Bool} :
    Plain s (handleReconcile p s t k o act ne).1 ∨
      SettleStep p s t (handleReconcile p s t k o act ne).1 := by
  unfold handleReconcile
  split
  · exact .inl Plain.refl
  · rename_i rc hrc
    split
    · exact .inl Plain.refl
    · rename_i hu
      split
      · exact .inl Plain.refl
      · rename_i hn
        have hu' : rc.status = .unknown := Classical.not_not.mp hu
        have hn' : rc.reconciled = none := by simpa using hn
        refine .inr ⟨k, rc, { rc with reconciled := some o }, o, act, ne, get?_some hrc,
          .inr ⟨hu', hn'⟩, ?_, rfl, rfl,
          fun hok => ⟨fun _ => hu', fun ho => absurd hu' (open_ne ho).2,
            fun _ => hok.2.2 (.inr hu')⟩, ?_⟩
        · simp [Holds, hu']
        · repeat' (first | (dsimp only) | split)
          all_goals first | exact recordFailure_same | exact Same.refl

theorem handleResult_own {o : Outcome} {act : Option Nat} {ne : Bool}
    (hc : s.calls[k]? = some c) (ha : (handleResult p s t k o act ne).2.accepted = true) :
    ∃ c', Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne
      t).1 (handleResult p s t k o act ne).1 := by
  unfold handleResult at ha ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?, hc] at ha ⊢
  dsimp only at ha ⊢
  split at ha
  · cases ha
  · rename_i hd
    simp only [hd, ↓reduceIte]
    refine ⟨{ c with status := o.status }, ?_⟩
    repeat' (first | (dsimp only) | split)
    all_goals first | exact recordFailure_same | exact recordSuccess_same | exact Same.refl

theorem handleReconcile_own {o : Outcome} {act : Option Nat} {ne : Bool}
    (hc : s.calls[k]? = some c) (ha : (handleReconcile p s t k o act ne).2.accepted = true) :
    ∃ c', Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne
      t).1 (handleReconcile p s t k o act ne).1 := by
  unfold handleReconcile at ha ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?, hc] at ha ⊢
  dsimp only at ha ⊢
  split at ha
  · cases ha
  · rename_i hu
    split at ha
    · cases ha
    · rename_i hn
      simp only [hu, hn, ↓reduceIte]
      refine ⟨{ c with reconciled := some o }, ?_⟩
      repeat' (first | (dsimp only) | split)
      all_goals first | exact recordFailure_same | exact Same.refl | (exfalso; simp_all)

/-- The shapes of an accepted step other than a claim, as the invariant's proof needs them. -/
def Kind (p : Policy) (s : State) (e : Event) (s' : State) : Prop :=
  Plain s s' ∨ SettleStep p s e.time s' ∨
    (∃ l, e.body = .ledgerSync l ∧ s' = (handleLedgerSync s l).1) ∨
    ∃ i pd r ps as l, e.body = .sessionStart i pd r ps as l ∧
      s' = (handleSessionStart s i pd r ps as l).1

theorem stepHandle_kind (hcl : (stepHandle p s e).2.claimed = false) :
    Kind p s e (stepHandle p s e).1 := by
  revert hcl
  unfold Kind stepHandle
  split <;> rename_i hb <;> intro hcl
  all_goals first
    | with_reducible exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, hb, rfl⟩))
    | with_reducible exact Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))
    | with_reducible exact handleResult_kind.elim Or.inl fun h => Or.inr (Or.inl h)
    | with_reducible exact handleReconcile_kind.elim Or.inl fun h => Or.inr (Or.inl h)
    | with_reducible exact Or.inl (handleDispatch_plain hcl)
    | with_reducible exact Or.inl handleSessionEnd_plain
    | with_reducible exact Or.inl handleTurnStart_plain
    | with_reducible exact Or.inl handleTurnEnd_plain
    | with_reducible exact Or.inl handleStepStart_plain
    | with_reducible exact Or.inl handleApproverAttest_plain
    | with_reducible exact Or.inl handlePermissionRevoke_plain
    | with_reducible exact Or.inl handlePropose_plain
    | with_reducible exact Or.inl handleApprove_plain
    | with_reducible exact Or.inl handleReject_plain
    | with_reducible exact Or.inl handleApprovalExpire_plain
    | with_reducible exact Or.inl handleGrantCreate_plain
    | with_reducible exact Or.inl handleGrantRevoke_plain
    | with_reducible exact Or.inl handleOutcomeUnknown_plain
    | with_reducible exact Or.inl handleCancel_plain
    | with_reducible exact Or.inl handleReset_plain
    | with_reducible exact Or.inl handleKill_plain
    | with_reducible exact Or.inl handlePermissionAdd_plain
    | with_reducible exact Or.inl handleEscalationAck_plain

/-- `Accounting`, with what its proof by induction needs besides. -/
structure Inv (p : Policy) (s : State) : Prop where
  unique : ∀ m k, (ownEntries p s m k).length ≤ 1
  owner : ∀ m k en, en ∈ ownEntries p s m k →
    ∃ c r, s.calls[k]? = some c ∧ 1 ≤ c.attempts ∧ p.action? c.tool = some r ∧ m ∈ r.meters
  held : ∀ (k : String) (c : CallRec) (r : Requirements) (m : String),
    s.calls[k]? = some c → p.action? c.tool = some r → m ∈ r.meters → 1 ≤ c.attempts → Holds c →
      ∃ en, ownEntries p s m k = [en] ∧ en.committed = false ∧ en.excess = 0 ∧
        en.amount = p.callAmount m c.cost
  settled : ∀ (k : String) (c : CallRec) (m : String) (en : MeterEntry), s.calls[k]? = some c →
    en ∈ ownEntries p s m k → ¬ Holds c → en.committed = true
  live : ∀ (k : String) (c : CallRec) (m : String) (en : MeterEntry), s.calls[k]? = some c →
    en ∈ ownEntries p s m k → Holds c → en.committed = false
  perCall : ∀ (k : String) (c : CallRec) (m : String) (en : MeterEntry) (spec : MeterSpec)
    (mx : Nat), s.calls[k]? = some c → p.modeOf c.tool = .enforce → en ∈ ownEntries p s m k →
      p.meter? m = some spec → spec.maxPerCall = some mx → en.amount ≤ mx
  recs : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → Ok c
  empty : s.started = false →
    s.sessionMeters = [] ∧ s.ledger.entries = [] ∧ ∀ k : String, s.calls[k]? = none

/-- What a step that neither claims nor settles a call may do to that call's own entries on a
meter: drop some of them, never an uncommitted one. -/
def Sub (l l' : List MeterEntry) : Prop :=
  (∀ x ∈ l', x ∈ l) ∧ l'.length ≤ l.length ∧ ∀ x ∈ l, x.committed = false → x ∈ l'

theorem Sub.refl : Sub l l := ⟨fun _ h => h, Nat.le_refl _, fun _ h _ => h⟩

theorem Prunes.sub (h : Prunes p t l l') : Sub l l' :=
  ⟨fun _ hx => h.mem hx, h.length, fun _ hx hc => h.keep hx hc⟩

theorem one_of (hu : l.length ≤ 1) (hx : x ∈ l) : l = [x] := by
  match l, hu, hx with
  | [y], _, hx => rw [List.mem_singleton.mp hx]

theorem Sub.single (h : Sub [x] l) (hc : x.committed = false) : l = [x] :=
  one_of h.2.1 (h.2.2 x List.mem_cons_self hc)

theorem own_plain (h : Plain s s') : ownEntries p s' m k = ownEntries p s m k := by
  unfold ownEntries entriesOf; rw [h.sid, h.sm, h.led]

theorem Inv.transfer (h : Inv p s) (hst : s'.started = true)
    (hc : ∀ k : String, RecStep s.calls[k]? s'.calls[k]?)
    (ho : ∀ m k, Sub (ownEntries p s m k) (ownEntries p s' m k)) : Inv p s' where
  unique m k := Nat.le_trans (ho m k).2.1 (h.unique m k)
  owner m k en hen := by
    obtain ⟨c, r, hk, ha, hr, hm⟩ := h.owner m k en ((ho m k).1 en hen)
    have hs := hc k
    rw [hk] at hs
    cases hk' : s'.calls[k]? with
    | none => rw [hk'] at hs; exact hs.elim
    | some c' =>
      rw [hk'] at hs
      exact ⟨c', r, rfl, by rw [hs.attempts]; exact ha, by rw [hs.tool]; exact hr, hm⟩
  held k c' r m hk' hr hm ha hH := by
    have hst := hc k
    rw [hk'] at hst
    cases hk : s.calls[k]? with
    | none => rw [hk] at hst; have := hst.1; omega
    | some c =>
      rw [hk] at hst
      have ok := h.recs k c hk
      have ha' : 1 ≤ c.attempts := by rw [← hst.attempts]; exact ha
      obtain ⟨en, he, h1, h2, h3⟩ := h.held k c r m hk (by rw [← hst.tool]; exact hr) hm
        ha' ((hst.holds ok ha').mp hH)
      refine ⟨en, ?_, h1, h2, by rw [hst.cost ok ha']; exact h3⟩
      have := ho m k
      rw [he] at this
      exact this.single h1
  settled k c' m en hk' hen hn := by
    obtain ⟨c, r, hk, ha, -, -⟩ := h.owner m k en ((ho m k).1 en hen)
    have hst := hc k
    rw [hk, hk'] at hst
    exact h.settled k c m en hk ((ho m k).1 en hen) fun hH =>
      hn ((hst.holds (h.recs k c hk) ha).mpr hH)
  live k c' m en hk' hen hH := by
    obtain ⟨c, r, hk, ha, -, -⟩ := h.owner m k en ((ho m k).1 en hen)
    have hst := hc k
    rw [hk, hk'] at hst
    exact h.live k c m en hk ((ho m k).1 en hen) ((hst.holds (h.recs k c hk) ha).mp hH)
  perCall k c' m en spec mx hk' hmode hen hs hx := by
    obtain ⟨c, r, hk, -, -, -⟩ := h.owner m k en ((ho m k).1 en hen)
    have hst := hc k
    rw [hk, hk'] at hst
    exact h.perCall k c m en spec mx hk (by rw [← hst.tool]; exact hmode) ((ho m k).1 en hen) hs hx
  recs k c' hk' := by
    have hst := hc k
    rw [hk'] at hst
    cases hk : s.calls[k]? with
    | none => rw [hk] at hst; exact hst.2
    | some c => rw [hk] at hst; exact hst.ok (h.recs k c hk)
  empty hf := by rw [hst] at hf; cases hf

theorem Inv.plain (h : Inv p s) (hs : s.started = true) (hp : Plain s s') : Inv p s' :=
  h.transfer (hp.started.trans hs) hp.calls fun _ _ => by rw [own_plain hp]; exact Sub.refl

theorem Inv.same (h : Inv p s) (hs : Same s s') : Inv p s' := by
  have ho : ∀ m k, ownEntries p s' m k = ownEntries p s m k := fun _ _ => own_same hs
  have hc := hs.calls
  refine ⟨fun m k => ?_, fun m k en hen => ?_, fun k c r m hk => ?_,
    fun k c m en hk => ?_, fun k c m en hk => ?_, fun k c m en spec mx hk => ?_,
    fun k c hk => ?_, fun hf => ?_⟩
  all_goals (try rw [hc] at hk)
  all_goals (try rw [ho])
  · exact h.unique m k
  · rw [ho] at hen; rw [hc]; exact h.owner m k en hen
  · exact h.held k c r m hk
  · exact h.settled k c m en hk
  · exact h.live k c m en hk
  · exact h.perCall k c m en spec mx hk
  · exact h.recs k c hk
  · rw [hs.started] at hf
    obtain ⟨h1, h2, h3⟩ := h.empty hf
    exact ⟨hs.sm.trans h1, hs.led.trans h2, fun k => by rw [hc]; exact h3 k⟩

theorem Inv.vacuous (hc : ∀ k : String, s.calls[k]? = none) (ho : ∀ m k, ownEntries p s m k = [])
    (he : s.started = false → s.sessionMeters = [] ∧ s.ledger.entries = []) : Inv p s where
  unique m k := by rw [ho]; exact Nat.zero_le _
  owner m k en hen := by rw [ho] at hen; cases hen
  held k c r m hk := by rw [hc] at hk; cases hk
  settled k c m en hk := by rw [hc] at hk; cases hk
  live k c m en hk := by rw [hc] at hk; cases hk
  perCall k c m en spec mx hk := by rw [hc] at hk; cases hk
  recs k c hk := by rw [hc] at hk; cases hk
  empty hf := ⟨(he hf).1, (he hf).2, hc⟩

theorem Inv.initial : Inv p (State.initial d) :=
  .vacuous (fun _ => by simp [State.initial])
    (fun m k => by unfold ownEntries entriesOf; split <;> rfl) fun _ => ⟨rfl, rfl⟩

theorem Inv.start {i pd rq : String} {ps : List String} {as : List (String × ApproverInfo)}
    {l : Ledger} (h : Inv p s) (hs : s.started = false) :
    Inv p (handleSessionStart s i pd rq ps as l).1 := by
  obtain ⟨hsm, -, hc⟩ := h.empty hs
  unfold handleSessionStart
  split
  · exact h
  · split
    · exact h
    · rename_i hno
      refine .vacuous hc (fun m k => ?_) (fun hf => by cases hf)
      unfold ownEntries entriesOf
      split
      · refine List.filter_eq_nil_iff.mpr fun en hen hp => hno (List.any_eq_true.mpr ⟨en, hen, ?_⟩)
        simp only [decide_eq_true_eq] at hp
        simp [hp.2.1]
      · exact (by rw [hsm]; rfl)

theorem len_of_count (hB : l.length ≤ 1) (hc : ∀ x, l'.count x ≤ l.count x) :
    l'.length ≤ l.length := by
  match l, hB with
  | [], _ =>
    cases l' with
    | nil => exact Nat.le_refl _
    | cons y l' =>
      have := hc y
      simp at this
  | [y], _ =>
    have hall : ∀ x ∈ l', y = x := fun x hx => by
      have h1 := hc x
      have h2 : 0 < l'.count x := List.count_pos_iff.mpr hx
      rw [List.count_singleton] at h1
      split at h1
      · exact eq_of_beq ‹_›
      · omega
    have := hc y
    rw [List.count_eq_length.mpr hall, List.count_singleton] at this
    simpa using this

theorem sync_sub {L L' : List MeterEntry} {sid : String}
    (hu : (L.filter (·.isFor m sid k)).length ≤ 1)
    (hcount : ∀ x ∈ L'.filter (·.session == sid),
      (L'.filter (·.session == sid)).count x ≤ (L.filter (·.session == sid)).count x)
    (hcomm : ∀ x ∈ (L.filter (·.session == sid)).filter
      (!(L'.filter (·.session == sid)).contains ·), x.committed = true) :
    Sub (L.filter (·.isFor m sid k)) (L'.filter (·.isFor m sid k)) := by
  have hf : ∀ L₀ : List MeterEntry, L₀.filter (·.isFor m sid k) =
      (L₀.filter (·.session == sid)).filter (·.isFor m sid k) := fun L₀ => by
    rw [List.filter_filter]
    refine List.filter_congr fun x _ => ?_
    cases hx : x.isFor m sid k
    · rfl
    · simp [(isFor_iff.mp hx).2.1]
  have hcnt : ∀ x,
      (L'.filter (·.isFor m sid k)).count x ≤ (L.filter (·.isFor m sid k)).count x := by
    intro x
    rw [hf L, hf L']
    cases hP : x.isFor m sid k
    · rw [List.count_eq_zero.mpr fun hx => by rw [(List.mem_filter.mp hx).2] at hP; cases hP]
      exact Nat.zero_le _
    · rw [List.count_filter (p := fun y => y.isFor m sid k) (a := x) hP,
        List.count_filter (p := fun y => y.isFor m sid k) (a := x) hP]
      by_cases hx : x ∈ L'.filter (·.session == sid)
      · exact hcount x hx
      · rw [List.count_eq_zero.mpr hx]; exact Nat.zero_le _
  refine ⟨fun x hx => ?_, len_of_count hu hcnt, fun x hx hc => ?_⟩
  · have := Nat.lt_of_lt_of_le (List.count_pos_iff.mpr hx) (hcnt x)
    exact List.count_pos_iff.mp this
  · rw [hf L] at hx
    obtain ⟨hxm, hxk⟩ := List.mem_filter.mp hx
    rw [hf L']
    refine List.mem_filter.mpr ⟨?_, hxk⟩
    refine Classical.byContradiction fun hn => ?_
    have := hcomm x (List.mem_filter.mpr ⟨hxm, by
      cases hb : (L'.filter (·.session == sid)).contains x
      · rfl
      · exact absurd (List.contains_iff_mem.mp hb) hn⟩)
    rw [hc] at this
    cases this

theorem Inv.sync {l : Ledger} (h : Inv p s) (hs : s.started = true) :
    Inv p (handleLedgerSync s l).1 := by
  unfold handleLedgerSync
  dsimp only
  split
  · exact h
  · rename_i hok
    simp only [Bool.or_eq_true, not_or] at hok
    obtain ⟨⟨-, hfit⟩, -⟩ := hok
    simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at hfit
    obtain ⟨hcount, hcomm⟩ := hfit
    have hp :
        Plain s (if (l.tombstone && !s.ledger.tombstone) = true then cancelPending s else s) := by
      split
      · exact cancelPending_plain
      · exact Plain.refl
    refine h.transfer (hp.started.trans hs) hp.calls fun m k => ?_
    have hown := h.unique m k
    rw [own_eq] at hown ⊢
    rw [own_eq]
    unfold entriesOf at hown ⊢
    dsimp only
    rw [hp.sid]
    split <;> rename_i hP
    · simp only [hP, ↓reduceIte] at hown
      exact sync_sub hown (fun x hx => by simpa using hcount x hx) fun x hx => by
        simpa using hcomm x hx
    · rw [hp.sm]
      exact Sub.refl

/-- The invariant after a step that changes only call `k` and its own entries, and the other
calls' own entries only as `Sub` allows. -/
theorem Inv.focus (h : Inv p s) (hst : s'.started = true) (hcalls : s'.calls = s.calls.insert k c₁)
    (hother : ∀ m k', k' ≠ k → Sub (ownEntries p s m k') (ownEntries p s' m k')) (hok : Ok c₁)
    (hu : ∀ m, (ownEntries p s' m k).length ≤ 1)
    (how : ∀ m en, en ∈ ownEntries p s' m k →
      1 ≤ c₁.attempts ∧ ∃ r, p.action? c₁.tool = some r ∧ m ∈ r.meters)
    (hh : ∀ r m, p.action? c₁.tool = some r → m ∈ r.meters → 1 ≤ c₁.attempts → Holds c₁ →
      ∃ en, ownEntries p s' m k = [en] ∧ en.committed = false ∧ en.excess = 0 ∧
        en.amount = p.callAmount m c₁.cost)
    (hs : ∀ m en, en ∈ ownEntries p s' m k → ¬Holds c₁ → en.committed = true)
    (hl : ∀ m en, en ∈ ownEntries p s' m k → Holds c₁ → en.committed = false)
    (hpc : ∀ m en spec mx, p.modeOf c₁.tool = .enforce → en ∈ ownEntries p s' m k →
      p.meter? m = some spec → spec.maxPerCall = some mx → en.amount ≤ mx) : Inv p s' := by
  have hself : s'.calls[k]? = some c₁ := by rw [hcalls, Std.ExtTreeMap.getElem?_insert_self]
  have hne : ∀ k', k' ≠ k → s'.calls[k']? = s.calls[k']? := fun k' hk => by
    rw [hcalls, insert_ne hk]
  refine ⟨fun m k' => ?_, fun m k' en hen => ?_, fun k' c r m hk' => ?_,
    fun k' c m en hk' hen => ?_, fun k' c m en hk' hen => ?_,
    fun k' c m en spec mx hk' hmode hen => ?_, fun k' c hk' => ?_, fun hf => ?_⟩
  all_goals (try (by_cases hk : k' = k))
  all_goals (try (subst hk))
  all_goals (try (rw [hself] at hk'; cases hk'))
  all_goals (try (rw [hne k' hk] at hk'))
  · exact hu m
  · exact Nat.le_trans (hother m k' hk).2.1 (h.unique m k')
  · obtain ⟨h1, r, h2, h3⟩ := how m en hen
    exact ⟨c₁, r, hself, h1, h2, h3⟩
  · obtain ⟨c, r, hc, h1, h2, h3⟩ := h.owner m k' en ((hother m k' hk).1 en hen)
    exact ⟨c, r, by rw [hne k' hk]; exact hc, h1, h2, h3⟩
  · exact hh r m
  · intro hr hm ha hH
    obtain ⟨en, he, h1, h2, h3⟩ := h.held k' c r m hk' hr hm ha hH
    have := hother m k' hk
    rw [he] at this
    exact ⟨en, this.single h1, h1, h2, h3⟩
  · exact hs m en hen
  · exact h.settled k' c m en hk' ((hother m k' hk).1 en hen)
  · exact hl m en hen
  · exact h.live k' c m en hk' ((hother m k' hk).1 en hen)
  · exact hpc m en spec mx hmode hen
  · exact h.perCall k' c m en spec mx hk' hmode ((hother m k' hk).1 en hen)
  · exact hok
  · exact h.recs k' c hk'
  · rw [hst] at hf; cases hf

theorem action_of_mem {tool : String} (hm : m ∈ ((p.action? tool).getD {}).meters) :
    p.action? tool = some ((p.action? tool).getD {}) := by
  cases h : p.action? tool with
  | none => rw [h] at hm; cases hm
  | some r => rfl

theorem meters_nodup (hwf : p.WF) {tool : String} : ((p.action? tool).getD {}).meters.Nodup := by
  cases h : p.action? tool with
  | none => exact List.nodup_nil
  | some r => exact WF.meters_nodup hwf h

theorem Inv.claimed (hwf : p.WF) (hr : Reachable p d s) (h : Inv p s)
    (hcl : (step p s e).2.claimed = true) : Inv p (step p s e).1 := by
  obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hr hcl
  obtain ⟨hen, c, hc, ⟨hst, hretry, -, -, -, -⟩, hmode⟩ := (dispatch_claimed_iff he).mp hcl
  have hstarted : s.started = true := by
    rcases hen.1 with h | h
    · exact h
    · rw [he] at h; cases h
  rw [claim_post hcl he hc]
  refine Inv.same
    (s := Writ.claim p s e.time k c ((p.action? c.tool).getD {}) (c.status == .unknown) key)
    ?_ ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hok := h.recs k c hc
  have hnd := meters_nodup hwf (p := p) (tool := c.tool)
  obtain ⟨hcalls, -, -⟩ := claim_state (p := p) (s := s) (t := e.time) (k := k) (rc := c)
    (r := (p.action? c.tool).getD {}) (retry := c.status == .unknown) (key := key)
  have hok₁ : Ok
      { c with status := .dispatched, attempts := c.attempts + 1, idempotencyKey := some key } := by
    refine ⟨fun hn => ?_, fun ho => absurd ho (by simp [Open]), fun _ => Nat.le_add_left _ _⟩
    rcases hst with hst | hst
    · exact absurd (hok.1 hn) (by rw [hst]; nofun)
    · exact absurd (hretry hst).1 hn
  rcases hst with hst | hst
  · have hret : (c.status == .unknown) = false := by rw [hst]; rfl
    rw [hret] at hcalls ⊢
    have h0 : c.attempts = 0 := hok.2.1 (.inr hst)
    have hnone : ∀ m, ownEntries p s m k = [] := fun m =>
      List.eq_nil_iff_forall_not_mem.mpr fun en hen => by
        obtain ⟨c', r', hc', ha, -⟩ := h.owner m k en hen
        rw [hc] at hc'
        cases hc'
        omega
    have hout : ∀ m, m ∉ ((p.action? c.tool).getD {}).meters →
        ownEntries p (Writ.claim p s e.time k c ((p.action? c.tool).getD {}) false key) m k = [] :=
      fun m hm => by
        have := claim_first_out (p := p) (s := s) (t := e.time) (k := k) (c := c) (key := key) hm
        rw [hnone] at this
        exact this.nil
    refine h.focus (claim_started.trans hstarted) hcalls (fun m k' hk' => (claim_other hk').sub)
      hok₁ (fun m => ?_) (fun m en hen => ?_) (fun r m hra hm _ _ => ?_)
      (fun _ _ _ hn => absurd (.inl rfl) hn) (fun m en hen _ => ?_)
      (fun m en spec mx hm' hen hs hx => ?_)
    · by_cases hm : m ∈ ((p.action? c.tool).getD {}).meters
      · obtain ⟨x, hx, -⟩ := claim_first_self (t := e.time) (key := key) hnd hm (hnone m)
        rw [hx]; exact Nat.le_refl _
      · rw [hout m hm]; exact Nat.zero_le _
    · by_cases hm : m ∈ ((p.action? c.tool).getD {}).meters
      · exact ⟨Nat.le_add_left _ _, _, action_of_mem hm, hm⟩
      · rw [hout m hm] at hen; cases hen
    · have hR : (p.action? c.tool).getD {} = r := by rw [hra]; rfl
      have hm' : m ∈ ((p.action? c.tool).getD {}).meters := by rw [hR]; exact hm
      obtain ⟨x, hx, h1, h2, h3, -⟩ := claim_first_self (t := e.time) (key := key) hnd hm' (hnone m)
      exact ⟨x, hx, h1, h2, h3⟩
    · by_cases hm : m ∈ ((p.action? c.tool).getD {}).meters
      · obtain ⟨x, hx, h1, -⟩ := claim_first_self (t := e.time) (key := key) hnd hm (hnone m)
        rw [hx, List.mem_singleton] at hen
        rw [hen]; exact h1
      · rw [hout m hm] at hen; cases hen
    · by_cases hm : m ∈ ((p.action? c.tool).getD {}).meters
      · obtain ⟨x, hxe, -, -, h3, -⟩ := claim_first_self (t := e.time) (key := key) hnd hm (hnone m)
        rw [hxe, List.mem_singleton] at hen
        rw [hen, h3, callAmount_eq hs]
        obtain ⟨-, -, -, hmet⟩ := (hmode hm').2
        obtain ⟨spec', hs', hshape, -⟩ := hmet m hm fun hu => absurd hu (by rw [hst]; nofun)
        rw [hs] at hs'
        cases hs'
        exact shape_per_call hwf hs hx hshape
      · rw [hout m hm] at hen; cases hen
  · have hret : (c.status == .unknown) = true := by rw [hst]; rfl
    rw [hret] at hcalls ⊢
    have hH : Holds c := .inr ⟨hst, (hretry hst).1⟩
    have ha1 : 1 ≤ c.attempts := hok.2.2 (.inr hst)
    have hnd' : (s.staleMeters p e.time ((p.action? c.tool).getD {}).meters k).Nodup := by
      unfold State.staleMeters
      exact hnd.filter _
    have hrel : ∀ m,
        (∀ en ∈ ownEntries p (Writ.claim p s e.time k c ((p.action? c.tool).getD {}) true key) m k,
          ∃ y ∈ ownEntries p s m k, en.committed = y.committed ∧ en.amount = y.amount ∧
            en.excess = y.excess) ∧
        (ownEntries p (Writ.claim p s e.time k c ((p.action? c.tool).getD {}) true key) m k).length
          ≤ (ownEntries p s m k).length ∧
        ∀ y, ownEntries p s m k = [y] → y.committed = false → ∃ y',
          ownEntries p (Writ.claim p s e.time k c ((p.action? c.tool).getD {}) true key) m k =
            [y'] ∧ y'.committed = false ∧ y'.amount = y.amount ∧ y'.excess = y.excess := by
      intro m
      by_cases hm : m ∈ s.staleMeters p e.time ((p.action? c.tool).getD {}).meters k
      · obtain ⟨l₁, h₁, h₂⟩ := claim_retry_in (c := c) (key := key) hnd' hm
        refine ⟨fun en hen => ?_, ?_, fun y hy hy0 => ?_⟩
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (h₂.mem hen)
          exact ⟨y, h₁.mem hy, rfl, rfl, rfl⟩
        · exact Nat.le_trans h₂.length (by rw [List.length_map]; exact h₁.length)
        · rw [hy] at h₁
          rw [h₁.single hy0, List.map_singleton] at h₂
          exact ⟨_, h₂.single hy0, hy0, rfl, rfl⟩
      · have h₁ := claim_retry_out (c := c) (key := key) hm
        refine ⟨fun en hen => ⟨en, h₁.mem hen, rfl, rfl, rfl⟩, h₁.length, fun y hy hy0 => ?_⟩
        rw [hy] at h₁
        exact ⟨y, h₁.single hy0, hy0, rfl, rfl⟩
    refine h.focus (claim_started.trans hstarted) hcalls (fun m k' hk' => (claim_other hk').sub)
      hok₁ (fun m => Nat.le_trans (hrel m).2.1 (h.unique m k)) (fun m en hen => ?_)
      (fun r m hra hm _ _ => ?_) (fun _ _ _ hn => absurd (.inl rfl) hn)
      (fun m en hen _ => ?_) (fun m en spec mx hm' hen hs hx => ?_)
    · obtain ⟨y, hy, -⟩ := (hrel m).1 en hen
      obtain ⟨c', r, hc', -, hra, hm⟩ := h.owner m k y hy
      rw [hc] at hc'
      cases hc'
      exact ⟨Nat.le_add_left _ _, r, hra, hm⟩
    · obtain ⟨y, hy, h1, h2, h3⟩ := h.held k c r m hc hra hm ha1 hH
      obtain ⟨y', hy', h1', h2', h3'⟩ := (hrel m).2.2 y hy h1
      exact ⟨y', hy', h1', by rw [h3', h2], by rw [h2', h3]⟩
    · obtain ⟨y, hy, hc1, -⟩ := (hrel m).1 en hen
      rw [hc1]
      exact h.live k c m y hc hy hH
    · obtain ⟨y, hy, -, ha2, -⟩ := (hrel m).1 en hen
      rw [ha2]
      exact h.perCall k c m y spec mx hc hm' hy hs hx

theorem callMeters_nodup (hwf : p.WF) : (callMeters p c).Nodup := by
  unfold callMeters
  cases h : p.action? c.tool with
  | none => exact List.nodup_nil
  | some r => exact WF.meters_nodup hwf h

theorem Inv.settle (hwf : p.WF) (h : Inv p s) (hs : s.started = true) (hst : SettleStep p s t s') :
    Inv p s' := by
  obtain ⟨k, c, c', o, act, ne, hc, hH, hnH, ht, ha, hokf, hsame⟩ := hst
  refine Inv.same ?_ hsame
  have hout : ∀ m, m ∉ callMeters p c → ownEntries p s m k = [] := fun m hm =>
    List.eq_nil_iff_forall_not_mem.mpr fun en hen => by
      obtain ⟨c₀, r, hc₀, -, hra, hmr⟩ := h.owner m k en hen
      rw [hc] at hc₀
      cases hc₀
      exact hm (by unfold callMeters; rw [hra]; exact hmr)
  have hrel : ∀ m,
      (∀ en ∈ ownEntries p (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c)
          k o act ne t).1 m k,
        en.committed = true ∧ ∃ y ∈ ownEntries p s m k, en.amount ≤ y.amount) ∧
      (ownEntries p (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c)
          k o act ne t).1 m k).length ≤ (ownEntries p s m k).length := by
    intro m
    by_cases hm : m ∈ callMeters p c
    · obtain ⟨l₁, l₂, h₁, ⟨hlen, hcl⟩, h₃⟩ := settle_in (p := p) (k := k)
        (s := { s with calls := s.calls.insert k c' }) (o := o) (act := act) (ne := ne) (t := t)
        (callMeters_nodup hwf) hm
      refine ⟨fun en hen => ?_, Nat.le_trans h₃.length (Nat.le_trans hlen h₁.length)⟩
      obtain ⟨h1, y, hy, hle⟩ := hcl en (h₃.mem hen)
      exact ⟨h1, y, h₁.mem hy, hle⟩
    · have h₁ := settle_out (p := p) (s := { s with calls := s.calls.insert k c' }) (k := k)
        (o := o) (act := act) (ne := ne) (t := t) hm
      have h₀ : ownEntries p { s with calls := s.calls.insert k c' } m k = [] := hout m hm
      rw [h₀] at h₁
      rw [h₁.nil]
      exact ⟨fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  refine h.focus (settle_started.trans hs) settle_calls (fun m k' hk' => (settle_other hk').sub)
    (hokf (h.recs k c hc)) (fun m => Nat.le_trans (hrel m).2 (h.unique m k)) (fun m en hen => ?_)
    (fun _ _ _ _ _ hH' => absurd hH' hnH) (fun m en hen _ => ((hrel m).1 en hen).1)
    (fun _ _ _ hH' => absurd hH' hnH) (fun m en spec mx hm' hen hsp hx => ?_)
  · obtain ⟨-, y, hy, -⟩ := (hrel m).1 en hen
    obtain ⟨c₀, r, hc₀, h1, hra, hmr⟩ := h.owner m k y hy
    rw [hc] at hc₀
    cases hc₀
    exact ⟨by rw [ha]; exact h1, r, by rw [ht]; exact hra, hmr⟩
  · obtain ⟨-, y, hy, hle⟩ := (hrel m).1 en hen
    exact Nat.le_trans hle (h.perCall k c m y spec mx hc (by rw [← ht]; exact hm') hy hsp hx)

theorem Inv.handled (hwf : p.WF) (h : Inv p s) (hn : stepEnvelope s e = none)
    (hcl : (stepHandle p s e).2.claimed = false) : Inv p (stepHandle p s e).1 := by
  have henv := envelope_iff.mp hn
  cases hs : s.started
  · have hstart : e.body.isStart = true := by
      rcases henv.1 with h | h
      · rw [hs] at h; cases h
      · exact h
    cases hb : e.body
    all_goals (rw [hb] at hstart; try cases hstart)
    unfold Writ.stepHandle
    rw [hb]
    exact h.start hs
  · rcases stepHandle_kind hcl with hp | hst | ⟨l, hb, he⟩ | ⟨i, pd, r, ps, as, l, hb, he⟩
    · exact h.plain hs hp
    · exact h.settle hwf hs hst
    · rw [he]; exact h.sync hs
    · exact absurd ⟨hs, by rw [hb]; rfl⟩ henv.2.2.1

theorem Inv.stepped (hwf : p.WF) (hr : Reachable p d s) (h : Inv p s) :
    Inv p (step p s e).1 := by
  cases hcl : (step p s e).2.claimed
  · cases ha : (step p s e).2.accepted
    · rw [frame ha]; exact h
    · have hk := accepted_step ha
      have hcl' : (stepHandle p s e).2.claimed = false := by rw [hk] at hcl; exact hcl
      rw [hk]
      exact (h.handled hwf (accepted_open ha) hcl').same ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact h.claimed hwf hr hcl

theorem inv_reachable (hwf : p.WF) (hr : Reachable p d s) : Inv p s := by
  induction hr with
  | init => exact Inv.initial
  | step hr ih => exact ih.stepped hwf hr

end Accounting

open Accounting

variable {n cap mx : Nat} {cost : Option Cost} {g : List (String × Bool)} {key : String}
  {r : Requirements} {en : MeterEntry}

theorem accounting_reachable (hwf : p.WF) : Reachable p d s → Accounting p s := fun hr =>
  have h := inv_reachable hwf hr
  { unique := h.unique
    owner := fun m en hen hm hs => h.owner m en.call en (by
      rw [own_eq]; exact List.mem_filter.mpr ⟨hen, isFor_iff.mpr ⟨hm, hs, rfl⟩⟩)
    held := fun k c r m spec hk hra hm hs ha hH => by
      obtain ⟨en, he, h1, h2, h3⟩ := h.held k c r m hk hra hm ha hH
      exact ⟨en, he, h1, h2, by rw [h3, callAmount_eq hs]⟩
    settled := h.settled }

/-- Section 8, theorem 8: a committed entry of this session leaves its meter's list only when a
`ledger_sync` replaces the ledger, or when pruning drops it outside its meter's window. -/
theorem committed_stays (hwf : p.WF) (hr : Reachable p d s) (hen : en ∈ entriesOf p s m)
    (hm : en.meter = m) (hs : en.session = s.sessionId) (hcm : en.committed = true)
    (ha : (step p s e).2.accepted = true) (hgone : en ∉ entriesOf p (step p s e).1 m) :
    (∃ l, e.body = .ledgerSync l) ∨ ∃ spec w, p.meter? m = some spec ∧ spec.windowMs = some w ∧
      en.time + w ≤ e.time ∧ (en.excess = 0 ∨ en.excessAt + w ≤ e.time) := by
  have h := inv_reachable hwf hr
  have hown : en ∈ ownEntries p s m en.call := by
    rw [own_eq]; exact List.mem_filter.mpr ⟨hen, isFor_iff.mpr ⟨hm, hs, rfl⟩⟩
  have hpr : ∀ s', Prunes p e.time (ownEntries p s m en.call) (ownEntries p s' m en.call) →
      en ∉ entriesOf p s' m → ∃ spec w, p.meter? m = some spec ∧ spec.windowMs = some w ∧
        en.time + w ≤ e.time ∧ (en.excess = 0 ∨ en.excessAt + w ≤ e.time) := fun s' hp hn => by
    have hg : en ∉ ownEntries p s' m en.call := fun h' => hn (by
      rw [own_eq] at h'; exact (List.mem_filter.mp h').1)
    obtain ⟨-, spec, w, hsp, hw, h1, h2⟩ := hp.gone hown hg
    exact ⟨spec, w, hm ▸ hsp, hw, h1, h2⟩
  have hnotk : ∀ k c, s.calls[k]? = some c → (Holds c ∨ c.attempts = 0) → en.call ≠ k :=
    fun k c hk hc he => by
      subst he
      rcases hc with hH | h0
      · have := h.live _ c m en hk hown hH
        rw [hcm] at this
        cases this
      · obtain ⟨c', _, hk', ha', -⟩ := h.owner m _ en hown
        rw [hk] at hk'
        cases hk'
        omega
  cases hcl : (step p s e).2.claimed
  · have hk := accepted_step ha
    have hcl' : (stepHandle p s e).2.claimed = false := by rw [hk] at hcl; exact hcl
    have henv := envelope_iff.mp (accepted_open ha)
    rw [hk] at hgone
    change en ∉ entriesOf p (stepHandle p s e).1 m at hgone
    cases hs' : s.started
    · obtain ⟨hsm, hled, -⟩ := h.empty hs'
      unfold entriesOf at hen
      split at hen
      · rw [hled] at hen; cases hen
      · rw [hsm] at hen; cases hen
    · rcases stepHandle_kind hcl' with hp | hst | ⟨l, hb, -⟩ | ⟨i, pd, rq, ps, as, l, hb, -⟩
      · exact absurd (by unfold entriesOf; rw [hp.sm, hp.led]; exact hen) hgone
      · right
        obtain ⟨k, c, c', o, act, ne, hc, hH, -, -, -, -, hsame⟩ := hst
        refine hpr _ ?_ hgone
        rw [own_same hsame]
        exact settle_other (p := p) (s := { s with calls := s.calls.insert k c' })
          (hnotk k c hc (.inl hH))
      · exact .inl ⟨l, hb⟩
      · exact absurd ⟨hs', by rw [hb]; rfl⟩ henv.2.2.1
  · right
    obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hr hcl
    obtain ⟨-, c, hc, ⟨hst, hretry, -⟩, -⟩ := (dispatch_claimed_iff he).mp hcl
    rw [claim_post hcl he hc] at hgone
    refine hpr _ (claim_other (key := key) (hnotk k c hc ?_)) hgone
    rcases hst with hst | hst
    · exact .inr ((h.recs k c hc).2.1 (.inr hst))
    · exact .inl (.inr ⟨hst, (hretry hst).1⟩)

theorem meter_cap_retry (hwf : p.WF) (hr : Reachable p d s) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .unknown) (hm : p.modeOf c.tool = .enforce)
    (hra : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap)
    (hout : ∀ en ∈ entriesOf p s m, en.meter = m → en.session = s.sessionId → en.call = k →
      spec.windowMs.all (en.time + · > e.time) = false) :
    usageAt spec (entriesOf p (step p s e).1 m) m e.time ≤ cap := by
  have hI := inv_reachable hwf hr
  obtain ⟨-, c', hc', ⟨-, hretry, -⟩, -⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  have hH : Holds c := .inr ⟨hst, (hretry hst).1⟩
  refine meter_cap_retry_of hwf h he hc hst hm hra hmr hs hcap hout (hI.unique m k)
    fun en hen hm' hs' hk' => ?_
  have hown : en ∈ ownEntries p s m k := by
    rw [own_eq]; exact List.mem_filter.mpr ⟨hen, isFor_iff.mpr ⟨hm', hs', hk'⟩⟩
  obtain ⟨c', r', hc', ha, -⟩ := hI.owner m k en hown
  rw [hc] at hc'
  cases hc'
  obtain ⟨x, hx, -, -, hamt⟩ := hI.held k c r m hc hra hmr ha hH
  rw [hx, List.mem_singleton] at hown
  rw [hown, hamt, callAmount_eq hs]
  exact Nat.le_refl _

/-- Section 8, theorem 8: no single call's reservation exceeds `max_per_call`, at every reachable
state, a partial capture included. -/
theorem reserved_per_call (hwf : p.WF) (hr : Reachable p d s) (hc : s.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hen : en ∈ ownEntries p s m k)
    (hs : p.meter? m = some spec) (hx : spec.maxPerCall = some mx) : en.amount ≤ mx :=
  (inv_reachable hwf hr).perCall k c m en spec mx hc hm hen hs hx

/-- Section 8, theorem 8: a `result` or `reconcile` that does not release a call holding its
reservation commits its entry on each of its action's meters, keeping the reservation's time,
never raising the amount and dating any overrun at the report; the entry then stays unless pruning
drops it outside its meter's window at once. -/
theorem settle_commits {o : Outcome} {act : Option Nat} {ne : Bool} (hwf : p.WF)
    (hr : Reachable p d s) (ha : (step p s e).2.accepted = true)
    (he : e.body = .result k o act ne ∨ e.body = .reconcile k o act ne) (hne : ne = false)
    (ho : o ≠ .declined) (hc : s.calls[k]? = some c) (hh : Holds c)
    (hra : p.action? c.tool = some r) (hmr : m ∈ r.meters) :
    ∃ en, ownEntries p s m k = [en] ∧ en.committed = false ∧
      ((∃ en', ownEntries p (step p s e).1 m k = [en'] ∧ en'.committed = true ∧
          en'.time = en.time ∧ en'.amount ≤ en.amount ∧
          ((en'.excess = en.excess ∧ en'.excessAt = en.excessAt) ∨
            (en'.amount = en.amount ∧ en'.excessAt = e.time))) ∨
        (ownEntries p (step p s e).1 m k = [] ∧ ∃ spec w, p.meter? m = some spec ∧
          spec.windowMs = some w ∧ en.time + w ≤ e.time ∧
          (en.excess = 0 ∨ en.excessAt + w ≤ e.time))) := by
  have h := inv_reachable hwf hr
  have ha1 : 1 ≤ c.attempts := (h.recs k c hc).2.2 (hh.imp id (·.1))
  obtain ⟨en, hen, hu, hx0, -⟩ := h.held k c r m hc hra hmr ha1 hh
  refine ⟨en, hen, hu, ?_⟩
  have hk := accepted_step ha
  have ha' : (stepHandle p s e).2.accepted = true := by rw [hk] at ha; exact ha
  obtain ⟨c', hsame⟩ : ∃ c', Same (State.settle p { s with calls := s.calls.insert k c' }
      (callMeters p c) k o act ne e.time).1 (stepHandle p s e).1 := by
    rcases he with he | he
    · have hs : stepHandle p s e = handleResult p s e.time k o act ne := by
        simp only [stepHandle, he]
      rw [hs] at ha' ⊢
      exact handleResult_own hc ha'
    · have hs : stepHandle p s e = handleReconcile p s e.time k o act ne := by
        simp only [stepHandle, he]
      rw [hs] at ha' ⊢
      exact handleReconcile_own hc ha'
  rw [own_same (hsame.trans (s₂ := (step p s e).1) (by rw [hk]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))]
  have hms : callMeters p c = r.meters := by unfold callMeters; rw [hra]; rfl
  have hrel : (ne || o == .declined) = false := by
    subst hne
    cases o <;> simp_all
  obtain ⟨y, ⟨hy1, hym, hyt, hya, hyx⟩, hy | ⟨hy, hpr⟩⟩ := settle_commit (p := p)
    (s := { s with calls := s.calls.insert k c' }) (t := e.time) (k := k) (m := m)
    (callMeters_nodup hwf) (hms ▸ hmr) hrel hen hu
  · exact .inl ⟨y, hy, hy1, hyt, hya, hyx⟩
  · obtain ⟨-, spec, w, hsp, hw, h1, -⟩ := hpr
    have hin : en ∈ ownEntries p s m k := by rw [hen]; exact List.mem_singleton_self en
    have hm' : en.meter = m := (isFor_iff.mp (own_isFor hin)).1
    refine .inr ⟨hy, spec, w, by rw [← hm', ← hym]; exact hsp, hw, by rw [← hyt]; exact h1,
      .inl hx0⟩

namespace Accounting

variable {ms : List String} {o : Outcome} {act : Option Nat} {ne : Bool}

theorem usage_filter (q : MeterEntry → Bool) {now : Nat} :
    usageAt spec (es.filter q) m now ≤ usageAt spec es m now := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons x es ih =>
    rw [List.filter_cons]
    split
    · rw [usageAt_cons, usageAt_cons]; omega
    · rw [usageAt_cons]; omega

theorem usage_commit {sid : String} {now : Nat}
    (ha : ∀ x ∈ es, x.isFor m' sid k = true → x.meter = m → a ≤ x.amount) :
    usageAt spec (es.map fun x => if !x.isFor m' sid k then x
      else if a > x.amount then { x with excess := a - x.amount, excessAt := t, committed := true }
      else { x with amount := a, committed := true }) m now ≤ usageAt spec es m now := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons x es ih =>
    have ih := ih fun y hy => ha y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, usageAt_cons, usageAt_cons]
    by_cases hi : x.isFor m' sid k = true
    · by_cases hxm : x.meter = m
      · have hng : ¬ a > x.amount := by have := ha x List.mem_cons_self hi hxm; omega
        simp only [hi, Bool.not_true, Bool.false_eq_true, ite_false, hng, hxm, ite_true]
        split <;> omega
      · simp only [hi, Bool.not_true, Bool.false_eq_true, ite_false]
        split <;> first | omega | (simp only [hxm, ite_false]; omega)
    · simp only [hi, Bool.not_false, ite_true]; omega

theorem reserved_eq (hu : (ownEntries p s m k).length ≤ 1) (hx : x ∈ entriesOf p s m)
    (hi : x.isFor m s.sessionId k = true) : s.reserved p m k = x.amount := by
  have hown : x ∈ ownEntries p s m k := by rw [own_eq]; exact List.mem_filter.mpr ⟨hx, hi⟩
  have h1 := one_of hu hown
  unfold State.reserved State.entry?
  rw [meterEntries_eq, ← List.head?_filter, ← own_eq, h1]
  rfl

theorem release_usage (hs : p.meter? m = some spec) :
    usageAt spec (entriesOf p (s.release p m' k t) m) m t ≤ usageAt spec (entriesOf p s m) m t := by
  unfold State.release
  rcases entriesOf_update with h | ⟨sc, h⟩ <;> rw [h]
  · exact Nat.le_refl _
  · rw [usageAt_upd hs]; exact usage_filter _

theorem commit_usage (hs : p.meter? m = some spec)
    (ha : ∀ x ∈ entriesOf p s m, x.isFor m' s.sessionId k = true → x.meter = m → a ≤ x.amount) :
    usageAt spec (entriesOf p (s.commit p m' k a t) m) m t ≤
      usageAt spec (entriesOf p s m) m t := by
  unfold State.commit
  rcases entriesOf_update with h | ⟨sc, h⟩ <;> rw [h]
  · exact Nat.le_refl _
  · rw [usageAt_upd hs]; exact usage_commit ha

theorem release_one (hu : (ownEntries p s m k).length ≤ 1) :
    (ownEntries p (s.release p m' k t) m k).length ≤ 1 := by
  by_cases he : m' = m
  · subst he; rw [own_release_self]; exact Nat.zero_le _
  · exact Nat.le_trans (own_release_other (.inl he)).length hu

theorem commit_one (hu : (ownEntries p s m k).length ≤ 1) :
    (ownEntries p (s.commit p m' k a t) m k).length ≤ 1 := by
  by_cases he : m' = m
  · subst he
    obtain ⟨l, ⟨hl, -⟩, hp⟩ :=
      own_commit_self (p := p) (s := s) (m := m') (k := k) (a := a) (t := t)
    exact Nat.le_trans hp.length (Nat.le_trans hl hu)
  · exact Nat.le_trans (own_commit_other (.inl he)).length hu

theorem commit_ok (hu : (ownEntries p s m k).length ≤ 1) (ha : m' = m → a ≤ s.reserved p m k) :
    ∀ x ∈ entriesOf p s m, x.isFor m' s.sessionId k = true → x.meter = m → a ≤ x.amount := by
  intro x hx hi hxm
  have hm' : m' = m := (isFor_iff.mp hi).1.symm.trans hxm
  subst hm'
  rw [← reserved_eq hu hx hi]
  exact ha rfl

/-- A settle raises usage on `m` at its own time only by reporting `m` as overrun. -/
theorem settle_usage (hs : p.meter? m = some spec) (hu : (ownEntries p s m k).length ≤ 1) :
    usageAt spec (entriesOf p (s.settle p ms k o act ne t).1 m) m t ≤
        usageAt spec (entriesOf p s m) m t ∨ m ∈ (s.settle p ms k o act ne t).2 := by
  unfold State.settle
  refine (foldl_invariant (fun b : State × List String => (ownEntries p b.1 m k).length ≤ 1 ∧
    (usageAt spec (entriesOf p b.1 m) m t ≤ usageAt spec (entriesOf p s m) m t ∨ m ∈ b.2))
    ?_ ms (s, []) ⟨hu, .inl (Nat.le_refl _)⟩).2
  intro ⟨acc, over⟩ m' ⟨hu', hU⟩
  dsimp only at hu' hU ⊢
  have hc : ∀ a, (m' = m → a ≤ acc.reserved p m k) →
      usageAt spec (entriesOf p (acc.commit p m' k a t) m) m t ≤
        usageAt spec (entriesOf p acc m) m t := fun a ha => commit_usage hs (commit_ok hu' ha)
  split
  · exact ⟨release_one hu', hU.imp_left (Nat.le_trans (release_usage hs))⟩
  · split
    · refine ⟨commit_one hu', ?_⟩
      by_cases hov : act.getD (acc.reserved p m' k) > acc.reserved p m' k
      · simp only [hov, ↓reduceIte]
        by_cases he : m' = m
        · subst he; exact .inr (List.mem_append_right _ List.mem_cons_self)
        · exact (hU.imp_left (Nat.le_trans (hc _ fun h => absurd h he))).imp_right
            (List.mem_append_left _)
      · simp only [hov, ↓reduceIte]
        exact hU.imp_left (Nat.le_trans (hc _ fun h => by subst h; exact Nat.le_of_not_lt hov))
    · exact ⟨commit_one hu', hU.imp_left (Nat.le_trans (hc _ fun h => by
        subst h; exact Nat.le_refl _))⟩

theorem handleResult_settles (ha : (handleResult p s t k o act ne).2.accepted = true) :
    ∃ c c', s.calls[k]? = some c ∧
      Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).1
        (handleResult p s t k o act ne).1 ∧
      (handleResult p s t k o act ne).2 = .ok (.ofOverrun
        (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).2)
        none := by
  unfold handleResult at ha ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?] at ha ⊢
  cases hc : s.calls[k]? with
  | none => rw [hc] at ha; cases ha
  | some c =>
    rw [hc] at ha
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hd
      simp only [hd, ↓reduceIte]
      refine ⟨c, { c with status := o.status }, rfl, ?_, ?_⟩
      · repeat' (first | (dsimp only) | split)
        all_goals first | exact recordFailure_same | exact recordSuccess_same | exact Same.refl
      · rfl

theorem handleReconcile_settles (ha : (handleReconcile p s t k o act ne).2.accepted = true) :
    ∃ c c', s.calls[k]? = some c ∧
      Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).1
        (handleReconcile p s t k o act ne).1 ∧
      (handleReconcile p s t k o act ne).2 = .ok (.ofOverrun
        (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).2)
        none := by
  unfold handleReconcile at ha ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?] at ha ⊢
  cases hc : s.calls[k]? with
  | none => rw [hc] at ha; cases ha
  | some c =>
    rw [hc] at ha
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hu
      split at ha
      · cases ha
      · rename_i hn
        simp only [hu, hn, ↓reduceIte]
        refine ⟨c, { c with reconciled := some o }, rfl, ?_, rfl⟩
        repeat' (first | (dsimp only) | split)
        all_goals first | exact recordFailure_same | exact Same.refl | (exfalso; simp_all)

/-- A `result` or `reconcile` that settles call `k`, with the verdict its settle decides. -/
def SettleV (p : Policy) (s : State) (t : Nat) (s' : State) (v : Verdict) : Prop :=
  ∃ k c c' o act ne, s.calls[k]? = some c ∧
    Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).1
      s' ∧
    v = .ok (.ofOverrun
      (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c) k o act ne t).2) none

theorem meter_kind (ha : (stepHandle p s e).2.accepted = true)
    (hcl : (stepHandle p s e).2.claimed = false) :
    Plain s (stepHandle p s e).1 ∨ SettleV p s e.time (stepHandle p s e).1 (stepHandle p s e).2 ∨
      (∃ l, e.body = .ledgerSync l) ∨ ∃ i pd r ps as l, e.body = .sessionStart i pd r ps as l := by
  revert ha hcl
  unfold stepHandle
  split <;> rename_i hb <;> intro ha hcl
  all_goals first
    | with_reducible exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, hb⟩))
    | with_reducible exact Or.inr (Or.inr (Or.inl ⟨_, hb⟩))
    | (obtain ⟨c, c', hc, hs, hv⟩ := handleResult_settles ha
       exact Or.inr (Or.inl ⟨_, c, c', _, _, _, hc, hs, hv⟩))
    | (obtain ⟨c, c', hc, hs, hv⟩ := handleReconcile_settles ha
       exact Or.inr (Or.inl ⟨_, c, c', _, _, _, hc, hs, hv⟩))
    | with_reducible exact Or.inl (handleDispatch_plain hcl)
    | with_reducible exact Or.inl handleSessionEnd_plain
    | with_reducible exact Or.inl handleTurnStart_plain
    | with_reducible exact Or.inl handleTurnEnd_plain
    | with_reducible exact Or.inl handleStepStart_plain
    | with_reducible exact Or.inl handleApproverAttest_plain
    | with_reducible exact Or.inl handlePermissionRevoke_plain
    | with_reducible exact Or.inl handlePropose_plain
    | with_reducible exact Or.inl handleApprove_plain
    | with_reducible exact Or.inl handleReject_plain
    | with_reducible exact Or.inl handleApprovalExpire_plain
    | with_reducible exact Or.inl handleGrantCreate_plain
    | with_reducible exact Or.inl handleGrantRevoke_plain
    | with_reducible exact Or.inl handleOutcomeUnknown_plain
    | with_reducible exact Or.inl handleCancel_plain
    | with_reducible exact Or.inl handleReset_plain
    | with_reducible exact Or.inl handleKill_plain
    | with_reducible exact Or.inl handlePermissionAdd_plain
    | with_reducible exact Or.inl handleEscalationAck_plain

theorem stale_out (hu : (ownEntries p s m k).length ≤ 1) (hst : Stale p s t m k)
    (hs : p.meter? m = some spec) :
    ∀ en ∈ ownEntries p s m k, spec.windowMs.all (en.time + · > t) = false := fun en hen =>
  hst en (by rw [find_own, one_of hu hen]; rfl) spec hs

theorem own_mem {en : MeterEntry} (hen : en ∈ entriesOf p s m) (h1 : en.meter = m)
    (h2 : en.session = s.sessionId) (h3 : en.call = k) : en ∈ ownEntries p s m k :=
  List.mem_filter.mpr ⟨hen, decide_eq_true ⟨h1, h2, h3⟩⟩

theorem ofOverrun_mem (h : m ∈ ms) : Decision.ofOverrun ms = .overrun ms := by
  cases ms with
  | nil => cases h
  | cons => rfl

end Accounting

/-- Section 8, theorem 8: a retry inside its window reuses its reservation, in either mode. -/
theorem meter_reuse (hwf : p.WF) (hrch : Reachable p d s) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .unknown) (hs : p.meter? m = some spec)
    (hin : ∃ en ∈ ownEntries p s m k, spec.windowMs.all (en.time + · > e.time) = true) :
    usageAt spec (entriesOf p (step p s e).1 m) m e.time =
      usageAt spec (entriesOf p s m) m e.time := by
  obtain ⟨en, hen, hw⟩ := hin
  have hret : (c.status == .unknown) = true := by rw [hst]; rfl
  rw [claimed_entries h he hc, hret, entriesOf_claim_retry]
  refine retime_fold_other hs _ _ fun hsm => ?_
  rw [stale_out ((accounting_reachable hwf hrch).unique m k) (Dispatch.stale_iff.mp hsm).2 hs en
    hen] at hw
  cases hw

/-- Section 8, theorem 8: usage passes the cap only through an overrun, a `log_only` reservation,
or a ledger the host brings. -/
theorem over_cap_only_by (hwf : p.WF) (hrch : Reachable p d s)
    (ha : (step p s e).2.accepted = true) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap)
    (hover : cap < usageAt spec (entriesOf p (step p s e).1 m) m e.time) :
    cap < usageAt spec (entriesOf p s m) m e.time ∨
      (∃ ms sh, (step p s e).2 = .ok (.overrun ms) sh ∧ m ∈ ms) ∨
      (∃ k n dg cost g key c, e.body = .dispatch k n dg cost g key ∧ s.calls[k]? = some c ∧
        p.modeOf c.tool = .logOnly) ∨
      (∃ l, e.body = .ledgerSync l) ∨
      (∃ i pd rq ps as l, e.body = .sessionStart i pd rq ps as l) := by
  have hA := accounting_reachable hwf hrch
  have hle (h : usageAt spec (entriesOf p (step p s e).1 m) m e.time ≤
      usageAt spec (entriesOf p s m) m e.time) : cap < usageAt spec (entriesOf p s m) m e.time :=
    Nat.lt_of_lt_of_le hover h
  cases hcl : (step p s e).2.claimed
  · have hk := accepted_step ha
    have hcl' : (stepHandle p s e).2.claimed = false := by rw [hk] at hcl; exact hcl
    have ha' : (stepHandle p s e).2.accepted = true := by rw [hk] at ha; exact ha
    have hE : entriesOf p (step p s e).1 m = entriesOf p (stepHandle p s e).1 m := by rw [hk]; rfl
    rcases meter_kind ha' hcl' with hp | ⟨k, c, c', o, act, ne, -, hsame, hv⟩ | hl | hss
    · refine .inl (hle (Nat.le_of_eq ?_))
      rw [hE]; unfold entriesOf; rw [hp.sm, hp.led]
    · rcases settle_usage (s := { s with calls := s.calls.insert k c' }) (ms := callMeters p c)
        (o := o) (act := act) (ne := ne) (t := e.time) hs (hA.unique m k) with h | h
      · exact .inl (hle (by rw [hE, entriesOf_same hsame]; exact h))
      · refine .inr (.inl ⟨_, none, ?_, h⟩)
        rw [hk]
        exact hv.trans (congrArg (Verdict.ok · none) (ofOverrun_mem h))
    · exact .inr (.inr (.inr (.inl hl)))
    · exact .inr (.inr (.inr (.inr hss)))
  · obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hrch hcl
    obtain ⟨-, c, hc, ⟨hst, -⟩, -⟩ := (dispatch_claimed_iff he).mp hcl
    cases hmode : p.modeOf c.tool
    · have hE := claimed_entries (m := m) hcl he hc
      refine .inl (hle ?_)
      rcases hst with hst | hst
      · have hret : (c.status == .unknown) = false := by rw [hst]; rfl
        rw [hret, entriesOf_claim_first] at hE
        by_cases hmr : m ∈ ((p.action? c.tool).getD {}).meters
        · exact absurd (meter_cap hwf hcl he hc hst hmode (action_of_mem hmr) hmr hs hcap)
            (Nat.not_le.mpr hover)
        · rw [hE, reserve_fold_other hs _ _ hmr, entriesOf_consumeGrant]
          exact Nat.le_refl _
      · have hret : (c.status == .unknown) = true := by rw [hst]; rfl
        rw [hret, entriesOf_claim_retry] at hE
        by_cases hsm : m ∈ s.staleMeters p e.time ((p.action? c.tool).getD {}).meters k
        · obtain ⟨hmr, hstale⟩ := Dispatch.stale_iff.mp hsm
          have hout := stale_out (hA.unique m k) hstale hs
          exact absurd (meter_cap_retry hwf hrch hcl he hc hst hmode (action_of_mem hmr) hmr hs hcap
            fun en hen h1 h2 h3 => hout en (own_mem hen h1 h2 h3)) (Nat.not_le.mpr hover)
        · rw [hE, retime_fold_other hs _ _ hsm]
          exact Nat.le_refl _
    · exact .inr (.inr (.inl ⟨k, n, dg, cost, g, key, c, he, hc, hmode⟩))

namespace Accounting

def pusd : MeterSpec :=
  { unit := .money "USD", cap := some 100, scope := .principal, windowMs := some 10 }

def syncPolicy : Policy := { meters := [("usd", pusd)], actions := [("t", Meters.capAction)] }

def syncOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨30, "USD"⟩) [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "t" "d2" (some ⟨30, "USD"⟩) [] []⟩
  , ⟨5, 5, 4, none, .dispatch "c2" 1 "d2" (some ⟨30, "USD"⟩) [] "k2"⟩
  , ⟨6, 6, 5, none, .result "c2" .succeeded (some 30) false⟩
  , ⟨7, 7, 6, none, .dispatch "c1" 1 "d1" (some ⟨30, "USD"⟩) [] "k1"⟩
  , ⟨8, 8, 7, none, .outcomeUnknown "c1"⟩ ]

def c1Entry : MeterEntry :=
  { meter := "usd", session := "s1", call := "c1", time := 7, amount := 30, committed := false }

def c2Entry : MeterEntry := { c1Entry with call := "c2", time := 5, committed := true }

def otherEntry : MeterEntry :=
  { meter := "usd", session := "s2", call := "x", time := 8, amount := 10, committed := true }

/-- Another session of the principal dropped `c2`'s committed entry and wrote one of its own. -/
def prunedSync (entries : List MeterEntry) : Event :=
  ⟨9, 9, 8, none, .ledgerSync { version := 6, entries }⟩

def syncAll : List Event := syncOpen ++ [prunedSync [otherEntry, c1Entry]]

/-- Time 20 is past `c1`'s reservation window (7 + 10), so the retry re-times it. -/
def syncRetry : Event := ⟨10, 20, 9, none, .dispatch "c1" 2 "d1" (some ⟨30, "USD"⟩) [] "k1"⟩

#guard decide syncPolicy.WF
#guard syncPolicy.modeOf "t" == .enforce
#guard (trace syncPolicy (State.initial "pd") syncAll).all (·.2.2.accepted)
#guard (after syncPolicy "pd" syncOpen).ledger.entries == [c2Entry, c1Entry]
#guard !(entriesOf syncPolicy (after syncPolicy "pd" syncAll) "usd").contains c2Entry
#guard ownEntries syncPolicy (after syncPolicy "pd" syncAll) "usd" "c2" == []
#guard ownEntries syncPolicy (after syncPolicy "pd" syncAll) "usd" "c1" == [c1Entry]
#guard ((after syncPolicy "pd" syncAll).calls["c1"]?).any fun c =>
  c.status == .unknown && c.reconciled.isNone && c.attempts == 1
#guard (ownEntries syncPolicy (after syncPolicy "pd" syncAll) "usd" "c1").all fun en =>
  !pusd.windowMs.all (en.time + · > 20)
#guard (step syncPolicy (after syncPolicy "pd" syncAll) syncRetry).2.claimed
#guard ownEntries syncPolicy (step syncPolicy (after syncPolicy "pd" syncAll) syncRetry).1 "usd"
  "c1" == [{ c1Entry with time := 20 }]
#guard usageAt pusd (entriesOf syncPolicy (step syncPolicy (after syncPolicy "pd" syncAll)
  syncRetry).1 "usd") "usd" 20 == 30
#guard (step syncPolicy (after syncPolicy "pd" syncOpen) (prunedSync [otherEntry])).2
  == .rejected .ledgerConflict

def pruneOpen : List Event :=
  Meters.capOpen ++ [Meters.firstClaim, ⟨6, 6, 5, none, .result "c1" .succeeded none false⟩]

/-- Time 16 is past the committed entry's window (5 + 10), and this reservation changes the list. -/
def lateClaim : Event := ⟨7, 16, 6, none, .dispatch "c2" 1 "d2" (some ⟨60, "USD"⟩) [] "k2"⟩

def c1Done : MeterEntry :=
  { meter := "usd", session := "s1", call := "c1", time := 5, amount := 60, committed := true }

#guard (trace Meters.capPolicy (State.initial "pd") pruneOpen).all (·.2.2.accepted)
#guard entriesOf Meters.capPolicy (after Meters.capPolicy "pd" pruneOpen) "usd" == [c1Done]
#guard (step Meters.capPolicy (after Meters.capPolicy "pd" pruneOpen) lateClaim).2.claimed
#guard !(entriesOf Meters.capPolicy (step Meters.capPolicy (after Meters.capPolicy "pd" pruneOpen)
  lateClaim).1 "usd").contains c1Done
#guard Meters.usd.windowMs == some 10 && c1Done.excess == 0 && decide (c1Done.time + 10 ≤ 16)

def reconciled : List Event :=
  Meters.capUnknown ++ [⟨7, 7, 6, none, .reconcile "c1" .succeeded none false⟩]

/-- Time 20 is past the reservation's window (5 + 10), so pruning drops the entry as it commits. -/
def lateReconcile : Event := ⟨7, 20, 6, none, .reconcile "c1" .succeeded none false⟩

#guard ((after Meters.capPolicy "pd" Meters.capUnknown).calls["c1"]?).any fun c =>
  c.status == .unknown && c.reconciled.isNone && c.attempts == 1
#guard ownEntries Meters.capPolicy (after Meters.capPolicy "pd" Meters.capUnknown) "usd" "c1"
  == [{ c1Done with committed := false }]
#guard (trace Meters.capPolicy (State.initial "pd") reconciled).all (·.2.2.accepted)
#guard ((after Meters.capPolicy "pd" reconciled).calls["c1"]?).any fun c =>
  c.status == .unknown && c.reconciled == some .succeeded
#guard ownEntries Meters.capPolicy (after Meters.capPolicy "pd" reconciled) "usd" "c1" == [c1Done]
#guard (step Meters.capPolicy (after Meters.capPolicy "pd" Meters.capUnknown) lateReconcile).2
  == .ok .none none
#guard ownEntries Meters.capPolicy (step Meters.capPolicy (after Meters.capPolicy "pd"
  Meters.capUnknown) lateReconcile).1 "usd" "c1" == []

def captured (actual : Nat) : List Event :=
  Meters.perCallOpen ++
    [Meters.perCallClaim, ⟨5, 5, 4, none, .result "c1" .succeeded (some actual) false⟩]

#guard Meters.perCallPolicy.modeOf "t" == .enforce
#guard Meters.perCallPolicy.meter? "small" == some Meters.small
#guard Meters.small.maxPerCall == some 50
#guard (trace Meters.perCallPolicy (State.initial "pd") (captured 25)).all (·.2.2.accepted)
#guard (ownEntries Meters.perCallPolicy (after Meters.perCallPolicy "pd" (captured 25)) "small"
  "c1").map (fun en => (en.amount, en.committed, en.excess)) == [(25, true, 0)]
#guard (ownEntries Meters.perCallPolicy (after Meters.perCallPolicy "pd" (captured 70)) "small"
  "c1").map (fun en => (en.amount, en.committed, en.excess)) == [(40, true, 30)]

end Accounting

end Writ.Proofs
