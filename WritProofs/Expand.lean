import Writ.Author.Expand
import WritProofs.Join

namespace Writ.Proofs

open Writ
open Join

/-- Every entry the files of a layer-2 policy write for action `n`, the leaf's first: what
`expand` joins for `n`. -/
def actionEntries (parents : List Policy2) (p : Policy2) (n : String) : List Action2 :=
  (p :: parents).flatMap fun f => (f.actions.filter (·.1 == n)).map (·.2)

/-- Where `labels` puts dimension `dim` in `d`'s order, as `expand` reads one file's labels: a
missing or unknown value is the last, strictest, position. -/
def labelRank (d : LabelDim) (labels : List (String × String)) (dim : String) : Nat :=
  match labels.lookup dim with
  | some v => if v ∈ d.order then d.order.idxOf v else d.order.length - 1
  | none => d.order.length - 1

/-- The labels `expand` resolves for action `n` and matches rules against: per declared dimension,
the highest position over every file that names `n`. -/
def labelsOf (parents : List Policy2) (p : Policy2) (n : String) : List (String × String) :=
  mergedActionLabels (mergedDims (p :: parents)) ((actionEntries parents p n).map (·.labels))

namespace Expand

theorem mem_actionEntries {parents : List Policy2} {p : Policy2} {n : String} {a : Action2} :
    a ∈ actionEntries parents p n ↔ ∃ f ∈ p :: parents, (n, a) ∈ f.actions := by
  simp only [actionEntries, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨f, hf, ⟨k, b⟩, ⟨hk, rfl⟩, rfl⟩
    exact ⟨f, hf, hk⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (n, a), ⟨h, rfl⟩, rfl⟩

theorem find_map_pair (g : String → Requirements) (n : String) : ∀ l : List String,
    ((l.map fun k => (k, g k)).find? (·.1 == n)).map (·.2) = if n ∈ l then some (g n) else none
  | [] => rfl
  | k :: l => by
    by_cases h : k = n
    · subst h; simp
    · have : (k == n) = false := by simpa using h
      rw [List.map_cons, List.find?_cons, this]
      simp only [find_map_pair g n l, List.mem_cons]
      by_cases hn : n ∈ l
      · simp [hn]
      · simp [hn, Ne.symm h]

theorem action?_expand {parents : List Policy2} {p : Policy2} {n : String} {y : Requirements} :
    (expand parents p).action? n = some y ↔ (∃ a, a ∈ actionEntries parents p n) ∧
      y = expandAction (mergedDims (p :: parents)) ((p :: parents).flatMap (·.rules)) (p :: parents) n := by
  have hnamed : n ∈ ((p :: parents).flatMap (·.actions.map (·.1))).eraseDups ↔
      ∃ a, a ∈ actionEntries parents p n := by
    rw [List.mem_eraseDups]
    simp only [List.mem_flatMap, List.mem_map, mem_actionEntries]
    constructor
    · rintro ⟨f, hf, ⟨k, a⟩, ha, rfl⟩; exact ⟨a, f, hf, ha⟩
    · rintro ⟨a, f, hf, ha⟩; exact ⟨f, hf, (n, a), ha, rfl⟩
  unfold Policy.action? expand
  rw [find_map_pair]
  by_cases h : n ∈ ((p :: parents).flatMap (·.actions.map (·.1))).eraseDups
  · simp only [h, ↓reduceIte, Option.some.injEq]
    exact ⟨fun e => ⟨hnamed.mp h, e.symm⟩, fun ⟨_, e⟩ => e.symm⟩
  · simp only [h, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    exact fun ha => absurd (hnamed.mpr ha) h

theorem rules_ext (ctx : Policy2) (a : Action2) : ∀ (rules : List Rule) (x : Requirements),
    x.le (rules.foldl (fun acc rule => if rule.matches ctx a then acc.joinReq rule.require else acc) x)
  | [], x => req_le_refl x
  | r :: rs, x => by
    rw [List.foldl_cons]
    refine req_le_trans ?_ (rules_ext ctx a rs _)
    split
    · exact req_le_joinReq _ _
    · exact req_le_refl _

theorem rules_rule (ctx : Policy2) (a : Action2) {r : Rule} (hm : r.matches ctx a = true) :
    ∀ (rules : List Rule) (x : Requirements), r ∈ rules →
      r.require.le (rules.foldl (fun acc rule => if rule.matches ctx a then acc.joinReq rule.require else acc) x)
  | [], _, h => nomatch h
  | r' :: rs, x, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp only [hm, ↓reduceIte]; exact require_le_trans (require_le_joinReq _ _) (rules_ext ctx a rs _)
    · exact rules_rule ctx a hm rs _ h

theorem rules_lub (ctx : Policy2) (a : Action2) {z : Requirements} : ∀ (rules : List Rule) (x : Requirements),
    x.le z → (∀ r ∈ rules, r.matches ctx a = true → r.require.le z) →
      (rules.foldl (fun acc rule => if rule.matches ctx a then acc.joinReq rule.require else acc) x).le z
  | [], _, hx, _ => hx
  | r :: rs, x, hx, hr => by
    rw [List.foldl_cons]
    refine rules_lub ctx a rs _ ?_ (fun r' h' hm => hr r' (List.mem_cons_of_mem _ h') hm)
    split
    · exact joinReq_le hx (hr r List.mem_cons_self ‹_›)
    · exact hx

theorem resolvedLabel_eq (p : Policy2) (labels : List (String × String)) (dim : String) :
    p.resolvedLabel labels dim = (p.labels.lookup dim).map (labelRank · labels dim) := rfl

theorem matches_of {ctx₁ ctx₂ : Policy2} {a₁ a₂ : Action2} {r : Rule}
    (h : ∀ dim d, ctx₁.labels.lookup dim = some d →
      ctx₂.labels.lookup dim = some d ∧ labelRank d a₁.labels dim ≤ labelRank d a₂.labels dim)
    (hm : r.matches ctx₁ a₁ = true) : r.matches ctx₂ a₂ = true := by
  unfold Rule.matches at *
  rw [List.all_eq_true] at *
  rintro ⟨dim, v⟩ hv
  have hc := hm (dim, v) hv
  simp only [resolvedLabel_eq] at *
  cases h₁ : ctx₁.labels.lookup dim with
  | none => simp [h₁] at hc
  | some d =>
    obtain ⟨h₂, hle⟩ := h dim d h₁
    simp only [h₁, h₂, Option.map_some, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
    exact ⟨hc.1, Nat.le_trans hc.2 hle⟩

theorem foldl_joinStrict_ge : ∀ (rest : List Requirements) (a : Requirements),
    ∀ r ∈ a :: rest, r.le (rest.foldl Requirements.joinStrict a)
  | [], a, r, h => by rw [List.mem_singleton.mp h]; exact req_le_refl a
  | b :: rest, a, r, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact req_le_trans (req_le_joinStrict_left _ b)
        (foldl_joinStrict_ge rest _ _ List.mem_cons_self)
    rcases List.mem_cons.mp h with rfl | h
    · exact req_le_trans (req_le_joinStrict_right a _)
        (foldl_joinStrict_ge rest _ _ List.mem_cons_self)
    · exact foldl_joinStrict_ge rest _ r (List.mem_cons_of_mem _ h)

theorem foldl_joinStrict_le {c : Requirements} : ∀ (rest : List Requirements) (a : Requirements),
    a.le c → (∀ r ∈ rest, r.le c) → (rest.foldl Requirements.joinStrict a).le c
  | [], _, ha, _ => ha
  | b :: rest, a, ha, hr => by
    rw [List.foldl_cons]
    exact foldl_joinStrict_le rest _ (joinStrict_le ha (hr b List.mem_cons_self))
      (fun r h => hr r (List.mem_cons_of_mem _ h))

theorem le_explicitReq {rs : List Requirements} {r : Requirements} (h : r ∈ rs) :
    r.le (explicitReq rs) := by
  cases rs with
  | nil => nomatch h
  | cons a rest => exact foldl_joinStrict_ge rest a r h

theorem explicitReq_le {rs : List Requirements} {c : Requirements} (hne : rs ≠ [])
    (h : ∀ r ∈ rs, r.le c) : (explicitReq rs).le c := by
  cases rs with
  | nil => exact absurd rfl hne
  | cons a rest =>
    exact foldl_joinStrict_le rest a (h a List.mem_cons_self) (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem matches_length : ∀ {xs ys : List Clause}, Clause.Matches xs ys → xs.length ≤ ys.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, ys, ⟨_, hy, _, hm⟩ => by
    have h₁ := matches_length hm
    rw [List.length_erase_of_mem hy] at h₁
    have h₂ := List.length_pos_of_mem hy
    simp only [List.length_cons]
    omega

/-- A consent below one a single approval satisfies is satisfied by a single approval too. -/
theorem single_of_le {c d : Consent} (h : c.le d) (hd : d.single = true) : c.single = true := by
  unfold Consent.single Consent.clauses at *
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_flatMap, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at *
  obtain ⟨hk, hg⟩ := hd
  refine ⟨?_, ?_⟩
  · rintro x ⟨g, hg', hx⟩
    obtain ⟨h', hh', hgh⟩ := h g hg'
    obtain ⟨y, hy, hxy⟩ := hgh.2.2 x hx
    exact Nat.le_trans hxy.1 (hk y ⟨h', hh', hy⟩)
  · intro g hgc
    obtain ⟨h', hh', hgh⟩ := h g hgc
    cases hdist : g.distinct
    · exact .inl rfl
    · right
      have hm := matches_length (hgh.2.1 hdist)
      rcases hg h' hh' with h₁ | h₁
      · exact absurd (hgh.1 hdist) (by simp [h₁])
      · omega

theorem le_grant_none {x y : Requirements} (h : x.le y) (g : Option Grantable) :
    ({ x with grantable := g } : Requirements).le { y with grantable := none } := by
  obtain ⟨c, -, e, i, r, u, f, m, k, s, n, p, q⟩ := h
  exact ⟨c, by cases g <;> trivial, e, i, r, u, f, m, k, s, n, p, q⟩

theorem le_dropMultiGrant (x : Requirements) : x.le (dropMultiGrant x) := by
  unfold dropMultiGrant
  split
  · exact req_le_refl x
  · exact le_grant_none (req_le_refl x) x.grantable

theorem dropMultiGrant_mono {x y : Requirements} (h : x.le y) :
    (dropMultiGrant x).le (dropMultiGrant y) := by
  unfold dropMultiGrant
  by_cases hy : y.consent.single = true
  · simp only [hy, single_of_le h.1 hy, ↓reduceIte]; exact h
  · simp only [hy, Bool.false_eq_true, ↓reduceIte]
    split
    · exact le_grant_none h x.grantable
    · exact le_grant_none h none

/-- The escalators `settleGrant` keeps when the action has no `grantable`. -/
def settled (l : List (String × Escalator)) : List (String × Escalator) :=
  (l.filter fun (_, e) => !(e.consent.groups.isEmpty && e.grantable)).map
    fun (n, e) => (n, { e with grantable := false })

theorem settleGrant_eq (r : Requirements) :
    settleGrant r = if r.grantable.isNone then { r with escalate := settled r.escalate } else r := rfl

theorem foldl_join_groups {g : Group} : ∀ (es : List (String × Escalator)) (acc : Escalator),
    g ∈ (es.foldl (fun acc p => acc.join p.2) acc).consent.groups ↔
      g ∈ acc.consent.groups ∨ ∃ p ∈ es, g ∈ p.2.consent.groups
  | [], acc => by simp
  | p :: es, acc => by
    rw [List.foldl_cons, foldl_join_groups es]
    simp only [Escalator.join, consent_mem_join, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]

theorem foldl_join_grantable : ∀ (es : List (String × Escalator)) (acc : Escalator),
    (es.foldl (fun acc p => acc.join p.2) acc).grantable = (acc.grantable && es.all (·.2.grantable))
  | [], acc => by simp
  | p :: es, acc => by
    rw [List.foldl_cons, foldl_join_grantable es]
    simp only [Escalator.join, List.all_cons, Bool.and_assoc]

theorem mem_escAt {l : List (String × Escalator)} {n : String} {g : Group} :
    g ∈ (escAt l n).consent.groups ↔ ∃ p ∈ l, p.1 = n ∧ g ∈ p.2.consent.groups := by
  unfold escAt
  rw [foldl_join_groups]
  simp only [Consent.none, List.not_mem_nil, false_or, List.mem_filter, beq_iff_eq, and_assoc]

theorem grantable_escAt {l : List (String × Escalator)} {n : String} :
    (escAt l n).grantable = true ↔ ∀ p ∈ l, p.1 = n → p.2.grantable = true := by
  unfold escAt
  rw [foldl_join_grantable]
  simp only [Bool.true_and, List.all_eq_true, List.mem_filter, beq_iff_eq, and_imp]

theorem mem_settled {l : List (String × Escalator)} {p : String × Escalator} :
    p ∈ settled l ↔ ∃ q ∈ l, !(q.2.consent.groups.isEmpty && q.2.grantable) = true ∧
      p = (q.1, { q.2 with grantable := false }) := by
  unfold settled
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨k, e⟩, ⟨hq, hk⟩, rfl⟩; exact ⟨(k, e), hq, hk, rfl⟩
  · rintro ⟨⟨k, e⟩, hq, hk, rfl⟩; exact ⟨(k, e), ⟨hq, hk⟩, rfl⟩

theorem mem_escAt_settled {l : List (String × Escalator)} {n : String} {g : Group} :
    g ∈ (escAt (settled l) n).consent.groups ↔ g ∈ (escAt l n).consent.groups := by
  rw [mem_escAt, mem_escAt]
  constructor
  · rintro ⟨p, hp, rfl, hg⟩
    obtain ⟨q, hq, -, rfl⟩ := mem_settled.mp hp
    exact ⟨q, hq, rfl, hg⟩
  · rintro ⟨q, hq, rfl, hg⟩
    refine ⟨(q.1, { q.2 with grantable := false }), mem_settled.mpr ⟨q, hq, ?_, rfl⟩, rfl, hg⟩
    have : q.2.consent.groups.isEmpty = false := by
      cases h : q.2.consent.groups with
      | nil => rw [h] at hg; nomatch hg
      | cons => rfl
    simp [this]

theorem grantable_escAt_settled {l : List (String × Escalator)} {n : String} :
    (escAt (settled l) n).grantable = true ↔
      ∀ q ∈ l, q.1 = n → q.2.consent.groups = [] ∧ q.2.grantable = true := by
  rw [grantable_escAt]
  constructor
  · intro h q hq hn
    by_cases hk : !(q.2.consent.groups.isEmpty && q.2.grantable) = true
    · have := h _ (mem_settled.mpr ⟨q, hq, hk, rfl⟩) hn
      simp at this
    · simpa using hk
  · intro h p hp hn
    obtain ⟨q, hq, hk, rfl⟩ := mem_settled.mp hp
    have := h q hq hn
    simp [this.1, this.2] at hk

theorem esc_le_settled (l : List (String × Escalator)) : EscLe l (settled l) := by
  refine escLe_iff.mpr fun n => ⟨fun g hg => ⟨g, mem_escAt_settled.mpr hg, group_le_refl g⟩, ?_⟩
  intro h
  exact grantable_escAt.mpr fun q hq hn => ((grantable_escAt_settled.mp h) q hq hn).2

theorem settled_mono {l₁ l₂ : List (String × Escalator)} (h : EscLe l₁ l₂) :
    EscLe (settled l₁) (settled l₂) := by
  refine escLe_iff.mpr fun n => ⟨fun g hg => ?_, fun hs => ?_⟩
  · obtain ⟨g', hg', hle⟩ := (escLe_iff.mp h n).1 g (mem_escAt_settled.mp hg)
    exact ⟨g', mem_escAt_settled.mpr hg', hle⟩
  · have h₂ := grantable_escAt_settled.mp hs
    have hc := (escLe_iff.mp h n).1
    have hb := (escLe_iff.mp h n).2 (grantable_escAt.mpr fun q hq hn => (h₂ q hq hn).2)
    refine grantable_escAt_settled.mpr fun q hq hn => ⟨?_, grantable_escAt.mp hb q hq hn⟩
    cases hgs : q.2.consent.groups with
    | nil => rfl
    | cons g gs =>
      obtain ⟨g', hg', -⟩ := hc g (mem_escAt.mpr ⟨q, hq, hn, by simp [hgs]⟩)
      obtain ⟨q', hq', hn', hg''⟩ := mem_escAt.mp hg'
      rw [(h₂ q' hq' hn').1] at hg''
      nomatch hg''

theorem le_escalate {x y : Requirements} (h : x.le y) {e : List (String × Escalator)}
    (he : EscLe x.escalate e) : x.le { y with escalate := e } := by
  obtain ⟨c, g, ex, i, r, u, f, m, k, -, n, p, q⟩ := h
  exact ⟨c, g, ex, i, r, u, f, m, k, he, n, p, q⟩

theorem le_settleGrant (x : Requirements) : x.le (settleGrant x) := by
  rw [settleGrant_eq]
  split
  · exact le_escalate (req_le_refl x) (esc_le_settled _)
  · exact req_le_refl x

theorem settleGrant_mono {x y : Requirements} (h : x.le y) : (settleGrant x).le (settleGrant y) := by
  by_cases hx : x.grantable.isNone = true
  · have hy : y.grantable.isNone = true := by
      have hg := h.2.1
      cases hxg : x.grantable with
      | some a => rw [hxg] at hx; simp at hx
      | none =>
        cases hyg : y.grantable with
        | none => rfl
        | some b => rw [hxg, hyg] at hg; exact hg.elim
    rw [settleGrant_eq, settleGrant_eq]
    simp only [hx, hy, ↓reduceIte]
    obtain ⟨c, g, ex, i, r, u, f, m, k, s, n, p, q⟩ := h
    exact ⟨c, g, ex, i, r, u, f, m, k, settled_mono s, n, p, q⟩
  · have : settleGrant x = x := by
      rw [settleGrant_eq]; simp only [hx, Bool.false_eq_true, ↓reduceIte]
    rw [this]
    exact req_le_trans h (le_settleGrant y)

theorem lookup_none {β : Type} : ∀ {l : List (String × β)} {k : String}, k ∉ l.map (·.1) →
    l.lookup k = none
  | [], _, _ => rfl
  | (k', b) :: l, k, h => by
    have hk : (k == k') = false := by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simpa using h.1
    rw [List.lookup_cons, hk]
    exact lookup_none fun h' => h (List.mem_cons_of_mem _ h')

theorem mem_of_lookup {β : Type} : ∀ {l : List (String × β)} {k : String} {v : β},
    l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => nomatch h
  | (k', b) :: l, k, v, h => by
    rw [List.lookup_cons] at h
    by_cases hk : k = k'
    · subst hk
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h; exact List.mem_cons_self
    · have : (k == k') = false := by simpa using hk
      rw [this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lookup_of_mem {β : Type} : ∀ {l : List (String × β)} {k : String} {v : β},
    (l.map (·.1)).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => nomatch h
  | (k', b) :: l, k, v, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.lookup_cons]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have hk : (k == k') = false := by
        have : k ∈ l.map (·.1) := List.mem_map.mpr ⟨(k, v), h, rfl⟩
        simp only [beq_eq_false_iff_ne, ne_eq]
        rintro rfl; exact hn.1 this
      rw [hk]
      exact lookup_of_mem hn.2 h

theorem mem_dims_fold : ∀ (l acc : List (String × LabelDim)) (e : String × LabelDim),
    e ∈ l.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) acc →
      e ∈ acc ∨ e ∈ l
  | [], _, _, h => .inl h
  | x :: l, acc, e, h => by
    rw [List.foldl_cons] at h
    rcases mem_dims_fold l _ e h with h | h
    · by_cases hd : (acc.any (·.1 == x.1)) = true
      · simp only [hd, ↓reduceIte] at h; exact .inl h
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        rcases List.mem_append.mp h with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.mp h ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

theorem nodup_dims_fold : ∀ (l acc : List (String × LabelDim)), (acc.map (·.1)).Nodup →
    ((l.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) acc).map
      (·.1)).Nodup
  | [], _, h => h
  | x :: l, acc, h => by
    rw [List.foldl_cons]
    apply nodup_dims_fold l
    by_cases hd : (acc.any (·.1 == x.1)) = true
    · simp only [hd, ↓reduceIte]; exact h
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      rw [List.map_append, List.nodup_append]
      refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      apply hd
      simp only [List.any_eq_true, beq_iff_eq]
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact ⟨e, he, hab.trans hb⟩

theorem acc_dims_fold : ∀ (l acc : List (String × LabelDim)) (e : String × LabelDim), e ∈ acc →
    e ∈ l.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) acc
  | [], _, _, h => h
  | x :: l, acc, e, h => by
    rw [List.foldl_cons]
    apply acc_dims_fold l
    by_cases hd : (acc.any (·.1 == x.1)) = true
    · simp only [hd, ↓reduceIte]; exact h
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]; exact List.mem_append_left _ h

theorem name_dims_fold : ∀ (l acc : List (String × LabelDim)) (e : String × LabelDim), e ∈ l →
    ∃ o, (e.1, o) ∈ l.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) acc
  | [], _, _, h => nomatch h
  | x :: l, acc, e, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · by_cases hd : (acc.any (·.1 == e.1)) = true
      · simp only [hd, ↓reduceIte]
        simp only [List.any_eq_true, beq_iff_eq] at hd
        obtain ⟨⟨k, o'⟩, hk, rfl⟩ := hd
        exact ⟨o', acc_dims_fold l _ _ hk⟩
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        exact ⟨e.2, acc_dims_fold l _ _ (List.mem_append_right _ List.mem_cons_self)⟩
    · exact name_dims_fold l _ e h

theorem mem_mergedDims {files : List Policy2} {e : String × LabelDim} (h : e ∈ mergedDims files) :
    e ∈ files.flatMap (·.labels) :=
  (mem_dims_fold _ [] e h).resolve_left List.not_mem_nil

theorem nodup_mergedDims (files : List Policy2) : ((mergedDims files).map (·.1)).Nodup :=
  nodup_dims_fold _ [] List.nodup_nil

theorem exists_mergedDims {files : List Policy2} {dim : String} {o : LabelDim}
    (h : (dim, o) ∈ files.flatMap (·.labels)) : ∃ d, (dim, d) ∈ mergedDims files :=
  name_dims_fold _ [] _ h

/-- The position `mergedActionLabels` takes for dimension `dim` over `ls`. -/
def bestRank (d : LabelDim) (dim : String) (ls : List (List (String × String))) : Nat :=
  match ls.map (labelRank d · dim) with
  | [] => d.order.length - 1
  | r :: rs => rs.foldl max r

theorem mergedActionLabels_eq (dims : List (String × LabelDim)) (ls : List (List (String × String))) :
    mergedActionLabels dims ls =
      dims.filterMap fun x => (x.2.order[bestRank x.2 x.1 ls]?).map (x.1, ·) := rfl

theorem le_foldl_max : ∀ (rs : List Nat) (r : Nat), r ≤ rs.foldl max r ∧ ∀ x ∈ rs, x ≤ rs.foldl max r
  | [], r => ⟨Nat.le_refl r, fun _ h => nomatch h⟩
  | x :: rs, r => by
    rw [List.foldl_cons]
    obtain ⟨h₁, h₂⟩ := le_foldl_max rs (max r x)
    refine ⟨Nat.le_trans (Nat.le_max_left r x) h₁, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_trans (Nat.le_max_right r y) h₁
    · exact h₂ y hy

theorem foldl_max_le : ∀ (rs : List Nat) (r k : Nat), r ≤ k → (∀ x ∈ rs, x ≤ k) → rs.foldl max r ≤ k
  | [], _, _, h, _ => h
  | x :: rs, r, k, h, hx => by
    rw [List.foldl_cons]
    exact foldl_max_le rs _ k (Nat.max_le.mpr ⟨h, hx x List.mem_cons_self⟩)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem labelRank_le_bestRank {d : LabelDim} {dim : String} {ls : List (List (String × String))}
    {l : List (String × String)} (h : l ∈ ls) : labelRank d l dim ≤ bestRank d dim ls := by
  unfold bestRank
  have hm : labelRank d l dim ∈ ls.map (labelRank d · dim) := List.mem_map.mpr ⟨l, h, rfl⟩
  split
  · rename_i he; rw [he] at hm; nomatch hm
  · rename_i r rs he
    rw [he] at hm
    rcases List.mem_cons.mp hm with h' | h'
    · rw [h']; exact (le_foldl_max rs r).1
    · exact (le_foldl_max rs r).2 _ h'

theorem bestRank_le {d : LabelDim} {dim : String} {ls : List (List (String × String))} {k : Nat}
    (hne : ls ≠ []) (h : ∀ l ∈ ls, labelRank d l dim ≤ k) : bestRank d dim ls ≤ k := by
  unfold bestRank
  split
  · rename_i he; exact absurd (List.map_eq_nil_iff.mp he) hne
  · rename_i r rs he
    have hall : ∀ x ∈ r :: rs, x ≤ k := by
      rw [← he]; intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      exact h l hl
    exact foldl_max_le rs r k (hall r List.mem_cons_self) (fun x hx => hall x (List.mem_cons_of_mem _ hx))

theorem labelRank_lt {d : LabelDim} (hne : d.order ≠ []) (l : List (String × String)) (dim : String) :
    labelRank d l dim < d.order.length := by
  have hpos : 0 < d.order.length := List.length_pos_iff.mpr hne
  unfold labelRank
  split
  · split
    · exact List.idxOf_lt_length_of_mem ‹_›
    · omega
  · omega

theorem bestRank_lt {d : LabelDim} (hne : d.order ≠ []) (dim : String)
    (ls : List (List (String × String))) : bestRank d dim ls < d.order.length := by
  have hpos : 0 < d.order.length := List.length_pos_iff.mpr hne
  unfold bestRank
  split
  · omega
  · rename_i r rs he
    have hall : ∀ x ∈ r :: rs, x ≤ d.order.length - 1 := by
      rw [← he]; intro x hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
      have := labelRank_lt hne l dim
      omega
    have := foldl_max_le rs r _ (hall r List.mem_cons_self) (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    omega

theorem labelRank_nil {d : LabelDim} (h : d.order = []) (l : List (String × String)) (dim : String) :
    labelRank d l dim = 0 := by
  unfold labelRank
  rw [h]
  split
  · simp
  · rfl

theorem lookup_filterMap {g : String × LabelDim → Option String} {dim : String} {d : LabelDim} :
    ∀ dims : List (String × LabelDim), (dims.map (·.1)).Nodup → (dim, d) ∈ dims →
      (dims.filterMap fun x => (g x).map (x.1, ·)).lookup dim = g (dim, d)
  | [], _, h => nomatch h
  | (k, e) :: rest, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    have hkeys : ∀ k' v, (k', v) ∈ rest.filterMap (fun x => (g x).map (x.1, ·)) →
        k' ∈ rest.map (·.1) := by
      intro k' v hv
      obtain ⟨⟨a, b⟩, ha, hab⟩ := List.mem_filterMap.mp hv
      simp only [Option.map_eq_some_iff] at hab
      obtain ⟨_, -, hab⟩ := hab
      cases hab
      exact List.mem_map.mpr ⟨(k', b), ha, rfl⟩
    rw [List.filterMap_cons]
    by_cases hk : k = dim
    · subst hk
      have he : e = d := by
        rcases List.mem_cons.mp h with h | h
        · cases h; rfl
        · exact absurd (List.mem_map.mpr ⟨_, h, rfl⟩) hn.1
      subst he
      cases hv : g (k, e) with
      | none =>
        simp only [Option.map_none]
        exact lookup_none fun hm => by
          obtain ⟨⟨k', v⟩, hm', rfl⟩ := List.mem_map.mp hm
          exact hn.1 (hkeys k' v hm')
      | some v => simp
    · have h' : (dim, d) ∈ rest := by
        rcases List.mem_cons.mp h with h | h
        · cases h; exact absurd rfl hk
        · exact h
      have ih := lookup_filterMap (g := g) rest hn.2 h'
      cases g (k, e) with
      | none => exact ih
      | some v =>
        have : (dim == k) = false := by simpa using Ne.symm hk
        simp only [Option.map_some, List.lookup_cons, this]
        exact ih

theorem labelRank_merged {dims : List (String × LabelDim)} {ls : List (List (String × String))}
    {dim : String} {d : LabelDim} (hn : (dims.map (·.1)).Nodup) (hm : (dim, d) ∈ dims)
    (hnd : d.order.Nodup) (hne : d.order ≠ []) :
    labelRank d (mergedActionLabels dims ls) dim = bestRank d dim ls := by
  have hlt := bestRank_lt hne dim ls
  unfold labelRank
  rw [mergedActionLabels_eq, lookup_filterMap (g := fun x => x.2.order[bestRank x.2 x.1 ls]?) dims hn hm,
    List.getElem?_eq_getElem hlt]
  simp only [List.getElem_mem, ↓reduceIte]
  exact hnd.idxOf_getElem _ hlt

theorem rank_le_merged {dims : List (String × LabelDim)} {ls : List (List (String × String))}
    {dim : String} {d : LabelDim} {l : List (String × String)} (hn : (dims.map (·.1)).Nodup)
    (hm : (dim, d) ∈ dims) (hnd : d.order.Nodup) (hl : l ∈ ls) :
    labelRank d l dim ≤ labelRank d (mergedActionLabels dims ls) dim := by
  by_cases he : d.order = []
  · rw [labelRank_nil he]; exact Nat.zero_le _
  · rw [labelRank_merged hn hm hnd he]; exact labelRank_le_bestRank hl

theorem merged_le_merged {dims dims' : List (String × LabelDim)}
    {ls ls' : List (List (String × String))} {dim : String} {d : LabelDim}
    (hn : (dims.map (·.1)).Nodup) (hm : (dim, d) ∈ dims) (hn' : (dims'.map (·.1)).Nodup)
    (hm' : (dim, d) ∈ dims') (hnd : d.order.Nodup) (hne : ls ≠ [])
    (h : ∀ l ∈ ls, ∃ l' ∈ ls', labelRank d l dim ≤ labelRank d l' dim) :
    labelRank d (mergedActionLabels dims ls) dim ≤ labelRank d (mergedActionLabels dims' ls') dim := by
  by_cases he : d.order = []
  · rw [labelRank_nil he]; exact Nat.zero_le _
  · rw [labelRank_merged hn hm hnd he, labelRank_merged hn' hm' hnd he]
    refine bestRank_le hne fun l hl => ?_
    obtain ⟨l', hl', hle⟩ := h l hl
    exact Nat.le_trans hle (labelRank_le_bestRank hl')

/-- The action `expand` builds for `n` before rules apply. -/
def mergedAction (parents : List Policy2) (p : Policy2) (n : String) : Action2 :=
  ⟨explicitReq ((actionEntries parents p n).map (·.req)), labelsOf parents p n⟩

theorem expand_some {parents : List Policy2} {p : Policy2} {n : String} {y : Requirements}
    (h : (expand parents p).action? n = some y) : (∃ a, a ∈ actionEntries parents p n) ∧
      y = settleGrant (dropMultiGrant (((p :: parents).flatMap (·.rules)).foldl
        (fun acc rule => if rule.matches { labels := mergedDims (p :: parents) } (mergedAction parents p n)
          then acc.joinReq rule.require else acc) (mergedAction parents p n).req)) :=
  action?_expand.mp h

theorem expand_named {parents : List Policy2} {p : Policy2} {n : String} {a : Action2}
    (h : a ∈ actionEntries parents p n) : (expand parents p).action? n =
      some (settleGrant (dropMultiGrant (((p :: parents).flatMap (·.rules)).foldl
        (fun acc rule => if rule.matches { labels := mergedDims (p :: parents) } (mergedAction parents p n)
          then acc.joinReq rule.require else acc) (mergedAction parents p n).req))) :=
  action?_expand.mpr ⟨⟨a, h⟩, rfl⟩

theorem le_finish (x : Requirements) : x.le (settleGrant (dropMultiGrant x)) :=
  req_le_trans (le_dropMultiGrant x) (le_settleGrant _)

theorem finish_mono {x y : Requirements} (h : x.le y) :
    (settleGrant (dropMultiGrant x)).le (settleGrant (dropMultiGrant y)) :=
  settleGrant_mono (dropMultiGrant_mono h)

theorem ne_nil_of_mem {α : Type} {l : List α} {a : α} (h : a ∈ l) : l ≠ [] := by
  rintro rfl; nomatch h

theorem mem_decls_files {parents : List File2} {leaf : File2} {e : String × LabelDim}
    (he : e ∈ (leaf.policy :: parents.map (·.policy)).flatMap (·.labels)) :
    ∃ f ∈ leaf :: parents, e ∈ f.policy.labels := by
  obtain ⟨f, hf, he⟩ := List.mem_flatMap.mp he
  rcases List.mem_cons.mp hf with rfl | hf
  · exact ⟨leaf, List.mem_cons_self, he⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact ⟨g, List.mem_cons_of_mem _ hg, he⟩

theorem nodup_of_firstDupValue : ∀ l : List String, firstDupValue l = none → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    unfold firstDupValue at h
    by_cases hx : xs.contains x = true
    · simp only [hx, ↓reduceIte, reduceCtorEq] at h
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      exact List.nodup_cons.mpr ⟨by simpa using hx, nodup_of_firstDupValue xs h⟩

theorem no_conflict_of_problems {parents : List File2} {leaf : File2}
    (h : Policy2.problems parents leaf = []) :
    ∀ e ∈ (leaf.policy :: parents.map (·.policy)).flatMap (·.labels),
      ∀ e' ∈ (leaf.policy :: parents.map (·.policy)).flatMap (·.labels), e.1 = e'.1 → e.2 = e'.2 := by
  have hdecl : ∀ {e : String × LabelDim}, e ∈ (leaf.policy :: parents.map (·.policy)).flatMap (·.labels) →
      e ∈ (leaf :: parents).flatMap (·.policy.labels) := by
    intro e he
    obtain ⟨f, hf, he⟩ := mem_decls_files he
    exact List.mem_flatMap.mpr ⟨f, hf, he⟩
  have hfirst : ∀ dim d, (dim, d) ∈ mergedDims (leaf.policy :: parents.map (·.policy)) →
      ∀ o, (dim, o) ∈ (leaf :: parents).flatMap (·.policy.labels) → o = d := by
    intro dim d hd o ho
    by_cases hne : o = d
    · exact hne
    have hp : Problem2.conflictingDimension dim ∈ Policy2.problems parents leaf := by
      unfold Policy2.problems
      rw [List.mem_eraseDups]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ ?_))))))
      refine List.mem_filterMap.mpr ⟨(dim, d), hd, ?_⟩
      have : ((leaf :: parents).flatMap (·.policy.labels)).any
          (fun x => x.1 == dim && x.2 != d) = true :=
        List.any_eq_true.mpr ⟨(dim, o), ho, by simp [hne]⟩
      simp only [this, ↓reduceIte]
    rw [h] at hp
    nomatch hp
  rintro ⟨dim, o⟩ ho ⟨dim', o'⟩ ho' (rfl : dim = dim')
  obtain ⟨d, hd⟩ := exists_mergedDims ho
  rw [hfirst dim d hd o (hdecl ho), hfirst dim d hd o' (hdecl ho')]

theorem nodup_of_problems {parents : List File2} {leaf : File2}
    (h : Policy2.problems parents leaf = []) :
    ∀ d ∈ mergedDims (leaf.policy :: parents.map (·.policy)), d.2.order.Nodup := by
  intro d hd
  obtain ⟨f, hf, hdf⟩ := mem_decls_files (mem_mergedDims hd)
  cases hv : firstDupValue d.2.order with
  | none => exact nodup_of_firstDupValue _ hv
  | some v =>
    have hp : Problem2.duplicateLabelValue f.name d.1 v ∈ Policy2.problems parents leaf := by
      unfold Policy2.problems
      rw [List.mem_eraseDups]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ ?_))))))
      refine List.mem_flatMap.mpr ⟨f, hf, List.mem_filterMap.mpr ⟨d, hdf, ?_⟩⟩
      simp [hv]
    rw [h] at hp
    nomatch hp

end Expand

open Expand

/-- Clause 1, by construction of the layer-2 check: a layer-2 policy (the leaf and the files it
extends) that `Policy2.check` accepts expands to a layer-1 policy that `Policy.check` accepts. -/
theorem expand_check {parents : List File2} {leaf : File2} (h : Policy2.check parents leaf = []) :
    (expand (parents.map (·.policy)) leaf.policy).check = [] := by
  simp only [Policy2.check, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  exact h.2

/-- What `expand` returns: the leaf's policy-level fields, and an action exactly for each name some
file (the leaf or one it extends) writes in `actions`. -/
theorem expand_actions (parents : List Policy2) (p : Policy2) :
    (expand parents p).mode = p.base.mode ∧ (expand parents p).approverRoles = p.base.approverRoles ∧
      (expand parents p).escalationRoles = p.base.escalationRoles ∧
      (expand parents p).meters = p.base.meters ∧ (expand parents p).limits = p.base.limits ∧
      (expand parents p).bindingMutable = p.base.bindingMutable ∧
      (expand parents p).killSetsTombstone = p.base.killSetsTombstone ∧
      ∀ n, (∃ y, (expand parents p).action? n = some y) ↔
        ∃ f ∈ p :: parents, ∃ a, (n, a) ∈ f.actions := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun n => ⟨fun ⟨_, hy⟩ => ?_, fun ⟨f, hf, a, ha⟩ => ?_⟩⟩
  · obtain ⟨⟨a, ha⟩, -⟩ := expand_some hy
    obtain ⟨f, hf, ha⟩ := mem_actionEntries.mp ha
    exact ⟨f, hf, a, ha⟩
  · exact ⟨_, expand_named (mem_actionEntries.mpr ⟨f, hf, ha⟩)⟩

/-- Never weaker than an explicit requirement: every file's entry for an action, the leaf's or one
it extends, is below the expanded action in every field `Requirements.le` compares. -/
theorem expand_explicit {parents : List Policy2} {p f : Policy2} {n : String} {a : Action2}
    (hf : f ∈ p :: parents) (ha : (n, a) ∈ f.actions) :
    ∃ y, (expand parents p).action? n = some y ∧ a.req.le y := by
  have he := mem_actionEntries.mpr ⟨f, hf, ha⟩
  refine ⟨_, expand_named he, req_le_trans ?_ (le_finish _)⟩
  exact req_le_trans (le_explicitReq (List.mem_map_of_mem he)) (rules_ext _ _ _ _)

/-- Never weaker than a matching rule, as `expand` resolves labels: a rule of any file that
matches the labels `expand` resolves for `n` (`labelsOf`) is below the expanded action on every
field it sets (`Require.le`). `Rule.matches` reads only the action's labels, so its requirements
are left empty. The `grantable` dropped when consent needs more than one approval is absent, which
every cap allows. -/
theorem expand_rule_resolved {parents : List Policy2} {p : Policy2} {n : String} {r : Rule}
    {y : Requirements} (hr : r ∈ (p :: parents).flatMap (·.rules))
    (hm : r.matches { labels := mergedDims (p :: parents) } { req := {}, labels := labelsOf parents p n } = true)
    (hy : (expand parents p).action? n = some y) : r.require.le y := by
  obtain ⟨-, rfl⟩ := expand_some hy
  exact require_le_trans (rules_rule _ (mergedAction parents p n) hm _ _ hr) (le_finish _)

/-- Never weaker than a matching rule: a rule of any file that matches an action as any one file
labels it (a missing or unknown label taking its dimension's last value) is below the expanded
action on every field it sets. Assumes each declared order lists no value twice (the JSON codec
refuses a duplicate, and so does `Policy2.problems`; see `expand_rule_checked`): with
`["low", "high", "low"]`, a missing label resolves to the first `"low"`, so a rule on `">=high"`
that matches an action one file labels `"high"` stops matching when another file names it without
a label. -/
theorem expand_rule {parents : List Policy2} {p f : Policy2} {n : String} {a : Action2} {r : Rule}
    (hdims : ∀ d ∈ mergedDims (p :: parents), d.2.order.Nodup)
    (hf : f ∈ p :: parents) (ha : (n, a) ∈ f.actions) (hr : r ∈ (p :: parents).flatMap (·.rules))
    (hm : r.matches { labels := mergedDims (p :: parents) } a = true) :
    ∃ y, (expand parents p).action? n = some y ∧ r.require.le y := by
  have he := mem_actionEntries.mpr ⟨f, hf, ha⟩
  refine ⟨_, expand_named he, expand_rule_resolved hr ?_ (expand_named he)⟩
  refine matches_of (fun dim d hl => ⟨hl, ?_⟩) hm
  have hmem := mem_of_lookup hl
  exact rank_le_merged (nodup_mergedDims _) hmem (hdims _ hmem) (List.mem_map_of_mem he)

/-- Monotone, as `expand` resolves labels: of two actions of one layer-2 policy, if the second's
resolved labels (`labelsOf`) are at or above the first's on every declared dimension and its
explicit requirements, joined across the files that name it, are at least as strict, then its
expansion is at least as strict. No hypothesis on the policy. -/
theorem expand_mono_resolved {parents : List Policy2} {p : Policy2} {n m : String} {x y : Requirements}
    (hlabels : ∀ e ∈ mergedDims (p :: parents),
      labelRank e.2 (labelsOf parents p n) e.1 ≤ labelRank e.2 (labelsOf parents p m) e.1)
    (hreq : (explicitReq ((actionEntries parents p n).map (·.req))).le
      (explicitReq ((actionEntries parents p m).map (·.req))))
    (hx : (expand parents p).action? n = some x) (hy : (expand parents p).action? m = some y) :
    x.le y := by
  obtain ⟨-, rfl⟩ := expand_some hx
  obtain ⟨-, rfl⟩ := expand_some hy
  refine finish_mono (rules_lub _ _ _ _ (req_le_trans hreq (rules_ext _ _ _ _)) fun r hr hm => ?_)
  exact rules_rule _ _ (matches_of (fun dim d hl => ⟨hl, hlabels (dim, d) (mem_of_lookup hl)⟩) hm) _ _ hr

/-- Monotone (spec theorem 13), comparing labels with a missing or unknown label as its dimension's
last value, and explicit requirements by `Requirements.le` (which leaves out `permission` and
`meters`): of two actions `n` and `m` of one layer-2 policy, if on every declared dimension each
file's label for `n` is at or below some file's label for `m`, and `n`'s explicit requirements,
joined across the files that name it, are below `m`'s, then `n`'s expansion is below `m`'s. Assumes
each declared order lists no value twice, as `expand_rule` does and for the same reason. -/
theorem expand_mono {parents : List Policy2} {p : Policy2} {n m : String} {x y : Requirements}
    (hdims : ∀ d ∈ mergedDims (p :: parents), d.2.order.Nodup)
    (hlabels : ∀ e ∈ mergedDims (p :: parents), ∀ a ∈ actionEntries parents p n,
      ∃ b ∈ actionEntries parents p m, labelRank e.2 a.labels e.1 ≤ labelRank e.2 b.labels e.1)
    (hreq : (explicitReq ((actionEntries parents p n).map (·.req))).le
      (explicitReq ((actionEntries parents p m).map (·.req))))
    (hx : (expand parents p).action? n = some x) (hy : (expand parents p).action? m = some y) :
    x.le y := by
  obtain ⟨⟨a₀, ha₀⟩, -⟩ := expand_some hx
  refine expand_mono_resolved (fun e he => ?_) hreq hx hy
  refine merged_le_merged (nodup_mergedDims _) he (nodup_mergedDims _) he (hdims e he)
    (ne_nil_of_mem (List.mem_map_of_mem (f := (·.labels)) ha₀)) fun l hl => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  obtain ⟨b, hb, hle⟩ := hlabels e he a ha
  exact ⟨b.labels, List.mem_map_of_mem hb, hle⟩

/-- Never weaker than a parent (spec theorem 13): expanding any file `q` among the leaf's (one it
extends, or the leaf itself), with any of the leaf's files as `q`'s own (`qs`, for example the files
`q` extends), gives each action something below what the leaf's expansion gives it, so a policy
that extends a baseline can never weaken an action the baseline defines. Assumes no label
dimension is declared with two different orders (a `conflicting_dimension` problem of
`Policy2.problems`): when the leaf reverses a parent's order, the parent's rules on that dimension
stop matching. Also assumes each declared order lists no value twice, as `expand_rule` does. An
action only the leaf names is reached by a parent's rules through `expand_rule`, not this theorem,
which covers the actions the parent's own expansion defines. -/
theorem expand_parent {parents qs : List Policy2} {p q : Policy2} {n : String} {x : Requirements}
    (hq : ∀ f ∈ q :: qs, f ∈ p :: parents)
    (hdims : ∀ d ∈ mergedDims (p :: parents), d.2.order.Nodup)
    (hconf : ∀ e ∈ (p :: parents).flatMap (·.labels), ∀ e' ∈ (p :: parents).flatMap (·.labels),
      e.1 = e'.1 → e.2 = e'.2)
    (hx : (expand qs q).action? n = some x) :
    ∃ y, (expand parents p).action? n = some y ∧ x.le y := by
  obtain ⟨⟨a₀, ha₀⟩, rfl⟩ := expand_some hx
  have hsub : ∀ a ∈ actionEntries qs q n, a ∈ actionEntries parents p n := by
    intro a ha
    obtain ⟨f, hf, ha⟩ := mem_actionEntries.mp ha
    exact mem_actionEntries.mpr ⟨f, hq f hf, ha⟩
  refine ⟨_, expand_named (hsub a₀ ha₀), finish_mono (rules_lub _ _ _ _ ?_ fun r hr hm => ?_)⟩
  · refine req_le_trans (explicitReq_le (ne_nil_of_mem (List.mem_map_of_mem ha₀)) fun r hr => ?_)
      (rules_ext _ _ _ _)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact le_explicitReq (List.mem_map_of_mem (hsub a ha))
  · have hr' : r ∈ (p :: parents).flatMap (·.rules) := by
      obtain ⟨f, hf, hrf⟩ := List.mem_flatMap.mp hr
      exact List.mem_flatMap.mpr ⟨f, hq f hf, hrf⟩
    refine rules_rule _ _ (matches_of (fun dim d hl => ?_) hm) _ _ hr'
    have hmem := mem_of_lookup hl
    have hdecl : (dim, d) ∈ (p :: parents).flatMap (·.labels) := by
      obtain ⟨f, hf, hd⟩ := List.mem_flatMap.mp (mem_mergedDims hmem)
      exact List.mem_flatMap.mpr ⟨f, hq f hf, hd⟩
    obtain ⟨d', hd'⟩ := exists_mergedDims hdecl
    have : d' = d := hconf (dim, d') (mem_mergedDims hd') (dim, d) hdecl rfl
    subst this
    refine ⟨lookup_of_mem (nodup_mergedDims _) hd', ?_⟩
    refine merged_le_merged (nodup_mergedDims _) hmem (nodup_mergedDims _) hd' (hdims _ hd')
      (ne_nil_of_mem (List.mem_map_of_mem (f := (·.labels)) ha₀)) fun l hl => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
    exact ⟨a.labels, List.mem_map_of_mem (hsub a ha), Nat.le_refl _⟩

/-- `expand_rule` for a policy whose layer-2 problems (`Policy2.problems`, the first part of
`Policy2.check`) are none, which rules out a declared order that lists a value twice. -/
theorem expand_rule_checked {parents : List File2} {leaf : File2} {f : Policy2} {n : String}
    {a : Action2} {r : Rule} (hcheck : Policy2.problems parents leaf = [])
    (hf : f ∈ leaf.policy :: parents.map (·.policy)) (ha : (n, a) ∈ f.actions)
    (hr : r ∈ (leaf.policy :: parents.map (·.policy)).flatMap (·.rules))
    (hm : r.matches { labels := mergedDims (leaf.policy :: parents.map (·.policy)) } a = true) :
    ∃ y, (expand (parents.map (·.policy)) leaf.policy).action? n = some y ∧ r.require.le y :=
  expand_rule (nodup_of_problems hcheck) hf ha hr hm

/-- `expand_mono` for a policy whose layer-2 problems are none, which rules out a declared order
that lists a value twice. -/
theorem expand_mono_checked {parents : List File2} {leaf : File2} {n m : String}
    {x y : Requirements} (hcheck : Policy2.problems parents leaf = [])
    (hlabels : ∀ e ∈ mergedDims (leaf.policy :: parents.map (·.policy)),
      ∀ a ∈ actionEntries (parents.map (·.policy)) leaf.policy n,
        ∃ b ∈ actionEntries (parents.map (·.policy)) leaf.policy m,
          labelRank e.2 a.labels e.1 ≤ labelRank e.2 b.labels e.1)
    (hreq : (explicitReq ((actionEntries (parents.map (·.policy)) leaf.policy n).map (·.req))).le
      (explicitReq ((actionEntries (parents.map (·.policy)) leaf.policy m).map (·.req))))
    (hx : (expand (parents.map (·.policy)) leaf.policy).action? n = some x)
    (hy : (expand (parents.map (·.policy)) leaf.policy).action? m = some y) : x.le y :=
  expand_mono (nodup_of_problems hcheck) hlabels hreq hx hy

/-- `expand_parent` for a policy whose layer-2 problems are none, which rules out a dimension
declared with two different orders and a declared order that lists a value twice. -/
theorem expand_parent_checked {parents : List File2} {leaf : File2} {qs : List Policy2} {q : Policy2}
    {n : String} {x : Requirements} (hcheck : Policy2.problems parents leaf = [])
    (hq : ∀ f ∈ q :: qs, f ∈ leaf.policy :: parents.map (·.policy))
    (hx : (expand qs q).action? n = some x) :
    ∃ y, (expand (parents.map (·.policy)) leaf.policy).action? n = some y ∧ x.le y :=
  expand_parent hq (nodup_of_problems hcheck) (no_conflict_of_problems hcheck) hx

namespace Expand

/-! Non-vacuity witnesses: an org baseline and a team policy that extends it and tries to loosen
`files.write` (more grant uses, a lower label). -/

def grant (uses : Nat) : Option Grantable := some ⟨.session, uses, none, false, false⟩

def writeRule : Rule := ⟨[("risk", "write")], { consent := some .perCall }⟩

def baseline : Policy2 where
  labels := [("risk", ⟨["read", "write", "destructive"]⟩)]
  rules := [writeRule,
    ⟨[("risk", "destructive")], { exposed := some false }⟩]
  actions := [("files.read", ⟨{}, [("risk", "read")]⟩),
    ("files.write", ⟨{ grantable := grant 5 }, [("risk", "write")]⟩),
    ("files.wipe", ⟨{}, []⟩)]

def team : Policy2 where
  base := { approverRoles := ["owner"] }
  rules := [⟨[("risk", "write")], { guards := ["audit"] }⟩]
  actions := [("files.write", ⟨{ grantable := grant 10 }, [("risk", "read")]⟩)]

def act (pol : Policy) (n : String) : Requirements := (pol.action? n).getD { maxAttempts := 99 }

def teamExp : Policy := expand [baseline] team

#guard Policy2.check [⟨baseline, {}, "org.json", []⟩] ⟨team, {}, "", []⟩ == []
#guard (teamExp.check).isEmpty
#guard teamExp.actions.map (·.1) == ["files.write", "files.read", "files.wipe"]
#guard teamExp.approverRoles == ["owner"]
#guard act teamExp "files.write" ==
  { consent := .perCall, grantable := grant 5, guards := ["audit"] }
#guard act teamExp "files.wipe" == { consent := .perCall, guards := ["audit"], exposed := false }

/-! `expand_explicit`: the expansion is at least as strict as both files' entries for
`files.write`, and strictly stricter than the team's. -/
#guard decide ((⟨{ grantable := grant 5 }, [("risk", "write")]⟩ : Action2).req.le (act teamExp "files.write"))
#guard decide ((⟨{ grantable := grant 10 }, [("risk", "read")]⟩ : Action2).req.le (act teamExp "files.write"))
#guard !decide ((act teamExp "files.write").le { grantable := grant 10 })

/-! `expand_rule`: the baseline's `>=write` rule matches `files.write` as the baseline labels it,
though not as the team does, and the expansion carries its consent. -/
#guard decide (∀ d ∈ mergedDims [team, baseline], d.2.order.Nodup)
#guard writeRule.matches { labels := mergedDims [team, baseline] } ⟨{}, [("risk", "write")]⟩
#guard !writeRule.matches { labels := mergedDims [team, baseline] } ⟨{}, [("risk", "read")]⟩
#guard decide (writeRule.require.le (act teamExp "files.write"))
#guard !decide (writeRule.require.le { grantable := grant 10 })

/-! `expand_rule_resolved`: the labels `expand` resolves for `files.write` are the baseline's. -/
#guard labelsOf [baseline] team "files.write" == [("risk", "write")]
#guard labelsOf [baseline] team "files.wipe" == [("risk", "destructive")]

/-! `expand_mono` and `expand_mono_resolved`: `files.write` (labels `read` and `write`, grantable)
is below `files.wipe` (unlabeled, so `destructive`; not grantable), and so are their expansions,
strictly. -/
#guard decide (∀ e ∈ mergedDims [team, baseline], ∀ a ∈ actionEntries [baseline] team "files.write",
  ∃ b ∈ actionEntries [baseline] team "files.wipe", labelRank e.2 a.labels e.1 ≤ labelRank e.2 b.labels e.1)
#guard decide (∀ e ∈ mergedDims [team, baseline],
  labelRank e.2 (labelsOf [baseline] team "files.write") e.1 ≤
    labelRank e.2 (labelsOf [baseline] team "files.wipe") e.1)
#guard decide ((explicitReq ((actionEntries [baseline] team "files.write").map (·.req))).le
  (explicitReq ((actionEntries [baseline] team "files.wipe").map (·.req))))
#guard decide ((act teamExp "files.write").le (act teamExp "files.wipe"))
#guard !decide ((act teamExp "files.wipe").le (act teamExp "files.write"))

/-! `expand_parent` and `expand_parent_checked`: the baseline's own expansion of `files.write` is
below the team's, strictly (the team adds a guard), and the policy has no layer-2 problems. -/
#guard decide (∀ e ∈ [team, baseline].flatMap (·.labels), ∀ e' ∈ [team, baseline].flatMap (·.labels),
  e.1 = e'.1 → e.2 = e'.2)
#guard Policy2.problems [⟨baseline, {}, "org.json", []⟩] ⟨team, {}, "", []⟩ == []
#guard act (expand [] baseline) "files.write" == { consent := .perCall, grantable := grant 5 }
#guard decide ((act (expand [] baseline) "files.write").le (act teamExp "files.write"))
#guard !decide ((act teamExp "files.write").le (act (expand [] baseline) "files.write"))

/-! The `_checked` forms: the team policy's layer-2 problems are none, and the files they read are
the same Lean values. -/
def orgFiles : List File2 := [⟨baseline, {}, "org.json", []⟩]
def teamFile : File2 := ⟨team, {}, "", []⟩
#guard Policy2.problems orgFiles teamFile == []
#guard orgFiles.map (·.policy) == [baseline] && teamFile.policy == team

/-! Why `expand_rule` and `expand_mono` assume duplicate-free orders: with `["low", "high", "low"]`
an unlabeled action resolves to the first `"low"`, below `"high"`. `b` is unlabeled, so on every
file's labels it is at or above `a`, and the rule matches `b` as its file labels it, but its
expansion is weaker than `a`'s and than the rule. -/
def highRule : Rule := ⟨[("risk", "high")], { exposed := some false }⟩

def dupOrder : Policy2 where
  labels := [("risk", ⟨["low", "high", "low"]⟩)]
  rules := [highRule]
  actions := [("a", ⟨{}, [("risk", "high")]⟩), ("b", ⟨{}, []⟩)]

#guard decide (∀ e ∈ mergedDims [dupOrder], ∀ a ∈ actionEntries [] dupOrder "a",
  ∃ b ∈ actionEntries [] dupOrder "b", labelRank e.2 a.labels e.1 ≤ labelRank e.2 b.labels e.1)
#guard highRule.matches { labels := mergedDims [dupOrder] } ⟨{}, []⟩
#guard act (expand [] dupOrder) "a" == { exposed := false }
#guard act (expand [] dupOrder) "b" == {}
#guard !decide ((act (expand [] dupOrder) "a").le (act (expand [] dupOrder) "b"))
#guard !decide (highRule.require.le (act (expand [] dupOrder) "b"))
#guard Policy2.problems [] ⟨dupOrder, {}, "", []⟩ == [.duplicateLabelValue "" "risk" "low"]

/-! Why `expand_parent` also assumes duplicate-free orders: the parent labels `a` `high`, the
leaf names `a` without a label, which resolves to the first `"low"`, so the parent's `>=high` rule
no longer matches. No dimension is declared twice. -/
def dupParent : Policy2 where
  labels := [("risk", ⟨["low", "high", "low"]⟩)]
  rules := [highRule]
  actions := [("a", ⟨{}, [("risk", "high")]⟩)]

def dupLeaf : Policy2 where
  actions := [("a", ⟨{}, []⟩)]

#guard decide (∀ e ∈ [dupLeaf, dupParent].flatMap (·.labels),
  ∀ e' ∈ [dupLeaf, dupParent].flatMap (·.labels), e.1 = e'.1 → e.2 = e'.2)
#guard act (expand [] dupParent) "a" == { exposed := false }
#guard act (expand [dupParent] dupLeaf) "a" == {}
#guard !decide ((act (expand [] dupParent) "a").le (act (expand [dupParent] dupLeaf) "a"))

/-! `expand_parent` on a chain: a leaf extends `team`, which extends `org`; expanding `team` with
`org` (q = `team`, qs = [`org`]) gives `files.write` something below the leaf's expansion, which
adds the leaf's cap of two grant uses and, as the leaf names it without a label, the
`>=destructive` rule. -/
def chainLeaf : Policy2 where
  base := { approverRoles := ["owner"] }
  actions := [("files.write", ⟨{ grantable := grant 2 }, []⟩)]

#guard Policy2.problems [⟨team, {}, "team.json", baseline.labels⟩, ⟨baseline, {}, "org.json", []⟩]
  ⟨chainLeaf, {}, "", []⟩ == []
-- `team` labels and rules on `org`'s dimension, so it is checked with the dimensions it inherits.
#guard Policy2.problems [⟨team, {}, "team.json", []⟩, ⟨baseline, {}, "org.json", []⟩] ⟨chainLeaf, {}, "", []⟩ ==
  [.unknownLabelDimension "team.json" "files.write" "risk", .unknownRuleDimension "team.json" 0 "risk"]
#guard act (expand [team, baseline] chainLeaf) "files.write" ==
  { consent := .perCall, grantable := grant 2, guards := ["audit"], exposed := false }
#guard decide ((act (expand [baseline] team) "files.write").le
  (act (expand [team, baseline] chainLeaf) "files.write"))
#guard !decide ((act (expand [team, baseline] chainLeaf) "files.write").le
  (act (expand [baseline] team) "files.write"))

/-! Why `expand_parent` assumes no conflicting dimension: the leaf reverses the parent's order, so
the parent's `>=mid` rule no longer matches `a`, which the parent labels `high`. -/
def ascending : Policy2 where
  labels := [("risk", ⟨["low", "mid", "high"]⟩)]
  rules := [⟨[("risk", "mid")], { exposed := some false }⟩]
  actions := [("a", ⟨{}, [("risk", "high")]⟩)]

def descending : Policy2 where
  labels := [("risk", ⟨["high", "mid", "low"]⟩)]

#guard act (expand [] ascending) "a" == { exposed := false }
#guard act (expand [ascending] descending) "a" == {}
#guard !decide ((act (expand [] ascending) "a").le (act (expand [ascending] descending) "a"))
#guard Policy2.problems [⟨ascending, {}, "org.json", []⟩] ⟨descending, {}, "", []⟩ ==
  [.conflictingDimension "risk"]

end Expand

end Writ.Proofs
