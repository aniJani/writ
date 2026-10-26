import Writ.Kernel.Eligibility

namespace Writ.Proofs

open Writ

/-- `Forall₂ R l₁ l₂`: the lists have the same length and `R` holds pointwise. Core Lean has no
`List.Forall₂` (it lives in Batteries and Mathlib), so this is the same definition. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

variable {p : Policy} {s : State} {c : Consent} {cl : Clause} {a : String} {info : ApproverInfo}
  {tally : List (String × String)}

/-- `w` is a (principal, approver id) pair. -/
def EligibleFor (p : Policy) (s : State) (cl : Clause) (w : String × String) : Prop :=
  ∃ info, s.approvers[w.2]? = some info ∧ info.principal = w.1 ∧ info.principal ≠ "agent" ∧
    (∃ x ∈ info.roles, x ∈ p.approverRoles) ∧
    (∀ rs, cl.roles = some rs → ∃ x ∈ info.roles, x ∈ rs) ∧
    (cl.humanOnly = true → info.kind = .human) ∧
    (cl.excludeRequester = true → info.principal ≠ s.requester)

def GroupMet (p : Policy) (s : State) (g : Group) (tally : List (String × String)) : Prop :=
  if g.distinct then
    ∃ as : List (String × String), (as.map (·.1)).Nodup ∧
      Forall₂ (fun cl w => w ∈ tally ∧ EligibleFor p s cl w)
        (g.clauses.flatMap fun cl => List.replicate cl.k cl) as
  else
    ∀ cl ∈ g.clauses, ∃ ws : List (String × String), (ws.map (·.1)).Nodup ∧ cl.k ≤ ws.length ∧
      ∀ w ∈ ws, w ∈ tally ∧ EligibleFor p s cl w

def ConsentMet (p : Policy) (s : State) (c : Consent) (tally : List (String × String)) : Prop :=
  ∀ g ∈ c.groups, GroupMet p s g tally

def TallyAttested (s : State) (tally : List (String × String)) : Prop :=
  ∀ w ∈ tally, ∃ info, s.approvers[w.2]? = some info ∧ info.principal = w.1

theorem Forall₂.imp {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hRS _ _ h) (Forall₂.imp hRS t)

theorem Forall₂.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a, R a b
  | _, _, .nil, _, hb => nomatch hb
  | _, _, .cons h t, b, hb => by
    cases hb with
    | head => exact ⟨_, h⟩
    | tail _ hb => exact Forall₂.mem_right t b hb

theorem eligibleFor_sound :
    s.eligibleFor p cl a = true → s.approvers[a]? = some info →
      EligibleFor p s cl (info.principal, a) := by
  intro he hinfo
  unfold State.eligibleFor at he
  rw [Std.ExtTreeMap.get?_eq_getElem?, hinfo] at he
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at he
  obtain ⟨⟨⟨⟨hagent, hroles⟩, hcl⟩, hhuman⟩, hreq⟩ := he
  refine ⟨info, hinfo, rfl, hagent, hroles, ?_, ?_, ?_⟩
  · intro rs hrs
    rw [hrs] at hcl
    simpa using hcl
  · intro h
    rcases hhuman with h' | h'
    · rw [h] at h'; cases h'
    · exact h'
  · intro h
    rcases hreq with h' | h'
    · rw [h] at h'; cases h'
    · exact h'

namespace ConsentMeaning

/-- `f` stands for the kernel's private `State.assign p s`: its unfolding equation holds by `rfl`,
which lets the proof use the definition without naming the private constant (`open private` is
Batteries-only). -/
theorem assign_sound (f : List Clause → List (String × String) → Bool)
    (hstep : ∀ cl rest avail, f (cl :: rest) avail =
      (let principals := (avail.map (·.1)).eraseDups
       let room (c : Clause) :=
         ((avail.filter (s.eligibleFor p c ·.2)).map (·.1)).eraseDups.length ≥ (cl :: rest).count c
       (cl :: rest).length ≤ principals.length && (cl :: rest).all room &&
         principals.any fun who =>
           avail.any (fun (w, a) => w == who && s.eligibleFor p cl a) &&
             f rest (avail.filter (·.1 != who)))) :
    ∀ (slots : List Clause) (avail : List (String × String)), f slots avail = true →
      ∃ as : List (String × String), (as.map (·.1)).Nodup ∧
        Forall₂ (fun cl w => w ∈ avail ∧ s.eligibleFor p cl w.2 = true) slots as := by
  intro slots
  induction slots with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, .nil⟩
  | cons cl rest ih =>
    intro avail h
    rw [hstep] at h
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨_, who, _, ⟨⟨w, a⟩, hwa, hpick⟩, hrest⟩ := h
    simp only [beq_iff_eq] at hpick
    obtain ⟨rfl, helig⟩ := hpick
    obtain ⟨as, hnd, hall⟩ := ih _ hrest
    refine ⟨(w, a) :: as, ?_, .cons ⟨hwa, helig⟩ (hall.imp fun _ x hx => ⟨?_, hx.2⟩)⟩
    · refine List.nodup_cons.mpr ⟨?_, hnd⟩
      intro hmem
      obtain ⟨x, hx, hxw⟩ := List.mem_map.mp hmem
      obtain ⟨_, hxa, _⟩ := hall.mem_right x hx
      have := (List.mem_filter.mp hxa).2
      simp [hxw] at this
    · exact (List.mem_filter.mp hx.1).1

theorem dedup_witness :
    ∀ (L : List (String × String)), ∃ ws : List (String × String),
      (∀ w ∈ ws, w ∈ L) ∧ (ws.map (·.1)).Nodup ∧ ws.length = (L.map (·.1)).eraseDups.length
  | [] => ⟨[], by simp, List.nodup_nil, rfl⟩
  | w :: L => by
    have hlt : (L.filter fun x => !x.1 == w.1).length < L.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ _)
    obtain ⟨ws, hsub, hnd, hlen⟩ := dedup_witness (L.filter fun x => !x.1 == w.1)
    refine ⟨w :: ws, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mp (hsub x hx)).1
    · refine List.nodup_cons.mpr ⟨?_, hnd⟩
      intro hmem
      obtain ⟨x, hx, hxw⟩ := List.mem_map.mp hmem
      have := (List.mem_filter.mp (hsub x hx)).2
      simp [hxw] at this
    · rw [List.map_cons, List.eraseDups_cons, List.length_cons, List.length_cons, hlen,
        List.filter_map]
      rfl
termination_by L => L.length

theorem eligible_of_attested (h : TallyAttested s tally) {w : String × String} (hw : w ∈ tally)
    (he : s.eligibleFor p cl w.2 = true) : EligibleFor p s cl w := by
  obtain ⟨info, hinfo, hprin⟩ := h w hw
  have := eligibleFor_sound he hinfo
  rw [hprin] at this
  exact this

end ConsentMeaning

open ConsentMeaning

theorem satisfied_sound (h : TallyAttested s tally) :
    s.satisfied p c tally = true → ConsentMet p s c tally := by
  intro hs g hg
  unfold State.satisfied at hs
  have hg' := List.all_eq_true.mp hs g hg
  unfold GroupMet
  by_cases hd : g.distinct = true
  · simp only [hd, ite_true] at hg' ⊢
    obtain ⟨as, hnd, hall⟩ := assign_sound _ (fun _ _ _ => rfl) _ _ hg'
    exact ⟨as, hnd, hall.imp fun _ w hw => ⟨hw.1, eligible_of_attested h hw.1 hw.2⟩⟩
  · simp only [hd, Bool.false_eq_true, ite_false] at hg' ⊢
    intro cl hcl
    have hk := List.all_eq_true.mp hg' cl hcl
    simp only [ge_iff_le, decide_eq_true_eq] at hk
    obtain ⟨ws, hsub, hnd, hlen⟩ := dedup_witness (tally.filter (s.eligibleFor p cl ·.2))
    refine ⟨ws, hnd, hlen ▸ hk, fun w hw => ?_⟩
    have hf := List.mem_filter.mp (hsub w hw)
    exact ⟨hf.1, eligible_of_attested h hf.1 hf.2⟩

namespace ConsentMeaning

def wPolicy : Policy where
  approverRoles := ["owner"]

def wApprovers : List (String × ApproverInfo) :=
  [("a1", ⟨"alice", .human, ["owner"]⟩), ("a2", ⟨"alice", .human, ["owner"]⟩),
   ("b1", ⟨"bob", .human, ["owner"]⟩)]

def wState : State where
  expectedPolicyDigest := ""
  requester := "rex"
  approvers := .ofList wApprovers

def wClauses : List Clause := [{ k := 1 }, { k := 1, roles := some ["owner"] }]

def wDistinct : Consent := .allOf wClauses (distinct := true)

def wQuorum2 : Consent := .quorum 2 none true false

def oneAlice : List (String × String) := [("alice", "a1"), ("alice", "a2")]

def aliceBob : List (String × String) := [("alice", "a1"), ("bob", "b1")]

def wAttested (s : State) (tally : List (String × String)) : Bool :=
  tally.all fun w => (s.approvers[w.2]?.map (·.principal)) == some w.1

end ConsentMeaning

#guard wAttested wState oneAlice && wAttested wState aliceBob
#guard wClauses.all fun cl => oneAlice.all fun w => wState.eligibleFor wPolicy cl w.2
#guard !wState.satisfied wPolicy wDistinct oneAlice
#guard wState.satisfied wPolicy wDistinct aliceBob
#guard !wState.satisfied wPolicy wQuorum2 oneAlice
#guard wState.satisfied wPolicy wQuorum2 aliceBob

end Writ.Proofs
