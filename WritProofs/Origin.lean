import WritProofs.Approvals
import WritProofs.Grants

namespace Writ.Proofs

open Writ
open Basic Calls Proofs.Consent Approvals

/-- Section 8, theorems 1 and 12: call `k` was created by an accepted `propose` of tool `t` with
digest `dg`, for an action the policy defines, at a state with no record of `k`. -/
def Proposed (p : Policy) (d : String) (es : List Event) (k t dg : String) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    s₀.calls[k]? = none ∧ (p.action? t).isSome = true ∧
    ∃ cost gs esc, e₀.body = .propose k t dg cost gs esc

/-- Section 8, theorem 12: generation `g` of call `k` of tool `t` has digest `dg` as the events of
the trace carried it. Generation 0 is the digest `k` was proposed with; generation `g + 1` is the
new digest of an accepted approval whose edit answered the request of generation `g`. -/
def GenerationDigest (p : Policy) (d : String) (es : List Event) (k t : String) (g : Nat)
    (dg : String) : Prop :=
  (g = 0 ∧ Proposed p d es k t dg) ∨
    ((∃ dg₀, Proposed p d es k t dg₀) ∧
      ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
        ∃ rid a rd rc x, e₀.body = .approve k rid a rd rc (some x) ∧ rid.generation + 1 = g ∧
          x.newDigest = dg)

/-- Section 8, theorems 1 and 12: record `c` of call `k` holds what events carried. The accepted
`propose` that created it carried its tool, proposed digest and cost, and the escalators its
`proposedEscalators` keeps (those the action defines). A call holding a grant was answered
`allowed_by_grant` with that grant, has the effective consent of that event's escalators and was
never edited. `c.generations` holds one entry per generation, from the proposed digest and cost to
the current ones, and the digest of each entry is that generation's digest. -/
def CallOrigin (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec) : Prop :=
  (∃ s₀ e₀ v₀ r gs esc, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    s₀.calls[k]? = none ∧ p.action? c.tool = some r ∧
    e₀.body = .propose k c.tool c.proposedDigest c.proposedCost gs esc ∧
    c.proposedEscalators = esc.filter (fun x => r.escalate.any (·.1 == x.1)) ∧
    ∀ gid, c.grant = some gid →
      (∃ sh, v₀ = .ok (.allowedByGrant gid) sh) ∧ c.consent = r.effectiveConsent c.cost esc ∧
        c.generation = 0) ∧
  c.generations.length = c.generation + 1 ∧
  c.generations[0]? = some (c.proposedDigest, c.proposedCost) ∧
  c.generations[c.generation]? = some (c.digest, c.cost) ∧
  ∀ g x, c.generations[g]? = some x → GenerationDigest p d es k c.tool g x.1

namespace Origin

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event} {k t dg : String}
  {c c' : CallRec}

/-- The fields of a call record that no step after its `propose` changes. -/
structure Fix (c c' : CallRec) : Prop where
  tool : c'.tool = c.tool
  proposedDigest : c'.proposedDigest = c.proposedDigest
  proposedCost : c'.proposedCost = c.proposedCost
  escalators : c'.proposedEscalators = c.proposedEscalators
  grant : c'.grant = c.grant

/-- The fields `CallOrigin` reads, unchanged. -/
structure Kept (c c' : CallRec) : Prop where
  fix : Fix c c'
  consent : c'.consent = c.consent
  generation : c'.generation = c.generation
  generations : c'.generations = c.generations
  digest : c'.digest = c.digest
  cost : c'.cost = c.cost

theorem Kept.refl : Kept c c := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem kept_of_same (h : RecSame c c') : Kept c c' :=
  ⟨⟨h.tool, h.proposedDigest, h.proposedCost, h.escalators, h.grant⟩, h.consent, h.generation,
    h.generations, h.digest, h.cost⟩

/-- What step `e`, with result `r`, leaves in a call record: one from before it with the fields
`CallOrigin` reads unchanged; one from before it that an accepted approval's edit moved to the
next generation; or a new one made from the step's `propose`. -/
def Moved (p : Policy) (s : State) (e : Event) (r : State × Verdict) : Prop :=
  ∀ (k : String) (c' : CallRec), r.1.calls[k]? = some c' →
    (∃ c, s.calls[k]? = some c ∧ Kept c c') ∨
    (∃ c rid a rd rc x, s.calls[k]? = some c ∧ c.status = .awaiting ∧
      e.body = .approve k rid a rd rc (some x) ∧ rid.generation = c.generation ∧ Fix c c' ∧
      c'.generation = c.generation + 1 ∧ c'.digest = x.newDigest ∧
      c'.generations = c.generations ++ [(x.newDigest, c'.cost)]) ∨
    (s.calls[k]? = none ∧ ∃ rq gs esc, p.action? c'.tool = some rq ∧
      e.body = .propose k c'.tool c'.proposedDigest c'.proposedCost gs esc ∧
      c'.proposedEscalators = esc.filter (fun x => rq.escalate.any (·.1 == x.1)) ∧
      c'.generation = 0 ∧ c'.generations = [(c'.proposedDigest, c'.proposedCost)] ∧
      c'.digest = c'.proposedDigest ∧ c'.cost = c'.proposedCost ∧
      ∀ gid, c'.grant = some gid →
        (∃ sh, r.2 = .ok (.allowedByGrant gid) sh) ∧ c'.consent = rq.effectiveConsent c'.cost esc)

theorem Moved.of_keeps {r : State × Verdict} (h : Keeps s r.1) : Moved p s e r :=
  fun k c' hc => by
    obtain ⟨c, hc₀, hs⟩ := h.calls k c' hc
    exact .inl ⟨c, hc₀, kept_of_same hs⟩

theorem Moved.of_calls {r : State × Verdict} (h : r.1.calls = s.calls) : Moved p s e r :=
  fun _ c' hc => .inl ⟨c', h ▸ hc, .refl⟩

/-- A property of each step's result holds of `stepHandle` once it holds of every result that
keeps `s` or leaves its calls alone, and of every `propose` and `approve` of `e`. -/
theorem stepHandle_of {P : State × Verdict → Prop} (keeps : ∀ r : State × Verdict, Keeps s r.1 → P r)
    (calls : ∀ r : State × Verdict, r.1.calls = s.calls → P r)
    (propose : ∀ {i tool dg cs gs xs}, e.body = .propose i tool dg cs gs xs →
      P (handlePropose p s e.time i tool dg cs gs xs))
    (approve : ∀ {i rid a rd cs ed}, e.body = .approve i rid a rd cs ed →
      P (handleApprove p s e.time i rid a rd cs ed)) :
    P (stepHandle p s e) := by
  unfold Writ.stepHandle
  split <;> rename_i hb
  · exact calls _ sessionStart_calls_eq
  · exact keeps _ handleSessionEnd_kept
  · exact keeps _ handleTurnStart_kept
  · exact keeps _ handleTurnEnd_kept
  · exact keeps _ handleStepStart_kept
  · exact keeps _ handleApproverAttest_kept
  · exact keeps _ handlePermissionRevoke_kept
  · exact propose hb
  · exact approve hb
  · exact keeps _ handleReject_kept
  · exact keeps _ handleApprovalExpire_kept
  · exact calls _ grantCreate_calls_eq
  · exact keeps _ handleGrantRevoke_kept
  · exact keeps _ handleDispatch_kept
  · exact keeps _ handleResult_kept
  · exact keeps _ handleOutcomeUnknown_kept
  · exact keeps _ handleReconcile_kept
  · exact keeps _ handleCancel_kept
  · exact keeps _ handleReset_kept
  · exact keeps _ handleKill_kept
  · exact keeps _ handlePermissionAdd_kept
  · exact keeps _ handleEscalationAck_kept
  · exact keeps _ handleLedgerSync_kept

/-- A property of every record of `m` and of `x` holds of every record of `m.insert i x`. -/
theorem forall_insert {Q : String → CallRec → Prop} {m : Std.ExtTreeMap String CallRec compare}
    {i : String} {x : CallRec} (hm : ∀ k c, m[k]? = some c → Q k c) (hx : Q i x) :
    ∀ k c, (m.insert i x)[k]? = some c → Q k c := by
  intro k c hc
  rw [Std.ExtTreeMap.getElem?_insert] at hc
  split at hc
  · rename_i he
    cases Std.LawfulEqCmp.eq_of_compare he
    cases hc
    exact hx
  · exact hm k c hc

theorem byGrant_shadowed {gid : String} {mode : Mode} :
    (Disposition.allowedByGrant gid).shadowed mode = (.allowedByGrant gid, none) := by
  cases mode <;> rfl

theorem enforceDecision_consent {tm : Nat} {tool dg' : String} {cost : Option Cost}
    {gs es' : List (String × Bool)} {dd : Disposition} {cs : Consent} {r : Requirements}
    (h : enforceDecision p s tm k tool dg' cost gs es' = (dd, cs))
    (hr : p.action? tool = some r) :
    (cs = r.effectiveConsent cost es' ∨ cs = r.consent) ∧
      ((∀ x, dd ≠ .denied x) → cs = r.effectiveConsent cost es') := by
  unfold enforceDecision at h
  simp only [hr, Option.getD_some, Option.isNone_some] at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals cases h
  all_goals first
    | exact ⟨.inl rfl, fun _ => rfl⟩
    | exact ⟨.inr rfl, fun hn => absurd rfl (hn _)⟩
    | contradiction

theorem moved_propose {i tool dg' : String} {cs : Option Cost} {gs xs : List (String × Bool)}
    (hb : e.body = .propose i tool dg' cs gs xs) :
    Moved p s e (handlePropose p s e.time i tool dg' cs gs xs) := by
  unfold handlePropose
  split
  · split <;> exact .of_calls rfl
  · rename_i hk
    split
    rename_i dd cn hd
    split
    · exact .of_calls rfl
    · rename_i r hr
      refine forall_insert (fun _ c' hc' => .inl ⟨c', hc', .refl⟩) (.inr (.inr
        ⟨by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hk, r, gs, xs, hr, hb, rfl, rfl, rfl, rfl,
          rfl, fun gid hg => ?_⟩))
      dsimp only at hg
      have hdd := Grants.shadowed_grant hg
      subst hdd
      refine ⟨⟨none, ?_⟩, (enforceDecision_consent hd hr).2 nofun⟩
      simp only [byGrant_shadowed]
      rfl

theorem applyApprove_record {tm : Nat} {a pr rd : String} {rc : CallRec} {cost : Option Cost}
    {ed : Option Edit} {r : State × Verdict}
    (h : applyApprove p s tm k rc a pr rd cost ed = .ok r) :
    ∃ x, r.1 = { s with calls := s.calls.insert k x } ∧ Fix rc x ∧
      ((ed = none ∧ Kept rc x ∧ x.requestedAt = rc.requestedAt) ∨
        ∃ y, ed = some y ∧ x.generation = rc.generation + 1 ∧ x.digest = y.newDigest ∧
          x.generations = rc.generations ++ [(y.newDigest, x.cost)] ∧ x.requestedAt = tm) ∧
      (x.authorizedAt = rc.authorizedAt ∨
        (x.authorizedAt = some tm ∧ r.2 = .ok .authorized none)) := by
  unfold applyApprove at h
  dsimp only at h
  iterate 5 (split at h; · cases h)
  cases ed with
  | none =>
    dsimp only at h
    split at h <;> cases h
    · exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
        .inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, .inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
        .inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, .inl rfl⟩
  | some y =>
    dsimp only at h
    split at h
    · cases h
    rename_i rec' hn
    have hx : Fix rc rec' ∧ rec'.generation = rc.generation + 1 ∧ rec'.digest = y.newDigest ∧
        rec'.generations = rc.generations ++ [(y.newDigest, rec'.cost)] ∧ rec'.requestedAt = tm ∧
        rec'.authorizedAt = rc.authorizedAt := by
      revert hn
      repeat' split
      all_goals (intro hn; cases hn)
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, h₆, h₇, h₈, h₉, h₁₀⟩ := hx
    split at h <;> cases h
    · exact ⟨_, rfl, ⟨h₁, h₂, h₃, h₄, h₅⟩, .inr ⟨y, rfl, h₆, h₇, h₈, h₉⟩, .inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, rfl, ⟨h₁, h₂, h₃, h₄, h₅⟩, .inr ⟨y, rfl, h₆, h₇, h₈, h₉⟩, .inl h₁₀⟩

theorem moved_approve {i a rd : String} {rid : RequestId} {cs : Option Cost} {ed : Option Edit}
    (hb : e.body = .approve i rid a rd cs ed) :
    Moved p s e (handleApprove p s e.time i rid a rd cs ed) := by
  unfold handleApprove
  split
  · exact .of_calls rfl
  · rename_i rc hck
    have hk := awaitingCheck_ok hck
    have hst := (awaitingCheck_facts hck).1
    have hrid := awaitingCheck_rid hck
    dsimp only
    split
    · exact .of_calls rfl
    · rename_i r hr
      obtain ⟨x, hx, hfix, hor, -⟩ := applyApprove_record hr
      rw [Moved, hx]
      refine forall_insert (fun _ c' hc' => .inl ⟨c', hc', .refl⟩) ?_
      rcases hor with ⟨-, hkept, -⟩ | ⟨y, hy, hg, hd, hgs, -⟩
      · exact .inl ⟨rc, hk, hkept⟩
      · subst hy
        exact .inr (.inl ⟨rc, rid, a, rd, cs, y, hk, hst, hb, by rw [hrid], hfix, hg, hd, hgs⟩)

theorem moved_stepHandle : Moved p s e (stepHandle p s e) :=
  stepHandle_of (fun _ h => .of_keeps h) (fun _ h => .of_calls h) moved_propose moved_approve

theorem proposed_mono (h : Proposed p d es k t dg) : Proposed p d (es ++ [e]) k t dg := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem generation_mono {g : Nat} (h : GenerationDigest p d es k t g dg) :
    GenerationDigest p d (es ++ [e]) k t g dg := by
  rcases h with ⟨hg, hp⟩ | ⟨⟨dg₀, hp⟩, s₀, e₀, v₀, hm, rest⟩
  · exact .inl ⟨hg, proposed_mono hp⟩
  · exact .inr ⟨⟨dg₀, proposed_mono hp⟩, s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem origin_mono (h : CallOrigin p d es k c) : CallOrigin p d (es ++ [e]) k c := by
  obtain ⟨⟨s₀, e₀, v₀, r, gs, esc, hm, rest⟩, hlen, h0, hcur, hgd⟩ := h
  exact ⟨⟨s₀, e₀, v₀, r, gs, esc, trace_mem_snoc hm, rest⟩, hlen, h0, hcur,
    fun g x hx => generation_mono (hgd g x hx)⟩

theorem origin_kept (h : CallOrigin p d es k c) (hk : Kept c c') : CallOrigin p d es k c' := by
  unfold CallOrigin
  rw [hk.fix.tool, hk.fix.proposedDigest, hk.fix.proposedCost, hk.fix.escalators, hk.fix.grant,
    hk.consent, hk.cost, hk.generation, hk.generations, hk.digest]
  exact h

theorem proposed_of (h : CallOrigin p d es k c) : Proposed p d es k c.tool c.proposedDigest := by
  obtain ⟨⟨s₀, e₀, v₀, r, gs, esc, hm, ha, hn, hr, hb, -⟩, -⟩ := h
  exact ⟨s₀, e₀, v₀, hm, ha, hn, by rw [hr]; rfl, _, gs, esc, hb⟩

theorem origin_snoc (ih : ∀ k c, (after p d es).calls[k]? = some c → CallOrigin p d es k c)
    (hc' : (after p d (es ++ [e])).calls[k]? = some c') : CallOrigin p d (es ++ [e]) k c' := by
  rw [after_snoc] at hc'
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at hc'
    exact origin_mono (ih k c' hc')
  have hst := accepted_step ha
  rw [hst] at hc'
  rcases moved_stepHandle (p := p) k c' hc' with ⟨c, hc, hk⟩ |
      ⟨c, rid, a, rd, rc, x, hc, haw, hb, hrid, hfix, hg, hd, hgs⟩ |
      ⟨hn, rq, gs, esc, hr, hb, hesc, hg0, hgs, hd, hcost, hgr⟩
  · exact origin_mono (origin_kept (ih k c hc) hk)
  · have hgn : c.grant = none :=
      (consentInv_reachable (reachable_after (p := p) (d := d) (es := es))).awaiting k c hc haw
    have hoc := ih k c hc
    have hprop := proposed_of hoc
    obtain ⟨⟨s₀, e₀, v₀, r, gs, esc, hm₀, ha₀, hn₀, hr₀, hb₀, hesc₀, -⟩, hlen, h0, -, hgd⟩ := hoc
    refine ⟨⟨s₀, e₀, v₀, r, gs, esc, trace_mem_snoc hm₀, ha₀, hn₀, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [hfix.tool]; exact hr₀
    · rw [hfix.tool, hfix.proposedDigest, hfix.proposedCost]; exact hb₀
    · rw [hfix.escalators]; exact hesc₀
    · intro gid hgid
      rw [hfix.grant, hgn] at hgid
      cases hgid
    · rw [hgs, List.length_append, hlen, hg]; rfl
    · rw [hgs, List.getElem?_append_left (by rw [hlen]; omega), h0, hfix.proposedDigest,
        hfix.proposedCost]
    · rw [hgs, hg, ← hlen, List.getElem?_concat_length, hd]
    · intro g y hy
      rw [hgs] at hy
      rw [hfix.tool]
      by_cases hlt : g < c.generations.length
      · rw [List.getElem?_append_left hlt] at hy
        exact generation_mono (hgd g y hy)
      · have hle := (List.getElem?_eq_some_iff.mp hy).1
        rw [List.length_append, List.length_singleton] at hle
        have hge : g = c.generations.length := by omega
        subst hge
        rw [List.getElem?_concat_length] at hy
        cases hy
        exact .inr ⟨⟨_, proposed_mono hprop⟩, _, _, _, trace_mem_last, ha, rid, a, rd, rc, x, hb,
          by rw [hrid, hlen], rfl⟩
  · refine ⟨⟨after p d es, e, _, rq, gs, esc, trace_mem_last, ha, hn, hr, hb, hesc, fun gid hgid => ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · obtain ⟨⟨sh, hv⟩, hcons⟩ := hgr gid hgid
      refine ⟨⟨sh, ?_⟩, hcons, hg0⟩
      rw [hst]
      exact hv
    · rw [hgs, hg0]; rfl
    · rw [hgs]; rfl
    · rw [hg0, hgs, hd, hcost]; rfl
    · intro g y hy
      rw [hgs] at hy
      cases g with
      | zero =>
        cases hy
        exact .inl ⟨rfl, _, _, _, trace_mem_last, ha, hn, by rw [hr]; rfl, _, gs, esc, hb⟩
      | succ n => simp at hy

end Origin

open Origin

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event} {k t dg : String}
  {c : CallRec}

/-- Section 8, theorems 1 and 12: every call record holds what events carried. Its tool, proposed
digest and cost and kept escalators are those of the accepted `propose` that created it; a call
holding a grant was answered `allowed_by_grant` for it, with the effective consent of that event's
escalators, and never edited; and each entry of its generations, from the proposed digest to the
current one, is the digest the `propose` or an accepted edit carried for that generation. -/
theorem call_origin (hc : (after p d es).calls[k]? = some c) : CallOrigin p d es k c :=
  snoc_induction (P := fun es => ∀ k c, (after p d es).calls[k]? = some c →
    CallOrigin p d es k c) (fun k c h => by simp [after_nil, State.initial] at h)
    (fun _ _ ih _ _ hc' => origin_snoc ih hc') es k c hc

namespace Origin

theorem persist (hc : s.calls[k]? = some c) :
    ∃ c', (step p s e).1.calls[k]? = some c' ∧ Fix c c' ∧
      ∃ l, c'.generations = c.generations ++ l := by
  obtain ⟨c', hc', -⟩ := calls_step_some (p := p) (e := e) hc
  refine ⟨c', hc', ?_⟩
  cases ha : (step p s e).2.accepted
  · rw [frame ha, hc] at hc'
    cases hc'
    exact ⟨Kept.refl.fix, [], by simp⟩
  · rw [accepted_step ha] at hc'
    rcases moved_stepHandle (p := p) k c' hc' with ⟨c₀, h₀, hk⟩ |
        ⟨c₀, -, -, -, -, x, h₀, -, -, -, hfix, -, -, hgs⟩ | ⟨hn, -⟩
    · rw [hc] at h₀; cases h₀
      exact ⟨hk.fix, [], by rw [hk.generations]; simp⟩
    · rw [hc] at h₀; cases h₀
      exact ⟨hfix, _, hgs⟩
    · rw [hc] at hn; cases hn

theorem index_keep {l l' : List (String × Option Cost)} {g : Nat} {x : String}
    (h : (l[g]?.map (·.1)) = some x) : ((l ++ l')[g]?.map (·.1)) = some x := by
  cases hg : l[g]? with
  | none => rw [hg] at h; cases h
  | some y =>
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hg).1, hg]
    rw [hg] at h
    exact h

theorem propose_creates {cost : Option Cost} {gs esc : List (String × Bool)}
    (ha : (step p s e).2.accepted = true) (hb : e.body = .propose k t dg cost gs esc)
    (hk : s.calls[k]? = none) (hr : (p.action? t).isSome = true) :
    ∃ c, (step p s e).1.calls[k]? = some c ∧ c.tool = t ∧ c.proposedDigest = dg := by
  rw [accepted_step ha]
  simp only [stepHandle, hb]
  unfold handlePropose
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  dsimp only
  generalize enforceDecision p s e.time k t dg cost gs esc = dc
  obtain ⟨dd, cs⟩ := dc
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  rw [hr]
  exact ⟨_, Std.ExtTreeMap.getElem?_insert_self, rfl, rfl⟩

theorem proposed_recorded (h : Proposed p d es k t dg) :
    ∃ c, (after p d es).calls[k]? = some c ∧ c.tool = t ∧ c.proposedDigest = dg := by
  refine snoc_induction (P := fun es => Proposed p d es k t dg →
    ∃ c, (after p d es).calls[k]? = some c ∧ c.tool = t ∧ c.proposedDigest = dg)
    (fun ⟨_, _, _, hm, _⟩ => by simp [trace] at hm) ?_ es h
  intro es e ih ⟨s₀, e₀, v₀, hm, ha, hn, hr, cost, gs, esc, hb⟩
  rw [after_snoc]
  rcases trace_mem_snoc_iff.mp hm with hm | hm
  · obtain ⟨c, hc, ht, hd⟩ := ih ⟨s₀, e₀, v₀, hm, ha, hn, hr, cost, gs, esc, hb⟩
    obtain ⟨c', hc', hfix, -⟩ := persist (p := p) (e := e) hc
    exact ⟨c', hc', hfix.tool.trans ht, hfix.proposedDigest.trans hd⟩
  · cases hm
    exact propose_creates ha hb hn hr

theorem edit_step {rid : RequestId} {a rd : String} {rc : Option Cost} {x : Edit}
    (ha : (step p s e).2.accepted = true) (hb : e.body = .approve k rid a rd rc (some x)) :
    ∃ c c', s.calls[k]? = some c ∧ (step p s e).1.calls[k]? = some c' ∧
      rid.generation = c.generation ∧
      c'.generations = c.generations ++ [(x.newDigest, c'.cost)] := by
  have ha' : (stepHandle p s e).2.accepted = true := by
    have h' := ha; rw [accepted_step ha] at h'; exact h'
  rw [accepted_step ha]
  simp only [stepHandle, hb] at ha' ⊢
  revert ha'
  unfold handleApprove
  split
  · intro h; cases h
  · rename_i rc' hck
    have hk := awaitingCheck_ok hck
    have hrid := awaitingCheck_rid hck
    dsimp only
    split
    · intro h; cases h
    · rename_i r hr
      intro _
      obtain ⟨y, hx, -, hor, -⟩ := applyApprove_record hr
      rcases hor with ⟨hn, -⟩ | ⟨z, hz, -, -, hgs, -⟩
      · cases hn
      · cases hz
        refine ⟨rc', y, hk, ?_, by rw [hrid], hgs⟩
        rw [hx]
        exact Std.ExtTreeMap.getElem?_insert_self

theorem edit_recorded {s₀ : State} {e₀ : Event} {v₀ : Verdict} {rid : RequestId} {a rd : String}
    {rc : Option Cost} {x : Edit} (hm : (s₀, e₀, v₀) ∈ trace p (State.initial d) es)
    (ha : v₀.accepted = true) (hb : e₀.body = .approve k rid a rd rc (some x)) :
    ∃ c, (after p d es).calls[k]? = some c ∧
      (c.generations[rid.generation + 1]?.map (·.1)) = some x.newDigest := by
  refine snoc_induction (P := fun es => (s₀, e₀, v₀) ∈ trace p (State.initial d) es →
    ∃ c, (after p d es).calls[k]? = some c ∧
      (c.generations[rid.generation + 1]?.map (·.1)) = some x.newDigest)
    (fun hm => by simp [trace] at hm) ?_ es hm
  intro es e ih hm
  rw [after_snoc]
  rcases trace_mem_snoc_iff.mp hm with hm | hm
  · obtain ⟨c, hc, hx⟩ := ih hm
    obtain ⟨c', hc', -, l, hl⟩ := persist (p := p) (e := e) hc
    exact ⟨c', hc', by rw [hl]; exact index_keep hx⟩
  · cases hm
    obtain ⟨c, c', hc, hc', hrid, hgs⟩ := edit_step ha hb
    obtain ⟨-, hlen, -⟩ := call_origin hc
    refine ⟨c', hc', ?_⟩
    rw [hgs, hrid, ← hlen, List.getElem?_concat_length]
    rfl

end Origin

/-- Section 8, theorem 12: a generation digest the events carried for call `k` of tool `t` is in
the call's record: the call is recorded with tool `t`, and entry `g` of its generations has that
digest. -/
theorem generation_recorded {g : Nat} (h : GenerationDigest p d es k t g dg) :
    ∃ c, (after p d es).calls[k]? = some c ∧ c.tool = t ∧
      (c.generations[g]?.map (·.1)) = some dg := by
  rcases h with ⟨rfl, hp⟩ | ⟨⟨dg₀, hp⟩, s₀, e₀, v₀, hm, ha, rid, a, rd, rc, x, hb, rfl, rfl⟩
  · obtain ⟨c, hc, ht, hd⟩ := proposed_recorded hp
    obtain ⟨-, -, h0, -⟩ := call_origin hc
    exact ⟨c, hc, ht, by rw [h0, hd]; rfl⟩
  · obtain ⟨c, hc, ht, -⟩ := proposed_recorded hp
    obtain ⟨c', hc', hx⟩ := edit_recorded hm ha hb
    rw [hc] at hc'
    cases hc'
    exact ⟨c, hc, ht, hx⟩

end Writ.Proofs
