import WritProofs.AtMostOnce
import WritProofs.Approvals
import WritProofs.Grants

namespace Writ.Proofs

open Writ
open Basic Calls Proofs.Consent Approvals

namespace Lifecycle

open AtMostOnce

variable {p : Policy} {d : String} {s s' s₀ s₁ : State} {e : Event} {k i : String}
  {c c' b : CallRec} {q : Prop} {u u' : String → Prop} {st : CallStatus}

/-- What a step may do to a call record: an Unknown record stays Unknown unless `q` (its own
claimed retry) holds, an Open record was Open before in the same epoch, and an `Active` record has
an authorization time. -/
structure Rec (q : Prop) (c c' : CallRec) : Prop where
  unknown : c.status = .unknown → c'.status = .unknown ∨ q
  isOpen : Open c'.status → Open c.status ∧ c'.epoch = c.epoch
  active : Active c'.status →
    c'.authorizedAt.isSome = true ∨ (Active c.status ∧ c'.authorizedAt = c.authorizedAt)

def New (s : State) (c : CallRec) : Prop :=
  (Open c.status → c.epoch = s.epoch) ∧ (Active c.status → c.authorizedAt.isSome = true)

structure Step (u : String → Prop) (s s' : State) : Prop where
  calls : ∀ (k : String) (c' : CallRec), s'.calls[k]? = some c' →
    (∃ c, s.calls[k]? = some c ∧ Rec (u k) c c') ∨ (s.calls[k]? = none ∧ New s' c')
  epoch : ∀ (k : String) (c' : CallRec), s'.calls[k]? = some c' → Open c'.status →
    s'.epoch = s.epoch

theorem Rec.refl : Rec q c c := ⟨.inl, fun h => ⟨h, rfl⟩, fun h => .inr ⟨h, rfl⟩⟩

theorem Rec.trans (h : Rec q c b) (h' : Rec q b c') : Rec q c c' where
  unknown hu := (h.unknown hu).elim h'.unknown .inr
  isOpen ho :=
    have ⟨ho', he'⟩ := h'.isOpen ho
    have ⟨ho'', he''⟩ := h.isOpen ho'
    ⟨ho'', he'.trans he''⟩
  active ha := (h'.active ha).elim .inl fun ⟨ha', he'⟩ =>
    (h.active ha').elim (fun hs => .inl (he' ▸ hs)) fun ⟨ha'', he''⟩ => .inr ⟨ha'', he'.trans he''⟩

theorem Rec.mono (h : Rec q c c') (hq : q → q') : Rec q' c c' :=
  { h with unknown := fun hu => (h.unknown hu).imp_right hq }

theorem Rec.closed (hu : c.status ≠ .unknown) (ho : ¬Open st) (ha : ¬Active st) :
    Rec q c { b with status := st } :=
  ⟨fun h => absurd h hu, fun h => absurd h ho, fun h => absurd h ha⟩

theorem New.rec (h : New s b) (hr : Rec q b c') (he : s'.epoch = s.epoch) : New s' c' :=
  ⟨fun ho => have ⟨ho', he'⟩ := hr.isOpen ho; he'.trans ((h.1 ho').trans he.symm),
   fun ha => (hr.active ha).elim id fun ⟨ha', he'⟩ => he' ▸ h.2 ha'⟩

theorem Step.mono (h : Step u s s') (hu : ∀ k, u k → u' k) : Step u' s s' :=
  ⟨fun k c' hc => (h.calls k c' hc).imp_left fun ⟨c, hk, hr⟩ => ⟨c, hk, hr.mono (hu k)⟩,
   h.epoch⟩

theorem Step.of (hc : s'.calls = s.calls) (he : s'.epoch = s.epoch) : Step u s s' :=
  ⟨fun _ c' h => .inl ⟨c', hc ▸ h, .refl⟩, fun _ _ _ _ => he⟩

theorem Step.refl : Step u s s := .of rfl rfl

theorem Step.congr (h : Step u s s₀) (hc : s₁.calls = s₀.calls) (he : s₁.epoch = s₀.epoch) :
    Step u s s₁ :=
  ⟨fun k c' hc' => by
    rcases h.calls k c' (hc ▸ hc') with h' | ⟨hn, hw⟩
    · exact .inl h'
    · exact .inr ⟨hn, hw.rec (Rec.refl (q := False)) he⟩,
   fun k c' hc' ho => he.trans (h.epoch k c' (hc ▸ hc') ho)⟩

theorem Step.quiet (h : Step u s s₀) (h' : Quiet s₀ s₁) : Step u s s₁ := h.congr h'.calls h'.epoch

theorem Step.insert (hk : s.calls[k]? = some c) (hr : Rec (u k) c c')
    (hc : s'.calls = s.calls.insert k c') (he : s'.epoch = s.epoch) : Step u s s' := by
  refine ⟨fun a x hx => ?_, fun _ _ _ _ => he⟩
  rw [hc, Std.ExtTreeMap.getElem?_insert] at hx
  split at hx
  · rename_i heq
    cases Std.LawfulEqCmp.eq_of_compare heq
    cases hx
    exact .inl ⟨c, hk, hr⟩
  · exact .inl ⟨x, hx, .refl⟩

theorem Step.fresh (hk : s.calls[k]? = none) (hn : New s' c')
    (hc : s'.calls = s.calls.insert k c') (he : s'.epoch = s.epoch) : Step u s s' := by
  refine ⟨fun a x hx => ?_, fun _ _ _ _ => he⟩
  rw [hc, Std.ExtTreeMap.getElem?_insert] at hx
  split at hx
  · rename_i heq
    cases Std.LawfulEqCmp.eq_of_compare heq
    cases hx
    exact .inr ⟨hk, hn⟩
  · exact .inl ⟨x, hx, .refl⟩

theorem Step.endCall (h : Step u s₀ s) (hk : s₀.calls[k]? = some c) (hu : c.status ≠ .unknown)
    (ho : ¬Open st) (ha : ¬Active st) : Step u s₀ (s.endCall k st) := by
  unfold State.endCall
  dsimp only
  refine ⟨fun a x hx => ?_, fun a x hx hox => ?_⟩
  · rw [Std.ExtTreeMap.getElem?_modify, releaseGrant_calls] at hx
    split at hx
    · rename_i heq
      cases Std.LawfulEqCmp.eq_of_compare heq
      cases hb : s.calls[k]? with
      | none => rw [hb] at hx; cases hx
      | some b =>
        rw [hb] at hx
        cases hx
        exact .inl ⟨c, hk, .closed hu ho ha⟩
    · rcases h.calls a x hx with h' | ⟨hn, hw⟩
      · exact .inl h'
      · exact .inr ⟨hn, hw.rec (Rec.refl (q := False)) releaseGrant_quiet.epoch⟩
  · rw [Std.ExtTreeMap.getElem?_modify, releaseGrant_calls] at hx
    rw [releaseGrant_quiet.epoch]
    split at hx
    · cases hb : s.calls[k]? with
      | none => rw [hb] at hx; cases hx
      | some b => rw [hb] at hx; cases hx; exact absurd hox ho
    · exact h.epoch a x hx hox

theorem Step.map {f : String → CallRec → CallRec} (h : Step u s₀ s)
    (hf : ∀ k b, Rec (u k) b (f k b)) (hc : s'.calls = s.calls.map f) (he : s'.epoch = s.epoch)
    (hn : ∀ k b, Open (f k b).status → Open b.status) : Step u s₀ s' := by
  refine ⟨fun a x hx => ?_, fun a x hx hox => ?_⟩
  · rw [hc, Std.ExtTreeMap.getElem?_map] at hx
    cases hb : s.calls[a]? with
    | none => rw [hb] at hx; cases hx
    | some b =>
      rw [hb] at hx
      cases hx
      rcases h.calls a b hb with ⟨c, hk, hr⟩ | ⟨hk, hw⟩
      · exact .inl ⟨c, hk, hr.trans (hf a b)⟩
      · exact .inr ⟨hk, hw.rec (hf a b) he⟩
  · rw [hc, Std.ExtTreeMap.getElem?_map] at hx
    cases hb : s.calls[a]? with
    | none => rw [hb] at hx; cases hx
    | some b =>
      rw [hb] at hx
      cases hx
      exact he.trans (h.epoch a b hb (hn a b hox))

theorem not_open_cancelled : ¬Open .cancelled := by simp [Open]

theorem not_active_cancelled : ¬Active .cancelled := by simp [Active]

theorem cancelPending_step : Step u s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant_mem (Step u s) _ ?_ _ .refl
  intro acc ⟨k, c⟩ hm ha
  have hk := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm
  dsimp only
  split <;> rename_i hs
  · exact ha.endCall hk (by rw [hs]; nofun) not_open_cancelled not_active_cancelled
  · exact ha.endCall hk (by rw [hs]; nofun) not_open_cancelled not_active_cancelled
  · exact ha

/-- No Open record survives `cancelPending`; the keys of `toList` are distinct, so each one is
ended once and never touched again. -/
theorem fold_closed {f : State → String × CallRec → State}
    (hf : ∀ (acc : State) (x : String × CallRec), acc.calls[x.1]? = some x.2 →
      (∀ c : CallRec, (f acc x).calls[x.1]? = some c → ¬Open c.status) ∧
        ∀ a, a ≠ x.1 → (f acc x).calls[a]? = acc.calls[a]?) :
    ∀ (L : List (String × CallRec)), L.Pairwise (fun a b => a.1 ≠ b.1) → ∀ acc : State,
      (∀ x ∈ L, acc.calls[x.1]? = some x.2) →
      (∀ (k : String) (c : CallRec), acc.calls[k]? = some c → Open c.status → ∃ x ∈ L, x.1 = k) →
      ∀ (k : String) (c : CallRec), (L.foldl f acc).calls[k]? = some c → ¬Open c.status
  | [], _, acc, _, ho, k, c, hk, hc => by
    obtain ⟨_, hx, _⟩ := ho k c hk hc
    cases hx
  | x :: L, hL, acc, hg, ho, k, c, hk, hc => by
    obtain ⟨hx, hne⟩ := hf acc x (hg x List.mem_cons_self)
    have hp := List.pairwise_cons.mp hL
    refine fold_closed hf L hp.2 (f acc x) (fun y hy => ?_) (fun a c' ha hca => ?_) k c hk hc
    · rw [hne y.1 fun he => hp.1 y hy he.symm]
      exact hg y (List.mem_cons_of_mem _ hy)
    · by_cases hax : a = x.1
      · subst hax; exact absurd hca (hx c' ha)
      · rw [hne a hax] at ha
        obtain ⟨y, hy, hya⟩ := ho a c' ha hca
        rcases List.mem_cons.mp hy with hy | hy
        · subst hy; exact absurd hya.symm hax
        · exact ⟨y, hy, hya⟩

theorem cancelPending_closed :
    ∀ (k : String) (c : CallRec), (cancelPending s).calls[k]? = some c → ¬Open c.status := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine fold_closed ?_ _ distinct_toList s toList_get
    fun k c hk _ => ⟨(k, c), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, rfl⟩
  intro acc ⟨k, c⟩ hk
  dsimp only at hk ⊢
  split <;> rename_i hs
  · refine ⟨fun c' hc' => ?_, fun a ha => Grants.endCall_ne ha⟩
    unfold State.endCall at hc'
    dsimp only at hc'
    rw [Std.ExtTreeMap.getElem?_modify_self, releaseGrant_calls, hk] at hc'
    cases hc'
    exact not_open_cancelled
  · refine ⟨fun c' hc' => ?_, fun a ha => Grants.endCall_ne ha⟩
    unfold State.endCall at hc'
    dsimp only at hc'
    rw [Std.ExtTreeMap.getElem?_modify_self, releaseGrant_calls, hk] at hc'
    cases hc'
    exact not_open_cancelled
  · refine ⟨fun c' hc' => ?_, fun _ _ => rfl⟩
    rw [hk] at hc'
    cases hc'
    rintro (h | h) <;> simp_all

def unknownIfDispatched (c : CallRec) : CallRec :=
  if c.status = .dispatched then { c with status := .unknown } else c

theorem unknownIfDispatched_rec : Rec q b (unknownIfDispatched b) := by
  unfold unknownIfDispatched
  split
  · rename_i hd
    exact ⟨fun hu => (by rw [hd] at hu; cases hu), fun ho => (by rcases ho with h | h <;> cases h),
      fun _ => .inr ⟨.inr (.inl hd), rfl⟩⟩
  · exact .refl

theorem unknownIfDispatched_open (h : Open (unknownIfDispatched b).status) : Open b.status := by
  unfold unknownIfDispatched at h
  split at h
  · rcases h with h | h <;> cases h
  · exact h

theorem interrupt_step : Step u s s.interrupt := by
  unfold State.interrupt
  exact cancelPending_step.map (fun _ _ => unknownIfDispatched_rec) rfl rfl
    fun _ _ => unknownIfDispatched_open

theorem interrupt_closed :
    ∀ (k : String) (c : CallRec), s.interrupt.calls[k]? = some c → ¬Open c.status := by
  intro k c hk ho
  unfold State.interrupt at hk
  dsimp only at hk
  rw [Std.ExtTreeMap.getElem?_map] at hk
  cases hb : (cancelPending s).calls[k]? with
  | none => rw [hb] at hk; cases hk
  | some b =>
    rw [hb] at hk
    cases hk
    exact cancelPending_closed k b hb (unknownIfDispatched_open ho)

local macro "life" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Step.refl
      | exact Step.of rfl rfl
      | exact cancelPending_step.congr rfl rfl
      | exact interrupt_step.congr rfl rfl)

theorem handleSessionStart_life : Step u s (handleSessionStart s i a y ps as l).1 := by
  unfold handleSessionStart; life

theorem handleSessionEnd_life : Step u s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; life

theorem handleTurnStart_life : Step u s (handleTurnStart s x).1 := by
  unfold handleTurnStart; life

theorem handleTurnEnd_life : Step u s (handleTurnEnd s).1 := by
  unfold handleTurnEnd; life

theorem handleStepStart_life : Step u s (handleStepStart p s).1 := by
  unfold handleStepStart; life

theorem handleApproverAttest_life : Step u s (handleApproverAttest s a ai).1 := by
  unfold handleApproverAttest; life

theorem handlePermissionRevoke_life : Step u s (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; life

theorem handleGrantCreate_life :
    Step u s (handleGrantCreate p s n i a y dg sc mu mc nb ex rv).1 := by
  unfold handleGrantCreate; life

theorem handleGrantRevoke_life : Step u s (handleGrantRevoke s i).1 := by
  unfold handleGrantRevoke; life

theorem handlePermissionAdd_life : Step u s (handlePermissionAdd p s a y).1 := by
  unfold handlePermissionAdd; life

theorem handleEscalationAck_life : Step u s (handleEscalationAck p s a n).1 := by
  unfold handleEscalationAck; life

theorem handleKill_life : Step u s (handleKill p s).1 := by
  unfold handleKill; life

theorem handleLedgerSync_life : Step u s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; life

theorem handleReset_life : Step u s (handleReset s).1 := by
  unfold handleReset
  dsimp only
  refine ⟨fun k c' hk => ?_, fun k c hk ho => absurd ho (interrupt_closed k c hk)⟩
  rcases interrupt_step.calls k c' hk with h | ⟨hn, hw⟩
  · exact .inl h
  · exact .inr ⟨hn, fun ho => absurd ho (interrupt_closed k c' hk), hw.2⟩

theorem handleCancel_life : Step u s (handleCancel s i).1 := by
  unfold handleCancel
  split
  · exact Step.refl
  · rename_i rc hrc
    split <;> rename_i hs
    · exact Step.refl.endCall (get?_some hrc) (by rw [hs]; nofun) not_open_cancelled
        not_active_cancelled
    · exact Step.refl.endCall (get?_some hrc) (by rw [hs]; nofun) not_open_cancelled
        not_active_cancelled
    · exact Step.refl

theorem callCheck_spec (h : callCheck s k rid = .ok c) :
    s.calls[k]? = some c ∧ c.status = .awaiting ∧ rid = ⟨s.sessionId, k, c.generation⟩ ∧
      c.epoch = s.epoch := by
  unfold callCheck at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hrc hst hn
       simp only [ne_eq, not_or, Classical.not_not] at hst hn
       exact ⟨get?_some hrc, hst, hn⟩)

theorem awaitingCheck_spec (h : awaitingCheck p s k rid a = .ok c) :
    s.calls[k]? = some c ∧ c.status = .awaiting ∧ rid = ⟨s.sessionId, k, c.generation⟩ ∧
      c.epoch = s.epoch := by
  unfold awaitingCheck at h
  cases hc : callCheck s k rid with
  | error => simp [hc, bind, Except.bind] at h
  | ok rc' =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    · cases h; exact callCheck_spec hc

theorem vetoCheck_open (h : vetoCheck p s k rid a = .ok c) :
    s.calls[k]? = some c ∧ c.status ≠ .unknown := by
  unfold vetoCheck at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rename_i hrc hst _ _
       refine ⟨get?_some hrc, fun hu => hst ?_⟩
       simp [hu])

theorem handleReject_life : Step u s (handleReject p s i rid a).1 := by
  unfold handleReject
  split
  · exact Step.refl
  · rename_i rc hv
    obtain ⟨hk, hu⟩ := vetoCheck_open hv
    exact (Step.refl.endCall hk hu (by simp [Open]) (by simp [Active])).congr rfl rfl

theorem handleApprovalExpire_life : Step u s (handleApprovalExpire s i rid).1 := by
  unfold handleApprovalExpire
  split
  · exact Step.refl
  · rename_i rc hv
    obtain ⟨hk, hs, -⟩ := callCheck_spec hv
    exact Step.refl.endCall hk (by rw [hs]; nofun) (by simp [Open]) (by simp [Active])

theorem applyApprove_life (hk : s.calls[i]? = some c) (hs : c.status = .awaiting)
    (ha : applyApprove p s t i c w pr dg cs ed = .ok r) : Step u s r.1 := by
  unfold applyApprove at ha
  repeat' (first | (dsimp only at ha) | split at ha)
  all_goals first
    | cases ha; done
    | (cases ha
       rename_i rc' hn _
       have hf : rc'.status = c.status ∧ rc'.epoch = c.epoch := by
         revert hn
         repeat' split
         all_goals (intro hn; cases hn <;> exact ⟨rfl, rfl⟩)
       refine Step.insert hk ⟨fun hu => ?_, fun _ => ?_, fun hx => ?_⟩ rfl rfl
       all_goals first
         | (rw [hs] at hu; cases hu)
         | exact ⟨.inl hs, hf.2⟩
         | exact .inl rfl
         | (rw [hf.1, hs] at hx; rcases hx with h | h | h <;> cases h))

theorem handleApprove_life : Step u s (handleApprove p s t i rid w dg cs ed).1 := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact Step.refl
    | (rename_i hck _ _ ha
       obtain ⟨hk, hs, -⟩ := awaitingCheck_spec hck
       exact applyApprove_life hk hs ha)

theorem handlePropose_life : Step u s (handlePropose p s t k tool dg cs gs xs).1 := by
  unfold handlePropose
  split
  · split <;> exact Step.refl
  · rename_i hk
    split
    split
    · exact Step.of rfl rfl
    · dsimp only
      refine Step.fresh (get?_none hk) ⟨fun _ => rfl, fun ha => ?_⟩ rfl rfl
      dsimp only at ha ⊢
      split
      · rfl
      · rename_i hn
        rcases ha with h | h | h
        · exact absurd h hn
        all_goals
          revert h
          generalize Disposition.shadowed _ _ = x
          obtain ⟨x, _⟩ := x
          cases x <;> simp [Disposition.status]

theorem outcome_closed (o : Outcome) : ¬Open o.status ∧ ¬Active o.status := by
  cases o <;> simp [Open, Active, Outcome.status]

theorem handleResult_life : Step u s (handleResult p s t i o a ne).1 := by
  unfold handleResult
  split
  · exact Step.refl
  · rename_i rc hrc
    split
    · exact Step.refl
    · rename_i hd
      have hu : rc.status ≠ .unknown := fun hu => hd (by rw [hu]; nofun)
      have h₁ : Step u s ((withStatus s i rc o.status).settle p (callMeters p rc) i o a ne t).1 :=
        (Step.insert (s' := withStatus s i rc o.status) (get?_some hrc)
          (.closed hu (outcome_closed o).1 (outcome_closed o).2) rfl rfl).quiet settle_quiet
      repeat' (first | (dsimp only) | split)
      all_goals first
        | exact h₁.quiet recordFailure_quiet
        | exact h₁.congr rfl rfl

theorem handleOutcomeUnknown_life : Step u s (handleOutcomeUnknown p s i).1 := by
  unfold handleOutcomeUnknown
  split
  · exact Step.refl
  · rename_i rc hrc
    split
    · exact Step.refl
    · rename_i hd
      have hd' : rc.status = .dispatched := Classical.not_not.mp hd
      refine (Step.insert (s' := withStatus s i rc .unknown) (get?_some hrc)
        ⟨fun hu => ?_, fun ho => ?_, fun _ => ?_⟩ rfl rfl).quiet recordFailure_quiet
      · rw [hd'] at hu; cases hu
      · rcases ho with h | h <;> cases h
      · exact .inr ⟨.inr (.inl hd'), rfl⟩

theorem handleReconcile_life : Step u s (handleReconcile p s t i o a ne).1 := by
  unfold handleReconcile
  split
  · exact Step.refl
  · rename_i rc hrc
    split
    · exact Step.refl
    · split
      · exact Step.refl
      · have h₁ : Step u s { s with calls := s.calls.insert i { rc with reconciled := some o } } :=
          Step.insert (c' := { rc with reconciled := some o }) (get?_some hrc)
            ⟨.inl, fun h => ⟨h, rfl⟩, fun h => .inr ⟨h, rfl⟩⟩ rfl rfl
        repeat' (first | (dsimp only) | split)
        all_goals first
          | exact (h₁.quiet settle_quiet).quiet recordFailure_quiet
          | exact h₁.quiet settle_quiet

theorem claim_life (hk : s.calls[i]? = some c)
    (hs : c.status = .authorized ∨ c.status = .unknown) (hq : c.status = .unknown → u i) :
    Step u s (claim p s t i c r retry key) := by
  obtain ⟨hc, he, -⟩ := claim_state (p := p) (s := s) (t := t) (k := i) (rc := c) (r := r)
    (retry := retry) (key := key)
  refine Step.insert hk ⟨fun hu => .inr (hq hu), fun ho => ?_, fun _ => ?_⟩ hc he
  · rcases ho with h | h <;> cases h
  · exact .inr ⟨hs.elim .inl (.inr ∘ .inr), rfl⟩

theorem closed_not_open (h : Closed st) : ¬Open st := fun ho => ho.elim h.2 (h.1 ∘ .inl)

theorem handleDispatch_unclaimed (h : (handleDispatch p s t i n dg cs g key).2.claimed = false) :
    Step u s (handleDispatch p s t i n dg cs g key).1 := by
  rcases Dispatch.handle_unclaimed h with he | ⟨c, st, hk, ha, hst, he⟩ <;> rw [he]
  · exact Step.refl
  · have hc := closed_of_denial hst
    exact Step.refl.endCall hk (by rw [ha]; nofun) (closed_not_open hc) hc.1

theorem handleDispatch_claimed (h : (handleDispatch p s t i n dg cs g key).2.claimed = true) :
    Step (· = i) s (handleDispatch p s t i n dg cs g key).1 := by
  obtain ⟨c, hk, hs, -⟩ := Dispatch.handle_claimed.mp h
  rw [Dispatch.handle_post h hk]
  exact claim_life hk (Dispatch.stage_active hs) fun _ => rfl

theorem handleDispatch_life :
    Step (fun k => k = i ∧ (handleDispatch p s t i n dg cs g key).2.claimed = true) s
      (handleDispatch p s t i n dg cs g key).1 := by
  cases h : (handleDispatch p s t i n dg cs g key).2.claimed
  · exact (handleDispatch_unclaimed (u := fun _ => False) h).mono fun _ h => h.elim
  · exact (handleDispatch_claimed h).mono fun _ hk => ⟨hk, rfl⟩

theorem stepHandle_life :
    Step (fun k => e.body.dispatchOf k = true ∧ (stepHandle p s e).2.claimed = true) s
      (stepHandle p s e).1 := by
  unfold stepHandle
  split <;> rename_i hb
  all_goals first
    | (refine handleDispatch_life.mono fun k ⟨hk, hc⟩ => ⟨?_, hc⟩
       subst hk; simp [EventBody.dispatchOf, hb])
    | with_reducible exact handleSessionStart_life
    | with_reducible exact handleSessionEnd_life
    | with_reducible exact handleTurnStart_life
    | with_reducible exact handleTurnEnd_life
    | with_reducible exact handleStepStart_life
    | with_reducible exact handleApproverAttest_life
    | with_reducible exact handlePermissionRevoke_life
    | with_reducible exact handlePropose_life
    | with_reducible exact handleApprove_life
    | with_reducible exact handleReject_life
    | with_reducible exact handleApprovalExpire_life
    | with_reducible exact handleGrantCreate_life
    | with_reducible exact handleGrantRevoke_life
    | with_reducible exact handleResult_life
    | with_reducible exact handleOutcomeUnknown_life
    | with_reducible exact handleReconcile_life
    | with_reducible exact handleCancel_life
    | with_reducible exact handleReset_life
    | with_reducible exact handleKill_life
    | with_reducible exact handlePermissionAdd_life
    | with_reducible exact handleEscalationAck_life
    | with_reducible exact handleLedgerSync_life

theorem step_life :
    Step (fun k => e.body.dispatchOf k = true ∧ (step p s e).2.claimed = true) s
      (step p s e).1 := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact Step.refl
  · rw [accepted_step ha]
    exact stepHandle_life.congr rfl rfl

/-- Section 8, theorem 6's epoch and authorized-TTL invariant: an Open call is of the current
epoch (a reset cancels the others), and an Active call has its authorization time. -/
structure Inv (s : State) : Prop where
  epoch : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → Open c.status → c.epoch = s.epoch
  auth : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → Active c.status →
    c.authorizedAt.isSome = true

theorem Inv.step (h : Inv s) (hs : Step u s s') : Inv s' := by
  refine ⟨fun k c' hk ho => ?_, fun k c' hk ha => ?_⟩
  · rcases hs.calls k c' hk with ⟨c, hc, hr⟩ | ⟨-, hn⟩
    · have ⟨ho', he⟩ := hr.isOpen ho
      rw [he, h.epoch k c hc ho', hs.epoch k c' hk ho]
    · exact hn.1 ho
  · rcases hs.calls k c' hk with ⟨c, hc, hr⟩ | ⟨-, hn⟩
    · rcases hr.active ha with h' | ⟨ha', he⟩
      · exact h'
      · rw [he]; exact h.auth k c hc ha'
    · exact hn.2 ha

theorem Inv.reachable (hr : Reachable p d s) : Inv s := by
  induction hr with
  | init =>
    exact ⟨fun _ _ h => by simp [State.initial] at h, fun _ _ h => by simp [State.initial] at h⟩
  | step _ ih => exact ih.step step_life

theorem dispatchOf_body {b : EventBody} (h : b.dispatchOf k = true) :
    ∃ n dg cost g key, b = .dispatch k n dg cost g key := by
  cases b <;> simp_all [EventBody.dispatchOf]

end Lifecycle

open Lifecycle

variable {p : Policy} {d : String} {s : State} {e : Event} {k : String} {c c' : CallRec}

/-- Section 8, theorem 5: a terminal status stays, except that a claimed retry of the call takes an
Unknown call back to Dispatched. With `calls_keep`, a terminal call is never removed. -/
theorem terminal_absorbing (hc : s.calls[k]? = some c) (ht : c.status.terminal = true)
    (hc' : (step p s e).1.calls[k]? = some c') :
    c'.status = c.status ∨ (c.status = .unknown ∧ c'.status = .dispatched ∧
      (step p s e).2.claimed = true ∧ e.body.dispatchOf k = true) := by
  by_cases hu : c.status = .unknown
  · rcases step_life.calls k c' hc' with ⟨c₀, h₀, hr⟩ | ⟨h₀, -⟩
    · rw [hc] at h₀
      cases h₀
      rcases hr.unknown hu with h | ⟨hd, hcl⟩
      · exact .inl (h.trans hu.symm)
      · obtain ⟨n, dg, cost, g, key, hb⟩ := dispatchOf_body hd
        rw [claim_post hcl hb hc] at hc'
        dsimp only at hc'
        rw [(AtMostOnce.claim_state (p := p)).1, Std.ExtTreeMap.getElem?_insert_self] at hc'
        cases hc'
        exact .inr ⟨hu, rfl, hcl, hd⟩
    · rw [hc] at h₀; cases h₀
  · exact .inl (calls_terminal hc ht hu hc')

/-- Section 8, theorem 6: a claimed dispatch, first attempt or retry, uses a call of the current
epoch. -/
theorem claim_epoch {n : Nat} {dg key : String} {cost : Option Cost} {g : List (String × Bool)}
    (hr : Reachable p d s) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c) :
    c.epoch = s.epoch := by
  obtain ⟨-, c₀, h₀, hp, -⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at h₀
  cases h₀
  rcases hp.1 with ha | hu
  · exact (Inv.reachable hr).epoch k c hc (.inr ha)
  · exact (hp.2.1 hu).2.2.1

/-- Section 8, theorem 6: an accepted `approve` answers the current request of an Awaiting call of
the current epoch, within the action's approval TTL. -/
theorem approve_fresh {rid : RequestId} {a dg : String} {cost : Option Cost} {ed : Option Edit}
    (h : (step p s e).2.accepted = true) (he : e.body = .approve k rid a dg cost ed) :
    ∃ c, s.calls[k]? = some c ∧ c.status = .awaiting ∧ rid = ⟨s.sessionId, k, c.generation⟩ ∧
      c.epoch = s.epoch ∧
      ∀ ttl, p.approvalTtl ((p.action? c.tool).getD {}) = some ttl →
        e.time < c.requestedAt + ttl := by
  have hh := (Dispatch.step_accepted_iff.mp h).2
  simp only [stepHandle, he] at hh
  unfold handleApprove at hh
  split at hh
  · simp [Verdict.accepted] at hh
  · rename_i rc hck
    dsimp only at hh
    split at hh
    · simp [Verdict.accepted] at hh
    · rename_i r har
      obtain ⟨hk, hs, hrid, hep⟩ := awaitingCheck_spec hck
      obtain ⟨-, -, -, httl, -⟩ := applyApprove_spec har
      exact ⟨rc, hk, hs, hrid, hep, httl⟩

/-- Section 8, theorem 6: a claimed dispatch of an enforced action, first attempt or retry, falls
inside the action's authorized TTL from the call's authorization time. -/
theorem claim_authorized_ttl {n ttl : Nat} {dg key : String} {cost : Option Cost}
    {g : List (String × Bool)} {r : Requirements}
    (hr : Reachable p d s) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hra : p.action? c.tool = some r)
    (ht : p.authorizedTtl r = some ttl) :
    ∃ t₀, c.authorizedAt = some t₀ ∧ e.time < t₀ + ttl := by
  obtain ⟨-, c₀, h₀, hp, ha⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at h₀
  cases h₀
  have hl := (ha hm).1.1 ttl (by rw [hra, Option.getD_some]; exact ht)
  have hs := (Inv.reachable hr).auth k c hc (hp.1.elim .inl (.inr ∘ .inr))
  cases hat : c.authorizedAt with
  | none => rw [hat] at hs; cases hs
  | some t₀ => rw [hat, Option.getD_some] at hl; exact ⟨t₀, rfl, hl⟩

/-- Section 8, theorem 6: a claimed dispatch, first attempt or retry, moves the call to
Dispatched and leaves its authorization time as it was, so a retry's authorized TTL still runs
from the original authorization. -/
theorem claim_keeps_authorizedAt {n : Nat} {dg key : String} {cost : Option Cost}
    {g : List (String × Bool)} (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c) :
    ∃ c', (step p s e).1.calls[k]? = some c' ∧ c'.status = .dispatched ∧
      c'.authorizedAt = c.authorizedAt := by
  rw [claim_post h he hc]
  refine ⟨{ c with
    status := .dispatched, attempts := c.attempts + 1, idempotencyKey := some key }, ?_, rfl, rfl⟩
  rw [(AtMostOnce.claim_state (p := p)).1, Std.ExtTreeMap.getElem?_insert_self]

/-- Section 8, theorem 6: no step moves the authorization time of a call that is no longer
Awaiting; only the approval or propose that authorizes a call sets it. -/
theorem authorizedAt_kept {c' : CallRec} (hc : s.calls[k]? = some c) (hst : c.status ≠ .awaiting)
    (hc' : (step p s e).1.calls[k]? = some c') : c'.authorizedAt = c.authorizedAt := by
  rcases Approvals.old_step k c c' hc hc' with hs | ⟨hw, -⟩
  · exact hs.authorizedAt
  · exact absurd hw hst

namespace Lifecycle

open AtMostOnce Dispatch

def statusOf (s : State) (k : String) : Option CallStatus := s.calls[k]?.map (·.status)

#guard statusOf (after retryPolicy "pd" retryUnknown) "c1" == some .unknown
#guard (step retryPolicy (after retryPolicy "pd" retryUnknown) retryEvent).2.claimed
#guard retryEvent.body.dispatchOf "c1"
#guard statusOf (step retryPolicy (after retryPolicy "pd" retryUnknown) retryEvent).1 "c1"
  == some .dispatched

def reconcileEvent : Event := ⟨6, 6, 5, none, .reconcile "c1" .succeeded none false⟩

#guard (step retryPolicy (after retryPolicy "pd" retryUnknown) reconcileEvent).2.accepted
#guard ((step retryPolicy (after retryPolicy "pd" retryUnknown) reconcileEvent).1.calls["c1"]?).any
  fun c => c.status == .unknown && c.reconciled == some .succeeded

def succeeded : List Event := witnessEvents ++ [⟨5, 5, 4, none, .result "c1" .succeeded none false⟩]

def lateResult : Event := ⟨6, 6, 5, none, .result "c1" .failed none false⟩

#guard statusOf (after witnessPolicy "pd" succeeded) "c1" == some .succeeded
#guard (step witnessPolicy (after witnessPolicy "pd" succeeded) lateResult).2
  == .rejected .callEnded
#guard statusOf (step witnessPolicy (after witnessPolicy "pd" succeeded) lateResult).1 "c1"
  == some .succeeded

def epochEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .reset⟩
  , ⟨4, 4, 3, none, .propose "c1" "t" "d1" none [] []⟩ ]

def epochDispatch : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

#guard (after witnessPolicy "pd" epochEvents).epoch == 1
#guard (step witnessPolicy (after witnessPolicy "pd" epochEvents) epochDispatch).2.claimed
#guard ((after witnessPolicy "pd" epochEvents).calls["c1"]?).any fun c =>
  c.status == .authorized && c.epoch == 1

def resetAuthorized : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .reset⟩ ]

#guard statusOf (after witnessPolicy "pd" (resetAuthorized.take 3)) "c1" == some .authorized
#guard statusOf (after witnessPolicy "pd" resetAuthorized) "c1" == some .cancelled
#guard (step witnessPolicy (after witnessPolicy "pd" resetAuthorized) epochDispatch).2
  == .rejected .callEnded

def ttlConsent : Policy := { consentPolicy with limits := { approvalTtlMs := some 10 } }

def approveOpen : List Event := consentEvents.take 3

/-- The request is made at time 3 with a TTL of 10, so time 12 is its last instant. -/
def approveAt (time : Nat) (gen : Nat) : Event :=
  ⟨4, time, 3, none, .approve "c1" ⟨"s1", "c1", gen⟩ "a1" "d1" none none⟩

#guard ttlConsent.approvalTtl ((ttlConsent.action? "pay").getD {}) == some 10
#guard ((after ttlConsent "pd" approveOpen).calls["c1"]?).any fun c =>
  c.status == .awaiting && c.requestedAt == 3 && c.generation == 0 && c.epoch == 0
#guard (step ttlConsent (after ttlConsent "pd" approveOpen) (approveAt 12 0)).2
  == .ok .authorized none
#guard (step ttlConsent (after ttlConsent "pd" approveOpen) (approveAt 13 0)).2
  == .rejected .approvalExpired
#guard (step ttlConsent (after ttlConsent "pd" approveOpen) (approveAt 12 1)).2
  == .rejected .staleRequest

def authAt (s : State) (k : String) : Option (Option Nat) := s.calls[k]?.map (·.authorizedAt)

#guard (List.range 6).map (fun n => authAt (after retryPolicy "pd" (retryUnknown.take n)) "c1")
  == [none, none, none, some (some 3), some (some 3), some (some 3)]
#guard ((step retryPolicy (after retryPolicy "pd" retryUnknown) retryEvent).1.calls["c1"]?).any
  fun c => c.status == .dispatched && c.attempts == 2 && c.authorizedAt == some 3

-- The TTL witnesses are in `Dispatch.lean`; these add the mode and rules `claim_authorized_ttl`
-- reads.
#guard ttlPolicy.modeOf "t" == .enforce
#guard ttlPolicy.action? "t" == some {}

end Lifecycle

end Writ.Proofs
