import WritProofs.Dispatch

namespace Writ.Proofs

open Writ
open Basic

variable {p : Policy} {s s' s₀ s₁ s₂ : State} {e : Event} {k : String} {c c' rc : CallRec}

namespace Calls

def Fresh (p : Policy) (c : CallRec) : Prop :=
  ∃ r, p.action? c.tool = some r ∧ (r.exposed = false → ∃ x, c.status = .denied x)

/-- A status a handler may still change: `unknown` counts, since a retry or reconcile moves it. -/
def Live (c : CallRec) : Prop := c.status.terminal = true → c.status = .unknown

/-- Only `propose` creates a record, so a new key holds a `Fresh` one. -/
def KeyStep (p : Policy) : Option CallRec → Option CallRec → Prop
  | some c, some c' =>
    c'.tool = c.tool ∧ (c.status.terminal = true → c.status ≠ .unknown → c'.status = c.status)
  | some _, none => False
  | none, some c' => Fresh p c'
  | none, none => True

def MapStep (p : Policy) (m m' : CallMap) : Prop := ∀ k : String, KeyStep p m[k]? m'[k]?

def CallsStep (p : Policy) (s s' : State) : Prop := MapStep p s.calls s'.calls

theorem Live.of_terminal (h : c.status.terminal = false) : Live c := fun h' => by
  rw [h] at h'; cases h'

theorem Live.keyStep (hl : Live c) (ht : c'.tool = c.tool) : KeyStep p (some c) (some c') :=
  ⟨ht, fun h hu => absurd (hl h) hu⟩

theorem Fresh.keyStep (hf : Fresh p c) (h : KeyStep p (some c) (some c')) : Fresh p c' := by
  obtain ⟨r, hr, hx⟩ := hf
  obtain ⟨ht, hs⟩ := h
  refine ⟨r, ht ▸ hr, fun he => ?_⟩
  obtain ⟨x, hx⟩ := hx he
  exact ⟨x, (hs (by rw [hx]; rfl) (by rw [hx]; nofun)).trans hx⟩

theorem KeyStep.refl : ∀ o, KeyStep p o o
  | some _ => ⟨rfl, fun _ _ => rfl⟩
  | none => trivial

theorem KeyStep.trans :
    ∀ {a b c : Option CallRec}, KeyStep p a b → KeyStep p b c → KeyStep p a c
  | some _, some _, some _, ⟨t₁, s₁⟩, ⟨t₂, s₂⟩ =>
    ⟨t₂.trans t₁, fun ht hu =>
      (s₂ (by rw [s₁ ht hu]; exact ht) (by rw [s₁ ht hu]; exact hu)).trans (s₁ ht hu)⟩
  | none, some _, some _, h₁, h₂ => Fresh.keyStep h₁ h₂
  | some _, none, _, h₁, _ => h₁.elim
  | _, some _, none, _, h₂ => h₂.elim
  | none, none, _, _, h₂ => h₂

theorem MapStep.refl {m : CallMap} : MapStep p m m := fun _ => KeyStep.refl _

theorem MapStep.insert_live {m m' : CallMap} (h : MapStep p m m') (hk : m[k]? = some c)
    (hl : Live c) (ht : c'.tool = c.tool) : MapStep p m (m'.insert k c') := by
  intro a
  rw [Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i he
    cases Std.LawfulEqCmp.eq_of_compare he
    rw [hk]; exact hl.keyStep ht
  · exact h a

theorem MapStep.insert_fresh {m m' : CallMap} (h : MapStep p m m') (hk : m[k]? = none)
    (hf : Fresh p c') : MapStep p m (m'.insert k c') := by
  intro a
  rw [Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i he
    cases Std.LawfulEqCmp.eq_of_compare he
    rw [hk]; exact hf
  · exact h a

theorem MapStep.modify_live {m m' : CallMap} {f : CallRec → CallRec} (h : MapStep p m m')
    (hk : m[k]? = some c) (hl : Live c) (hf : ∀ a, (f a).tool = a.tool) :
    MapStep p m (m'.modify k f) := by
  intro a
  rw [Std.ExtTreeMap.getElem?_modify]
  split
  · rename_i he
    cases Std.LawfulEqCmp.eq_of_compare he
    have hk' := h k
    rw [hk] at hk' ⊢
    cases hb : m'[k]? with
    | none => rw [hb] at hk'; exact hk'.elim
    | some b => rw [hb] at hk'; exact hl.keyStep ((hf b).trans hk'.1)
  · exact h a

theorem MapStep.map {m m' : CallMap} {f : String → CallRec → CallRec} (h : MapStep p m m')
    (hf : ∀ k c, KeyStep p (some c) (some (f k c))) : MapStep p m (m'.map f) := by
  intro a
  rw [Std.ExtTreeMap.getElem?_map]
  have ha := h a
  cases hb : m'[a]? with
  | none => rw [hb] at ha; exact ha
  | some b => rw [hb] at ha; exact ha.trans (hf a b)

theorem CallsStep.refl : CallsStep p s s := MapStep.refl

theorem CallsStep.of_calls (h : s'.calls = s.calls) : CallsStep p s s' := by
  unfold CallsStep; rw [h]; exact MapStep.refl

theorem CallsStep.congr (h : CallsStep p s₀ s₁) (he : s₂.calls = s₁.calls) :
    CallsStep p s₀ s₂ := by
  unfold CallsStep; rw [he]; exact h

theorem CallsStep.endCall (h : CallsStep p s₀ s) (hk : s₀.calls[k]? = some c) (hl : Live c) :
    CallsStep p s₀ (s.endCall k st) := by
  unfold State.endCall CallsStep
  dsimp only
  rw [releaseGrant_calls]
  exact MapStep.modify_live h hk hl (fun _ => rfl)

theorem foldl_invariant_mem {α β : Type _} (P : β → Prop) {f : β → α → β} :
    ∀ (l : List α), (∀ b a, a ∈ l → P b → P (f b a)) → ∀ b, P b → P (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, hf, b, hb =>
    foldl_invariant_mem P l (fun b a ha => hf b a (List.mem_cons_of_mem _ ha)) (f b a)
      (hf b a List.mem_cons_self hb)

theorem CallsStep.cancelPending : CallsStep p s (Writ.cancelPending s) := by
  unfold Writ.cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant_mem (CallsStep p s) _ ?_ _ CallsStep.refl
  intro acc ⟨k, c⟩ hm ha
  have hk := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm
  dsimp only
  split <;> rename_i hs
  · exact ha.endCall hk (.of_terminal (by rw [hs]; rfl))
  · exact ha.endCall hk (.of_terminal (by rw [hs]; rfl))
  · exact ha

theorem CallsStep.interrupt : CallsStep p s s.interrupt := by
  unfold State.interrupt CallsStep
  refine MapStep.map CallsStep.cancelPending fun _ c => ?_
  split
  · rename_i hd; exact Live.keyStep (.of_terminal (by rw [hd]; rfl)) rfl
  · exact KeyStep.refl _

theorem CallsStep.insert_live (hk : s.calls[k]? = some c) (hl : Live c)
    (he : s'.calls = s.calls.insert k c') (ht : c'.tool = c.tool) : CallsStep p s s' := by
  unfold CallsStep; rw [he]; exact MapStep.insert_live MapStep.refl hk hl ht

local macro "live" rc:term : tactic =>
  `(tactic| (intro ht; cases hs : CallRec.status $rc <;> simp_all [CallStatus.terminal]))

theorem CallsStep.claim (hk : s.calls[k]? = some rc) (hl : Live rc) :
    CallsStep p s (Writ.claim p s t k rc r retry key) := by
  unfold Writ.claim CallsStep
  dsimp only
  split
  · rw [foldl_calls (fun _ _ => retime_calls)]
    exact MapStep.insert_live MapStep.refl hk hl rfl
  · rw [foldl_calls (fun _ _ => reserve_calls), consumeGrant_calls]
    exact MapStep.insert_live MapStep.refl hk hl rfl

local macro "calls_step" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact CallsStep.refl
      | exact CallsStep.of_calls rfl
      | exact CallsStep.cancelPending
      | exact CallsStep.interrupt
      | (apply CallsStep.of_calls
         simp only [recordFailure_calls, recordSuccess_calls, settle_calls, releaseGrant_calls]))

theorem handleSessionStart_calls : CallsStep p s (handleSessionStart s i pd r ps as l).1 := by
  unfold handleSessionStart; calls_step

theorem handleSessionEnd_calls : CallsStep p s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; calls_step

theorem handleTurnStart_calls : CallsStep p s (handleTurnStart s u).1 := by
  unfold handleTurnStart; calls_step

theorem handleTurnEnd_calls : CallsStep p s (handleTurnEnd s).1 := by
  unfold handleTurnEnd; calls_step

theorem handleStepStart_calls : CallsStep p s (handleStepStart p s).1 := by
  unfold handleStepStart; calls_step

theorem handleApproverAttest_calls : CallsStep p s (handleApproverAttest s a i).1 := by
  unfold handleApproverAttest; calls_step

theorem handlePermissionRevoke_calls : CallsStep p s (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; calls_step

theorem handleGrantCreate_calls :
    CallsStep p s (handleGrantCreate p s t a b cs dg sc n mc nb ex rv).1 := by
  unfold handleGrantCreate; calls_step

theorem handleGrantRevoke_calls : CallsStep p s (handleGrantRevoke s i).1 := by
  unfold handleGrantRevoke; calls_step

theorem handleReset_calls : CallsStep p s (handleReset s).1 := by
  unfold handleReset; calls_step

theorem handleKill_calls : CallsStep p s (handleKill p s).1 := by
  unfold handleKill; calls_step

theorem handlePermissionAdd_calls : CallsStep p s (handlePermissionAdd p s a b).1 := by
  unfold handlePermissionAdd; calls_step

theorem handleEscalationAck_calls : CallsStep p s (handleEscalationAck p s a b).1 := by
  unfold handleEscalationAck; calls_step

theorem handleLedgerSync_calls : CallsStep p s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; calls_step

theorem handleCancel_calls : CallsStep p s (handleCancel s i).1 := by
  unfold handleCancel
  split
  · exact CallsStep.refl
  · rename_i rc hrc
    split
    · exact CallsStep.refl.endCall hrc (by live rc)
    · exact CallsStep.refl.endCall hrc (by live rc)
    · exact CallsStep.refl

theorem callCheck_live (h : callCheck s k rid = .ok rc) : Live rc := by
  unfold callCheck at h
  repeat' split at h
  all_goals (cases h <;> live rc)

theorem awaitingCheck_live (h : awaitingCheck p s k rid w = .ok rc) : Live rc := by
  unfold awaitingCheck at h
  cases hc : callCheck s k rid with
  | error => simp [hc, bind, Except.bind] at h
  | ok rc' =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    · cases h; exact callCheck_live hc

theorem vetoCheck_ok (h : vetoCheck p s k rid w = .ok rc) : s.calls[k]? = some rc ∧ Live rc := by
  unfold vetoCheck at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨by assumption, by live rc⟩)

theorem handleReject_calls : CallsStep p s (handleReject p s i r w).1 := by
  unfold handleReject
  split
  · exact CallsStep.refl
  · rename_i rc hv
    obtain ⟨hk, hl⟩ := vetoCheck_ok hv
    exact CallsStep.refl.endCall hk hl

theorem handleApprovalExpire_calls : CallsStep p s (handleApprovalExpire s i r).1 := by
  unfold handleApprovalExpire
  split
  · exact CallsStep.refl
  · rename_i rc hv
    exact CallsStep.refl.endCall (callCheck_ok hv) (callCheck_live hv)

theorem applyApprove_calls (hr : s.calls[k]? = some rc) (hl : Live rc)
    (ha : applyApprove p s t k rc w pr dg cs ed = .ok r) : CallsStep p s r.1 := by
  unfold applyApprove at ha
  repeat' (first | (dsimp only at ha) | split at ha)
  all_goals first
    | cases ha; done
    | (cases ha
       rename_i rc' hn _
       have ht : rc'.tool = rc.tool := by
         revert hn
         repeat' split
         all_goals (intro hn; cases hn <;> rfl)
       exact MapStep.insert_live MapStep.refl hr hl ht)

theorem handleApprove_calls : CallsStep p s (handleApprove p s t i r w dg cs ed).1 := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact CallsStep.refl
    | exact applyApprove_calls (awaitingCheck_ok (by assumption))
        (awaitingCheck_live (by assumption)) (by assumption)

theorem handleDispatch_calls : CallsStep p s (handleDispatch p s t i n dg cs g key).1 := by
  rcases Dispatch.handle_cases with he | ⟨c, st, hk, hs, -, he⟩ | ⟨c, hk, hs, he⟩ <;> rw [he]
  · exact CallsStep.refl
  · exact CallsStep.refl.endCall hk (by live c)
  · exact CallsStep.claim hk (by live c)

theorem handleResult_calls : CallsStep p s (handleResult p s t i o a n).1 := by
  unfold handleResult
  split
  · exact CallsStep.refl
  · rename_i rc hrc
    split
    · exact CallsStep.refl
    · have hl : Live rc := by live rc
      repeat' (first | (dsimp only) | split)
      all_goals
        exact CallsStep.insert_live hrc hl
          (by simp only [recordFailure_calls, recordSuccess_calls, settle_calls] <;> rfl) (by rfl)

theorem handleOutcomeUnknown_calls : CallsStep p s (handleOutcomeUnknown p s i).1 := by
  unfold handleOutcomeUnknown
  split
  · exact CallsStep.refl
  · rename_i rc hrc
    split
    · exact CallsStep.refl
    · exact CallsStep.insert_live hrc (by live rc) (by simp only [recordFailure_calls] <;> rfl)
        (by rfl)

theorem handleReconcile_calls : CallsStep p s (handleReconcile p s t i o a n).1 := by
  unfold handleReconcile
  split
  · exact CallsStep.refl
  · rename_i rc hrc
    split
    · exact CallsStep.refl
    · have hl : Live rc := by live rc
      have h' :
          CallsStep p s { s with calls := s.calls.insert i { rc with reconciled := some o } } :=
        MapStep.insert_live MapStep.refl hrc hl rfl
      repeat' (first | (dsimp only) | split)
      all_goals first
        | exact CallsStep.refl
        | exact h'.congr (by simp only [recordFailure_calls, settle_calls])

section propose

variable {tool dg : String} {cs : Option Cost} {gs es : List (String × Bool)} {r : Requirements}

theorem enforceDecision_denied
    (hu : p.action? tool = none ∨ ∃ r, p.action? tool = some r ∧ r.exposed = false) :
    ∃ x, (enforceDecision p s t k tool dg cs gs es).1 = .denied x := by
  unfold enforceDecision
  rcases hu with ha | ⟨r, ha, hx⟩
  · simp only [ha]
    split <;> exact ⟨_, rfl⟩
  · simp only [ha, hx, Option.getD_some, Option.isNone_some, Bool.not_false, Bool.false_eq_true,
      ite_false, ite_true]
    split <;> exact ⟨_, rfl⟩

theorem modeOf_unexposed (ha : p.action? tool = some r) (hx : r.exposed = false) :
    p.modeOf tool = .enforce := by
  unfold Policy.modeOf; simp [ha, hx]

theorem shadowed_enforce (x : Disposition) : x.shadowed .enforce = (x, none) := by
  cases x <;> rfl

theorem handlePropose_calls : CallsStep p s (handlePropose p s t k tool dg cs gs es).1 := by
  unfold handlePropose
  split
  · split <;> exact CallsStep.refl
  · rename_i hk
    split
    rename_i d c hd
    split
    · exact CallsStep.of_calls rfl
    · rename_i r hr
      dsimp only
      refine MapStep.insert_fresh MapStep.refl hk ⟨r, hr, fun hx => ?_⟩
      obtain ⟨x, hx'⟩ := enforceDecision_denied (s := s) (t := t) (k := k) (dg := dg) (cs := cs)
        (gs := gs) (es := es) (.inr ⟨r, hr, hx⟩)
      rw [hd] at hx'
      dsimp only at hx'
      subst hx'
      rw [modeOf_unexposed hr hx, shadowed_enforce]
      exact ⟨x, rfl⟩

end propose

theorem CallsStep.stepHandle : CallsStep p s (stepHandle p s e).1 := by
  unfold Writ.stepHandle
  split <;> first
    | with_reducible exact handleSessionStart_calls
    | with_reducible exact handleSessionEnd_calls
    | with_reducible exact handleTurnStart_calls
    | with_reducible exact handleTurnEnd_calls
    | with_reducible exact handleStepStart_calls
    | with_reducible exact handleApproverAttest_calls
    | with_reducible exact handlePermissionRevoke_calls
    | with_reducible exact handlePropose_calls
    | with_reducible exact handleApprove_calls
    | with_reducible exact handleReject_calls
    | with_reducible exact handleApprovalExpire_calls
    | with_reducible exact handleGrantCreate_calls
    | with_reducible exact handleGrantRevoke_calls
    | with_reducible exact handleDispatch_calls
    | with_reducible exact handleResult_calls
    | with_reducible exact handleOutcomeUnknown_calls
    | with_reducible exact handleReconcile_calls
    | with_reducible exact handleCancel_calls
    | with_reducible exact handleReset_calls
    | with_reducible exact handleKill_calls
    | with_reducible exact handlePermissionAdd_calls
    | with_reducible exact handleEscalationAck_calls
    | with_reducible exact handleLedgerSync_calls

theorem CallsStep.step : CallsStep p s (step p s e).1 := by
  have hh := CallsStep.stepHandle (p := p) (s := s) (e := e)
  unfold Writ.step
  split
  · exact CallsStep.refl
  · split
    · rename_i hs; rw [hs] at hh; exact hh
    · exact CallsStep.refl

theorem calls_step_some (hc : s.calls[k]? = some c) :
    ∃ c', (step p s e).1.calls[k]? = some c' ∧ KeyStep p (some c) (some c') := by
  have hs := CallsStep.step (p := p) (s := s) (e := e) k
  rw [hc] at hs
  cases hk : (step p s e).1.calls[k]? with
  | none => rw [hk] at hs; exact hs.elim
  | some c' => rw [hk] at hs; exact ⟨c', rfl, hs⟩

end Calls

open Calls

theorem calls_keep : (step p s e).1.calls[k]? = none → s.calls[k]? = none := by
  intro h
  have hs := CallsStep.step (p := p) (s := s) (e := e) k
  rw [h] at hs
  cases hk : s.calls[k]? with
  | none => rfl
  | some _ => rw [hk] at hs; exact hs.elim

theorem calls_tool : s.calls[k]? = some c →
    ∃ c', (step p s e).1.calls[k]? = some c' ∧ c'.tool = c.tool := by
  intro hc
  obtain ⟨c', hc', ht, _⟩ := calls_step_some (p := p) (e := e) hc
  exact ⟨c', hc', ht⟩

theorem calls_terminal (hc : s.calls[k]? = some c) (ht : c.status.terminal = true)
    (hu : c.status ≠ .unknown) (hc' : (step p s e).1.calls[k]? = some c') :
    c'.status = c.status := by
  obtain ⟨c'', hc'', _, hs⟩ := calls_step_some (p := p) (e := e) hc
  rw [hc'] at hc''
  cases hc''
  exact hs ht hu

end Writ.Proofs
