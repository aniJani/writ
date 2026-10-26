import Writ.Kernel.Run

namespace Writ.Proofs

open Writ

def after (p : Policy) (d : String) (es : List Event) : State := (run p (State.initial d) es).1

inductive Reachable (p : Policy) (d : String) : State → Prop where
  | init : Reachable p d (State.initial d)
  | step : Reachable p d s → Reachable p d (Writ.step p s e).1

def trace (p : Policy) : State → List Event → List (State × Event × Verdict)
  | _, [] => []
  | s, e :: es => (s, e, (step p s e).2) :: trace p (step p s e).1 es

def Verdict.accepted : Verdict → Bool
  | .ok _ _ => true
  | .rejected _ => false

def Verdict.claimed : Verdict → Bool
  | .ok .dispatchClaimed _ => true
  | _ => false

def EventBody.dispatchOf (k : String) : EventBody → Bool
  | .dispatch k' .. => k' == k
  | _ => false

def EventBody.unknownOf (k : String) : EventBody → Bool
  | .outcomeUnknown k' => k' == k
  | _ => false

def EventBody.isKill : EventBody → Bool
  | .kill => true
  | _ => false

end Writ.Proofs

-- Aliases in the kernel types' namespaces make `v.accepted` and `b.dispatchOf k` resolve while
-- the definitions stay in `Writ.Proofs`.
namespace Writ.Verdict
export Writ.Proofs.Verdict (accepted claimed)
end Writ.Verdict

namespace Writ.EventBody
export Writ.Proofs.EventBody (dispatchOf unknownOf isKill)
end Writ.EventBody

namespace Writ.Proofs

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event}

theorem claimed_accepted {v : Verdict} (h : v.claimed = true) : v.accepted = true := by
  cases v with
  | ok => rfl
  | rejected => cases h

local macro "unclaimed" : tactic =>
  `(tactic| repeat' (first | rfl | (dsimp only) | split | simp only [Verdict.claimed]))

namespace Basic

theorem run_nil_fst : (run p s []).1 = s := rfl

theorem run_cons_fst : (run p s (e :: es)).1 = (run p (step p s e).1 es).1 := rfl

theorem run_append {es₁ es₂ : List Event} :
    (run p s (es₁ ++ es₂)).1 = (run p (run p s es₁).1 es₂).1 := by
  induction es₁ generalizing s with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, run_cons_fst, ih]

theorem after_nil : after p d [] = State.initial d := rfl

theorem after_append {es₁ es₂ : List Event} :
    after p d (es₁ ++ es₂) = (run p (after p d es₁) es₂).1 :=
  run_append

theorem after_snoc : after p d (es ++ [e]) = (step p (after p d es) e).1 :=
  after_append

theorem snoc_induction {P : List Event → Prop} (h₀ : P [])
    (hs : ∀ (es : List Event) (e : Event), P es → P (es ++ [e])) (es : List Event) : P es := by
  have h : ∀ l : List Event, P l.reverse := by
    intro l
    induction l with
    | nil => exact h₀
    | cons e l ih => rw [List.reverse_cons]; exact hs _ _ ih
  simpa using h es.reverse

end Basic

open Basic

theorem Reachable.run (h : Reachable p d s) : Reachable p d (run p s es).1 := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => rw [run_cons_fst]; exact ih h.step

namespace Basic

theorem reachable_after : Reachable p d (after p d es) :=
  Reachable.init.run

theorem reachable_iff : Reachable p d s ↔ ∃ es, after p d es = s := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨[], rfl⟩
    | @step s e _ ih =>
      obtain ⟨es, rfl⟩ := ih
      exact ⟨es ++ [e], after_snoc⟩
  · rintro ⟨es, rfl⟩
    exact reachable_after

theorem trace_append_single :
    trace p s (es ++ [e]) = trace p s es ++ [((run p s es).1, e, (step p (run p s es).1 e).2)] := by
  induction es generalizing s with
  | nil => rfl
  | cons e' es ih => simp only [List.cons_append, trace, ih, run_cons_fst]

theorem trace_snoc :
    trace p (State.initial d) (es ++ [e])
      = trace p (State.initial d) es ++ [(after p d es, e, (step p (after p d es) e).2)] :=
  trace_append_single

theorem trace_mem_snoc_iff {x : State × Event × Verdict} :
    x ∈ trace p (State.initial d) (es ++ [e]) ↔
      x ∈ trace p (State.initial d) es ∨ x = (after p d es, e, (step p (after p d es) e).2) := by
  rw [trace_snoc, List.mem_append, List.mem_singleton]

theorem trace_mem_snoc {x : State × Event × Verdict} (h : x ∈ trace p (State.initial d) es) :
    x ∈ trace p (State.initial d) (es ++ [e]) :=
  trace_mem_snoc_iff.mpr (.inl h)

theorem trace_mem_last :
    (after p d es, e, (step p (after p d es) e).2) ∈ trace p (State.initial d) (es ++ [e]) :=
  trace_mem_snoc_iff.mpr (.inr rfl)

end Basic

theorem frame : (step p s e).2.accepted = false → (step p s e).1 = s := by
  unfold step
  split
  · intro _; rfl
  · split
    · simp [Verdict.accepted]
    · intro _; rfl

namespace Basic

theorem accepted_open : (step p s e).2.accepted = true → stepEnvelope s e = none := by
  unfold step
  split
  · simp [Verdict.accepted]
  · intro _; assumption

theorem accepted_step :
    (step p s e).2.accepted = true →
      (step p s e) = ({ (stepHandle p s e).1 with
        lastSeq := e.seq, lastTime := e.time, version := s.version + 1 },
        (stepHandle p s e).2) := by
  unfold step
  split
  · simp [Verdict.accepted]
  · split
    · rename_i h; intro _; rw [h]
    · rename_i v' hv _
      intro h
      cases v' with
      | ok d sh => exact absurd rfl (hv d sh)
      | rejected r => simp [Verdict.accepted] at h

theorem handleSessionStart_unclaimed : (handleSessionStart s i pd r ps as l).2.claimed = false := by
  unfold handleSessionStart; unclaimed

theorem handleSessionEnd_unclaimed : (handleSessionEnd s).2.claimed = false := by
  unfold handleSessionEnd; unclaimed

theorem handleTurnStart_unclaimed : (handleTurnStart s u).2.claimed = false := by
  unfold handleTurnStart; unclaimed

theorem handleTurnEnd_unclaimed : (handleTurnEnd s).2.claimed = false := by
  unfold handleTurnEnd; unclaimed

theorem handleStepStart_unclaimed : (handleStepStart p s).2.claimed = false := by
  unfold handleStepStart; unclaimed

theorem handleApproverAttest_unclaimed : (handleApproverAttest s a i).2.claimed = false := by
  unfold handleApproverAttest; unclaimed

theorem handlePermissionRevoke_unclaimed : (handlePermissionRevoke s a).2.claimed = false := by
  unfold handlePermissionRevoke; unclaimed

theorem applyApprove_unclaimed (h : applyApprove p s t i rc w pr dg c ed = .ok r) :
    r.2.claimed = false := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

theorem handleApprove_unclaimed : (handleApprove p s t i r w dg c ed).2.claimed = false := by
  unfold handleApprove
  repeat' (first | rfl | (dsimp only) | split)
  exact applyApprove_unclaimed (by assumption)

theorem handleReject_unclaimed : (handleReject p s i r w).2.claimed = false := by
  unfold handleReject; unclaimed

theorem handleApprovalExpire_unclaimed : (handleApprovalExpire s i r).2.claimed = false := by
  unfold handleApprovalExpire; unclaimed

theorem handleGrantCreate_unclaimed :
    (handleGrantCreate p s t a b c dg sc n mc nb ex rv).2.claimed = false := by
  unfold handleGrantCreate; unclaimed

theorem handleGrantRevoke_unclaimed : (handleGrantRevoke s i).2.claimed = false := by
  unfold handleGrantRevoke; unclaimed

theorem handleResult_unclaimed : (handleResult p s t i o a n).2.claimed = false := by
  unfold handleResult Decision.ofOverrun; unclaimed

theorem handleOutcomeUnknown_unclaimed : (handleOutcomeUnknown p s i).2.claimed = false := by
  unfold handleOutcomeUnknown; unclaimed

theorem handleReconcile_unclaimed : (handleReconcile p s t i o a n).2.claimed = false := by
  unfold handleReconcile Decision.ofOverrun; unclaimed

theorem handleCancel_unclaimed : (handleCancel s i).2.claimed = false := by
  unfold handleCancel; unclaimed

theorem handleReset_unclaimed : (handleReset s).2.claimed = false := by
  unfold handleReset; unclaimed

theorem handleKill_unclaimed : (handleKill p s).2.claimed = false := by unfold handleKill; unclaimed

theorem handlePermissionAdd_unclaimed : (handlePermissionAdd p s a b).2.claimed = false := by
  unfold handlePermissionAdd; unclaimed

theorem handleEscalationAck_unclaimed : (handleEscalationAck p s a b).2.claimed = false := by
  unfold handleEscalationAck; unclaimed

theorem handleLedgerSync_unclaimed : (handleLedgerSync s l).2.claimed = false := by
  unfold handleLedgerSync; unclaimed

theorem disposition_unclaimed (x : Disposition) (sh : Option Shadow) :
    (Verdict.ok x.decision sh).claimed = false := by
  cases x <;> rfl

theorem repeatDecision_claimed (h : (repeatDecision p s t k rc).1 = .dispatchClaimed) :
    rc.decision = .dispatchClaimed := by
  unfold repeatDecision at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals first | (cases h; done) | exact h

theorem handlePropose_claimed (h : (handlePropose p s t k tool dg c g x).2.claimed = true) :
    ∃ rc, s.calls[k]? = some rc ∧ rc.decision = .dispatchClaimed := by
  unfold handlePropose at h
  split at h
  · rename_i rc hrc
    refine ⟨rc, hrc, ?_⟩
    split at h
    · revert h
      generalize hr : repeatDecision p s t k rc = r
      obtain ⟨dd, sh⟩ := r
      intro h
      cases dd <;> simp [Verdict.claimed] at h
      exact repeatDecision_claimed (by rw [hr])
    · cases h
  · exfalso
    repeat' (first | (dsimp only at h) | split at h)
    all_goals rw [disposition_unclaimed] at h; cases h

theorem stepHandle_claimed (h : (stepHandle p s e).2.claimed = true) :
    (∃ k n dg c g key, e.body = .dispatch k n dg c g key) ∨
      ∃ k t dg c g x rc, e.body = .propose k t dg c g x ∧ s.calls[k]? = some rc ∧
        rc.decision = .dispatchClaimed := by
  unfold stepHandle at h
  split at h <;> rename_i hb
  all_goals first
    | (rw [handleSessionStart_unclaimed] at h; cases h)
    | (rw [handleSessionEnd_unclaimed] at h; cases h)
    | (rw [handleTurnStart_unclaimed] at h; cases h)
    | (rw [handleTurnEnd_unclaimed] at h; cases h)
    | (rw [handleStepStart_unclaimed] at h; cases h)
    | (rw [handleApproverAttest_unclaimed] at h; cases h)
    | (rw [handlePermissionRevoke_unclaimed] at h; cases h)
    | (rw [handleApprove_unclaimed] at h; cases h)
    | (rw [handleReject_unclaimed] at h; cases h)
    | (rw [handleApprovalExpire_unclaimed] at h; cases h)
    | (rw [handleGrantCreate_unclaimed] at h; cases h)
    | (rw [handleGrantRevoke_unclaimed] at h; cases h)
    | (rw [handleResult_unclaimed] at h; cases h)
    | (rw [handleOutcomeUnknown_unclaimed] at h; cases h)
    | (rw [handleReconcile_unclaimed] at h; cases h)
    | (rw [handleCancel_unclaimed] at h; cases h)
    | (rw [handleReset_unclaimed] at h; cases h)
    | (rw [handleKill_unclaimed] at h; cases h)
    | (rw [handlePermissionAdd_unclaimed] at h; cases h)
    | (rw [handleEscalationAck_unclaimed] at h; cases h)
    | (rw [handleLedgerSync_unclaimed] at h; cases h)
    | exact .inl ⟨_, _, _, _, _, _, hb⟩
    | (obtain ⟨rc, hrc, hd⟩ := handlePropose_claimed h
       exact .inr ⟨_, _, _, _, _, _, rc, hb, hrc, hd⟩)

theorem step_claimed (h : (step p s e).2.claimed = true) : (stepHandle p s e).2.claimed = true := by
  unfold step at h
  split at h
  · cases h
  · split at h <;> rename_i hh <;> rw [hh] <;> exact h

abbrev CallMap := Std.ExtTreeMap String CallRec compare

/-- A stored decision is a disposition's, so never a claim or an overrun, which a repeated
`propose` would otherwise return. -/
def CallsUnclaimed (m : CallMap) : Prop :=
  ∀ (k : String) (c : CallRec), m[k]? = some c →
    c.decision ≠ .dispatchClaimed ∧ ∀ ms, c.decision ≠ .overrun ms

def NoClaimed (s : State) : Prop := CallsUnclaimed s.calls

theorem CallsUnclaimed.insert {m : CallMap} (h : CallsUnclaimed m) {c : CallRec}
    (hc : c.decision ≠ .dispatchClaimed ∧ ∀ ms, c.decision ≠ .overrun ms) :
    CallsUnclaimed (m.insert k c) := by
  intro k' c' h'
  rw [Std.ExtTreeMap.getElem?_insert] at h'
  split at h'
  · cases h'; exact hc
  · exact h _ _ h'

theorem CallsUnclaimed.insert_of {m : CallMap} (h : CallsUnclaimed m) {c c₀ : CallRec}
    {k₀ : String} (h₀ : m[k₀]? = some c₀) (hd : c.decision = c₀.decision) :
    CallsUnclaimed (m.insert k c) :=
  h.insert (hd ▸ h _ _ h₀)

theorem CallsUnclaimed.modify {m : CallMap} (h : CallsUnclaimed m) {f : CallRec → CallRec}
    (hf : ∀ c, (f c).decision = c.decision) : CallsUnclaimed (m.modify k f) := by
  intro k' c' h'
  rw [Std.ExtTreeMap.getElem?_modify] at h'
  split at h'
  · cases hk : m[k]? with
    | none => simp [hk] at h'
    | some c₀ => simp [hk] at h'; subst h'; rw [hf]; exact h _ _ hk
  · exact h _ _ h'

theorem CallsUnclaimed.map {m : CallMap} (h : CallsUnclaimed m) {f : String → CallRec → CallRec}
    (hf : ∀ k c, (f k c).decision = c.decision) : CallsUnclaimed (m.map f) := by
  intro k' c' h'
  rw [Std.ExtTreeMap.getElem?_map] at h'
  cases hk : m[k']? with
  | none => simp [hk] at h'
  | some c₀ => simp [hk] at h'; subst h'; rw [hf]; exact h _ _ hk

theorem foldl_invariant {α β : Type _} (P : β → Prop) {f : β → α → β}
    (hf : ∀ b a, P b → P (f b a)) : ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_invariant P hf l (f b a) (hf b a hb)

theorem insert_ne {α : Type _} {t : Std.ExtTreeMap String α compare} {a k : String} {v : α}
    (h : a ≠ k) : (t.insert k v)[a]? = t[a]? := by
  rw [Std.ExtTreeMap.getElem?_insert]
  split
  next he => exact absurd (Std.LawfulEqCmp.eq_of_compare he).symm h
  · rfl

theorem modify_ne {α : Type _} {t : Std.ExtTreeMap String α compare} {a k : String}
    {f : α → α} (h : a ≠ k) : (t.modify k f)[a]? = t[a]? := by
  rw [Std.ExtTreeMap.getElem?_modify]
  split
  next he => exact absurd (Std.LawfulEqCmp.eq_of_compare he).symm h
  · rfl

theorem toList_get {α : Type _} {t : Std.ExtTreeMap String α compare} :
    ∀ x ∈ t.toList, t[x.1]? = some x.2 :=
  fun _ hx => Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx

theorem distinct_toList {α : Type _} {t : Std.ExtTreeMap String α compare} :
    t.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
  Std.ExtTreeMap.distinct_keys_toList.imp fun h he => h (by rw [he]; exact Std.ReflCmp.compare_self)

theorem releaseGrant_calls : (s.releaseGrant k).calls = s.calls := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem consumeGrant_calls : (s.consumeGrant k).calls = s.calls := by
  unfold State.consumeGrant; repeat' split
  all_goals rfl

theorem recordFailure_calls : (s.recordFailure p t).calls = s.calls := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem recordSuccess_calls : (s.recordSuccess t).calls = s.calls := rfl

theorem updateEntries_calls : (s.updateEntries p m t f).calls = s.calls := by
  unfold State.updateEntries; split <;> rfl

theorem reserve_calls : (s.reserve p m k a t).calls = s.calls := updateEntries_calls
theorem retime_calls : (s.retime p m k t).calls = s.calls := updateEntries_calls
theorem commit_calls : (s.commit p m k a t).calls = s.calls := updateEntries_calls
theorem release_calls : (s.release p m k t).calls = s.calls := updateEntries_calls

theorem settle_calls : (s.settle p ms k o a ne t).1.calls = s.calls := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.calls = s.calls) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · rw [release_calls, h]
  · split <;> rw [commit_calls, h]

theorem NoClaimed.of_calls {s' : State} (h : NoClaimed s) (he : s'.calls = s.calls) :
    NoClaimed s' := by
  unfold NoClaimed; rw [he]; exact h

theorem NoClaimed.endCall (h : NoClaimed s) : NoClaimed (s.endCall k st) := by
  unfold State.endCall NoClaimed
  dsimp only
  rw [releaseGrant_calls]
  exact CallsUnclaimed.modify h (fun _ => rfl)

theorem NoClaimed.cancelPending (h : NoClaimed s) : NoClaimed (Writ.cancelPending s) := by
  unfold Writ.cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant NoClaimed ?_ _ _ h
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact ha.endCall
  · exact ha.endCall
  · exact ha

theorem NoClaimed.interrupt (h : NoClaimed s) : NoClaimed s.interrupt := by
  unfold State.interrupt NoClaimed
  refine CallsUnclaimed.map h.cancelPending ?_
  intro k c; split <;> rfl

local macro "keeps" h:ident : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact $h
      | exact NoClaimed.of_calls $h rfl
      | exact NoClaimed.endCall $h
      | exact NoClaimed.cancelPending $h
      | exact NoClaimed.interrupt $h
      | (apply NoClaimed.of_calls $h
         simp only [recordFailure_calls, recordSuccess_calls, settle_calls, releaseGrant_calls]))

theorem handleSessionStart_noClaimed (h : NoClaimed s) :
    NoClaimed (handleSessionStart s i pd r ps as l).1 := by
  unfold handleSessionStart; keeps h

theorem handleSessionEnd_noClaimed (h : NoClaimed s) : NoClaimed (handleSessionEnd s).1 := by
  unfold handleSessionEnd; keeps h

theorem handleTurnStart_noClaimed (h : NoClaimed s) :
    NoClaimed (handleTurnStart s u).1 := by
  unfold handleTurnStart; keeps h

theorem handleTurnEnd_noClaimed (h : NoClaimed s) :
    NoClaimed (handleTurnEnd s).1 := by
  unfold handleTurnEnd; keeps h

theorem handleStepStart_noClaimed (h : NoClaimed s) :
    NoClaimed (handleStepStart p s).1 := by
  unfold handleStepStart; keeps h

theorem handleApproverAttest_noClaimed (h : NoClaimed s) :
    NoClaimed (handleApproverAttest s a i).1 := by
  unfold handleApproverAttest; keeps h

theorem handlePermissionRevoke_noClaimed (h : NoClaimed s) :
    NoClaimed (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; keeps h

theorem handleReject_noClaimed (h : NoClaimed s) :
    NoClaimed (handleReject p s i r w).1 := by
  unfold handleReject; keeps h

theorem handleApprovalExpire_noClaimed (h : NoClaimed s) :
    NoClaimed (handleApprovalExpire s i r).1 := by
  unfold handleApprovalExpire; keeps h

theorem handleGrantCreate_noClaimed (h : NoClaimed s) :
    NoClaimed (handleGrantCreate p s t a b c dg sc n mc nb ex rv).1 := by
  unfold handleGrantCreate; keeps h

theorem handleGrantRevoke_noClaimed (h : NoClaimed s) : NoClaimed (handleGrantRevoke s i).1 := by
  unfold handleGrantRevoke; keeps h

theorem handleCancel_noClaimed (h : NoClaimed s) :
    NoClaimed (handleCancel s i).1 := by
  unfold handleCancel; keeps h

theorem handleReset_noClaimed (h : NoClaimed s) :
    NoClaimed (handleReset s).1 := by
  unfold handleReset; keeps h

theorem handleKill_noClaimed (h : NoClaimed s) :
    NoClaimed (handleKill p s).1 := by
  unfold handleKill; keeps h

theorem handlePermissionAdd_noClaimed (h : NoClaimed s) :
    NoClaimed (handlePermissionAdd p s a b).1 := by
  unfold handlePermissionAdd; keeps h

theorem handleEscalationAck_noClaimed (h : NoClaimed s) :
    NoClaimed (handleEscalationAck p s a b).1 := by
  unfold handleEscalationAck; keeps h

theorem handleLedgerSync_noClaimed (h : NoClaimed s) : NoClaimed (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; keeps h

theorem NoClaimed.withStatus (h : NoClaimed s) (hr : s.calls[k]? = some rc) :
    NoClaimed (withStatus s k rc st) :=
  CallsUnclaimed.insert_of h hr rfl

theorem handleResult_noClaimed (h : NoClaimed s) : NoClaimed (handleResult p s t i o a n).1 := by
  unfold handleResult
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact h
    | (simp only [NoClaimed, recordFailure_calls, recordSuccess_calls, settle_calls]
       exact NoClaimed.withStatus h (by assumption))

theorem handleOutcomeUnknown_noClaimed (h : NoClaimed s) :
    NoClaimed (handleOutcomeUnknown p s i).1 := by
  unfold handleOutcomeUnknown
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact h
    | (simp only [NoClaimed, recordFailure_calls]
       exact NoClaimed.withStatus h (by assumption))

theorem handleReconcile_noClaimed (h : NoClaimed s) :
    NoClaimed (handleReconcile p s t i o a n).1 := by
  unfold handleReconcile
  split
  · exact h
  · rename_i rc hrc
    have h' : NoClaimed { s with calls := s.calls.insert i { rc with reconciled := some o } } :=
      CallsUnclaimed.insert_of h hrc rfl
    repeat' (first | (dsimp only) | split)
    all_goals first
      | exact h
      | exact h'.of_calls (by simp only [recordFailure_calls, settle_calls])

theorem foldl_calls {α : Type _} {f : State → α → State}
    (hf : ∀ s a, (f s a).calls = s.calls) (l : List α) (s : State) :
    (l.foldl f s).calls = s.calls :=
  foldl_invariant (fun b => b.calls = s.calls) (fun b a hb => (hf b a).trans hb) l s rfl

theorem NoClaimed.claim (h : NoClaimed s) (hr : s.calls[k]? = some rc) :
    NoClaimed (Writ.claim p s t k rc r retry key) := by
  unfold Writ.claim NoClaimed
  dsimp only
  split
  · rw [foldl_calls (fun _ _ => retime_calls)]
    exact CallsUnclaimed.insert_of h hr rfl
  · rw [foldl_calls (fun _ _ => reserve_calls), consumeGrant_calls]
    exact CallsUnclaimed.insert_of h hr rfl

theorem handleDispatch_noClaimed (h : NoClaimed s) :
    NoClaimed (handleDispatch p s t i n dg c g key).1 := by
  unfold handleDispatch
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact h
    | exact h.endCall
    | exact h.claim (by assumption)

theorem disposition_decision_ne (x : Disposition) :
    x.decision ≠ .dispatchClaimed ∧ ∀ ms, x.decision ≠ .overrun ms := by
  cases x <;> simp [Disposition.decision]

theorem handlePropose_noClaimed (h : NoClaimed s) :
    NoClaimed (handlePropose p s t k tool dg c g x).1 := by
  unfold handlePropose
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact h
    | exact CallsUnclaimed.insert h (disposition_decision_ne _)

theorem callCheck_ok (h : callCheck s k rid = .ok rc) : s.calls[k]? = some rc := by
  unfold callCheck at h
  repeat' split at h
  all_goals (cases h <;> assumption)

theorem awaitingCheck_ok (h : awaitingCheck p s k rid w = .ok rc) : s.calls[k]? = some rc := by
  unfold awaitingCheck at h
  cases hc : callCheck s k rid with
  | error => simp [hc, bind, Except.bind] at h
  | ok rc' =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    · cases h; exact callCheck_ok hc

theorem applyApprove_noClaimed (h : NoClaimed s) (hr : s.calls[k]? = some rc)
    (ha : applyApprove p s t k rc w pr dg c ed = .ok r) : NoClaimed r.1 := by
  unfold applyApprove at ha
  repeat' (first | (dsimp only at ha) | split at ha)
  all_goals first
    | cases ha; done
    | (cases ha
       rename_i rc' hn _
       have hd : rc'.decision = rc.decision := by
         revert hn
         repeat' split
         all_goals (intro hn; cases hn <;> rfl)
       exact CallsUnclaimed.insert_of h hr hd)

theorem handleApprove_noClaimed (h : NoClaimed s) :
    NoClaimed (handleApprove p s t i r w dg c ed).1 := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact h
    | exact applyApprove_noClaimed h (awaitingCheck_ok (by assumption)) (by assumption)

theorem NoClaimed.stepHandle (h : NoClaimed s) : NoClaimed (stepHandle p s e).1 := by
  unfold Writ.stepHandle
  split <;> first
    | with_reducible exact handleSessionStart_noClaimed h
    | with_reducible exact handleSessionEnd_noClaimed h
    | with_reducible exact handleTurnStart_noClaimed h
    | with_reducible exact handleTurnEnd_noClaimed h
    | with_reducible exact handleStepStart_noClaimed h
    | with_reducible exact handleApproverAttest_noClaimed h
    | with_reducible exact handlePermissionRevoke_noClaimed h
    | with_reducible exact handlePropose_noClaimed h
    | with_reducible exact handleApprove_noClaimed h
    | with_reducible exact handleReject_noClaimed h
    | with_reducible exact handleApprovalExpire_noClaimed h
    | with_reducible exact handleGrantCreate_noClaimed h
    | with_reducible exact handleGrantRevoke_noClaimed h
    | with_reducible exact handleDispatch_noClaimed h
    | with_reducible exact handleResult_noClaimed h
    | with_reducible exact handleOutcomeUnknown_noClaimed h
    | with_reducible exact handleReconcile_noClaimed h
    | with_reducible exact handleCancel_noClaimed h
    | with_reducible exact handleReset_noClaimed h
    | with_reducible exact handleKill_noClaimed h
    | with_reducible exact handlePermissionAdd_noClaimed h
    | with_reducible exact handleEscalationAck_noClaimed h
    | with_reducible exact handleLedgerSync_noClaimed h

theorem NoClaimed.step (h : NoClaimed s) : NoClaimed (step p s e).1 := by
  have hh := h.stepHandle (p := p) (e := e)
  unfold Writ.step
  split
  · exact h
  · split
    · rename_i hs; rw [hs] at hh; exact hh
    · exact h

theorem NoClaimed.initial : NoClaimed (State.initial d) := by
  intro k c hk
  simp [State.initial] at hk

theorem NoClaimed.reachable (hr : Reachable p d s) : NoClaimed s := by
  induction hr with
  | init => exact NoClaimed.initial
  | step _ ih => exact NoClaimed.step ih

end Basic

theorem no_claimed_decision (hr : Reachable p d s) :
    ∀ (k : String) (c : CallRec), s.calls[k]? = some c → c.decision ≠ .dispatchClaimed :=
  fun k c hk => (NoClaimed.reachable hr k c hk).1

theorem claimed_dispatch (hr : Reachable p d s) (h : (step p s e).2.claimed = true) :
    ∃ k n dg c g key, e.body = .dispatch k n dg c g key := by
  rcases stepHandle_claimed (step_claimed h) with hd | ⟨_, _, _, _, _, _, rc, _, hrc, hdec⟩
  · exact hd
  · exact absurd hdec (no_claimed_decision hr _ rc hrc)

namespace Basic

def witnessPolicy : Policy := { actions := [("t", {})] }

def witnessEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" none [] "k1"⟩ ]

def staleEvent : Event := ⟨4, 5, 4, none, .turnEnd⟩

end Basic

#guard (trace witnessPolicy (State.initial "pd") witnessEvents).map (·.2.2.accepted)
  == [true, true, true, true]
#guard ((trace witnessPolicy (State.initial "pd") witnessEvents).map (·.2.2.claimed)).getLast?
  == some true
#guard (step witnessPolicy (after witnessPolicy "pd" witnessEvents) staleEvent).2
  == .rejected .staleSeq
#guard (step witnessPolicy (after witnessPolicy "pd" witnessEvents) staleEvent).2.accepted == false
#guard (step witnessPolicy (after witnessPolicy "pd" witnessEvents) staleEvent).1
  == after witnessPolicy "pd" witnessEvents

end Writ.Proofs
