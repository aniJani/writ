import WritProofs.Dispatch

namespace Writ.Proofs

open Writ
open Basic

/-- The entries after the last accepted `turn_start`, or all of them when there is none. Only
that event resets the kernel's turn counters, so events after a `turn_end` stay in the turn. -/
def sinceTurn (l : List (State × Event × Verdict)) : List (State × Event × Verdict) :=
  l.foldl (init := []) fun acc x =>
    match x.2.1.body, x.2.2 with
    | .turnStart _, .ok _ _ => []
    | _, _ => acc ++ [x]

def newAllowed (p : Policy) (x : State × Event × Verdict) : Bool :=
  match x.2.1.body, x.2.2 with
  | .propose k t .., .ok dc _ =>
    x.1.calls[k]?.isNone && p.modeOf t == .enforce &&
      match dc with
      | .denied _ => false
      | _ => true
  | _, _ => false

def newNeedsApproval (x : State × Event × Verdict) : Bool :=
  match x.2.1.body, x.2.2 with
  | .propose k .., .ok (.needsApproval _) _ => x.1.calls[k]?.isNone
  | _, _ => false

def stepAccepted (x : State × Event × Verdict) : Bool :=
  match x.2.1.body with
  | .stepStart => x.2.2.accepted
  | _ => false

namespace Limits

variable {p : Policy} {s : State} {e : Event}

def ctr (s : State) : List Nat :=
  [s.stepsThisTurn, s.proposalsThisTurn, s.approvalsThisTurn, s.proposalsThisSession,
   s.approvalsThisSession]

theorem releaseGrant_ctr : ctr (s.releaseGrant k) = ctr s := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem consumeGrant_ctr : ctr (s.consumeGrant k) = ctr s := by
  unfold State.consumeGrant; repeat' split
  all_goals rfl

theorem recordFailure_ctr {tool : String} : ctr (s.recordFailure p tool) = ctr s := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem updateEntries_ctr : ctr (s.updateEntries p m t f) = ctr s := by
  unfold State.updateEntries; split <;> rfl

theorem foldl_ctr {α : Type _} {f : State → α → State} (hf : ∀ s a, ctr (f s a) = ctr s)
    (l : List α) (s : State) : ctr (l.foldl f s) = ctr s :=
  foldl_invariant (fun b => ctr b = ctr s) (fun b a hb => (hf b a).trans hb) l s rfl

theorem settle_ctr : ctr (s.settle p ms k o a ne t).1 = ctr s := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => ctr b.1 = ctr s) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact updateEntries_ctr.trans h
  · split <;> exact updateEntries_ctr.trans h

theorem endCall_ctr : ctr (s.endCall k st) = ctr s := releaseGrant_ctr

theorem cancelPending_ctr : ctr (cancelPending s) = ctr s := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b => ctr b = ctr s) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact endCall_ctr.trans ha
  · exact endCall_ctr.trans ha
  · exact ha

theorem interrupt_ctr : ctr s.interrupt = ctr s := cancelPending_ctr

theorem claim_ctr {r : Requirements} {key : String} {retry : Bool} :
    ctr (claim p s t k rc r retry key) = ctr s := by
  unfold claim
  dsimp only
  split
  · exact foldl_ctr (fun _ _ => updateEntries_ctr) _ _
  · exact (foldl_ctr (fun _ _ => updateEntries_ctr) _ _).trans consumeGrant_ctr

theorem withStatus_ctr : ctr (withStatus s k rc st) = ctr s := rfl

theorem recordSuccess_ctr {tool : String} : ctr (s.recordSuccess tool) = ctr s := rfl

local macro "ctr_keeps" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | rfl
      | exact cancelPending_ctr
      | exact interrupt_ctr
      | exact endCall_ctr
      | exact claim_ctr
      | (simp only [recordFailure_ctr, recordSuccess_ctr, settle_ctr, withStatus_ctr]; done)
      | (rw [recordFailure_ctr]; exact settle_ctr)
      | exact settle_ctr)

theorem handleSessionStart_ctr : ctr (handleSessionStart s i pd r ps as l).1 = ctr s := by
  unfold handleSessionStart; ctr_keeps

theorem handleSessionEnd_ctr : ctr (handleSessionEnd s).1 = ctr s := by
  unfold handleSessionEnd; ctr_keeps

theorem handleTurnEnd_ctr : ctr (handleTurnEnd s).1 = ctr s := by
  unfold handleTurnEnd; ctr_keeps

theorem handleApproverAttest_ctr : ctr (handleApproverAttest s a i).1 = ctr s := by
  unfold handleApproverAttest; ctr_keeps

theorem handlePermissionRevoke_ctr : ctr (handlePermissionRevoke s a).1 = ctr s := by
  unfold handlePermissionRevoke; ctr_keeps

theorem applyApprove_ctr (h : applyApprove p s t k rc w pr dg c ed = .ok r) : ctr r.1 = ctr s := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

theorem handleApprove_ctr : ctr (handleApprove p s t i r w dg c ed).1 = ctr s := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | rfl
    | exact applyApprove_ctr (by assumption)

theorem handleReject_ctr : ctr (handleReject p s i r w).1 = ctr s := by
  unfold handleReject
  split
  · rfl
  · exact endCall_ctr (s := s) (k := i) (st := .rejected)

theorem handleApprovalExpire_ctr : ctr (handleApprovalExpire s i r).1 = ctr s := by
  unfold handleApprovalExpire; ctr_keeps

theorem handleGrantCreate_ctr :
    ctr (handleGrantCreate p s t a b c dg sc n mc nb ex rv).1 = ctr s := by
  unfold handleGrantCreate; ctr_keeps

theorem handleGrantRevoke_ctr : ctr (handleGrantRevoke s i).1 = ctr s := by
  unfold handleGrantRevoke; ctr_keeps

theorem handleDispatch_ctr : ctr (handleDispatch p s t i n dg c g key).1 = ctr s := by
  rcases Dispatch.handle_cases with he | ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] <;>
    ctr_keeps

theorem handleResult_ctr : ctr (handleResult p s t i o a n).1 = ctr s := by
  unfold handleResult; ctr_keeps

theorem handleOutcomeUnknown_ctr : ctr (handleOutcomeUnknown p s i).1 = ctr s := by
  unfold handleOutcomeUnknown; ctr_keeps

theorem handleReconcile_ctr : ctr (handleReconcile p s t i o a n).1 = ctr s := by
  unfold handleReconcile; ctr_keeps

theorem handleCancel_ctr : ctr (handleCancel s i).1 = ctr s := by
  unfold handleCancel; ctr_keeps

theorem handleReset_ctr : ctr (handleReset s).1 = ctr s := by
  unfold handleReset; ctr_keeps

theorem handleKill_ctr : ctr (handleKill p s).1 = ctr s := by
  unfold handleKill; ctr_keeps

theorem handlePermissionAdd_ctr : ctr (handlePermissionAdd p s a b).1 = ctr s := by
  unfold handlePermissionAdd; ctr_keeps

theorem handleEscalationAck_ctr : ctr (handleEscalationAck p s a b).1 = ctr s := by
  unfold handleEscalationAck; ctr_keeps

theorem handleLedgerSync_ctr : ctr (handleLedgerSync s l).1 = ctr s := by
  unfold handleLedgerSync; ctr_keeps

def counts : EventBody → Bool
  | .propose .. | .turnStart _ | .stepStart => true
  | _ => false

theorem stepHandle_ctr (h : counts e.body = false) : ctr (stepHandle p s e).1 = ctr s := by
  unfold stepHandle
  split <;> rename_i hb <;> (try (rw [hb] at h; cases h)) <;> first
    | with_reducible exact handleSessionStart_ctr
    | with_reducible exact handleSessionEnd_ctr
    | with_reducible exact handleTurnEnd_ctr
    | with_reducible exact handleApproverAttest_ctr
    | with_reducible exact handlePermissionRevoke_ctr
    | with_reducible exact handleApprove_ctr
    | with_reducible exact handleReject_ctr
    | with_reducible exact handleApprovalExpire_ctr
    | with_reducible exact handleGrantCreate_ctr
    | with_reducible exact handleGrantRevoke_ctr
    | with_reducible exact handleDispatch_ctr
    | with_reducible exact handleResult_ctr
    | with_reducible exact handleOutcomeUnknown_ctr
    | with_reducible exact handleReconcile_ctr
    | with_reducible exact handleCancel_ctr
    | with_reducible exact handleReset_ctr
    | with_reducible exact handleKill_ctr
    | with_reducible exact handlePermissionAdd_ctr
    | with_reducible exact handleEscalationAck_ctr
    | with_reducible exact handleLedgerSync_ctr

theorem counts_true {b : EventBody} (h : counts b = true) :
    (∃ k t dg c g x, b = .propose k t dg c g x) ∨ (∃ u, b = .turnStart u) ∨
      b = .stepStart := by
  cases b <;> simp_all [counts]

structure Le (s s' : State) : Prop where
  steps : s.stepsThisTurn ≤ s'.stepsThisTurn
  props : s.proposalsThisTurn ≤ s'.proposalsThisTurn
  appr : s.approvalsThisTurn ≤ s'.approvalsThisTurn
  propsS : s.proposalsThisSession ≤ s'.proposalsThisSession
  apprS : s.approvalsThisSession ≤ s'.approvalsThisSession

theorem Le.of_ctr {s' : State} (h : ctr s' = ctr s) : Le s s' := by
  simp only [ctr, List.cons.injEq] at h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem propose_le : Le s (handlePropose p s t k tool dg c g x).1 := by
  unfold handlePropose
  repeat' (first | (dsimp only) | split)
  all_goals exact ⟨by simp, by simp, by simp, by simp, by simp⟩

theorem propose_new (hk : s.calls[k]? = none) :
    (handlePropose p s t k tool dg c g x).1.proposalsThisTurn = s.proposalsThisTurn + 1 ∧
      (handlePropose p s t k tool dg c g x).1.proposalsThisSession
        = s.proposalsThisSession + 1 := by
  unfold handlePropose
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  repeat' (first | (dsimp only) | split)
  all_goals exact ⟨rfl, rfl⟩

theorem stepStart_le : Le s (handleStepStart p s).1 := by
  unfold handleStepStart
  repeat' (first | (dsimp only) | split)
  all_goals exact ⟨by simp, by simp, by simp, by simp, by simp⟩

theorem turnStart_le :
    s.proposalsThisSession ≤ (handleTurnStart s u).1.proposalsThisSession ∧
      s.approvalsThisSession ≤ (handleTurnStart s u).1.approvalsThisSession := by
  unfold handleTurnStart
  split <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem exceeded_lt {L : Option Nat} (h : exceeded L c = false) (hn : L = some n) : c < n := by
  subst hn; simp only [exceeded, decide_eq_false_iff_not] at h; omega

theorem preConsent_none {r : Requirements} (h : preConsentDenial p s t r tool dg c g = none) :
    exceeded p.limits.maxProposalsPerSession s.proposalsThisSession = false ∧
      exceeded p.limits.maxProposalsPerTurn s.proposalsThisTurn = false := by
  unfold preConsentDenial at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h₁ h₂
      exact ⟨by simpa using h₁, by simpa using h₂⟩

theorem enforce_allowed (h : ∀ r, (enforceDecision p s t k tool dg c g x).1 ≠ .denied r) :
    exceeded p.limits.maxProposalsPerSession s.proposalsThisSession = false ∧
      exceeded p.limits.maxProposalsPerTurn s.proposalsThisTurn = false := by
  unfold enforceDecision at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals first
    | exact absurd rfl (h _)
    | exact preConsent_none (by assumption)

theorem enforce_needsApproval
    (h : (enforceDecision p s t k tool dg c g x).1 = .needsApproval rid) :
    (p.action? tool).isSome ∧
      exceeded p.limits.maxApprovalRequestsPerSession s.approvalsThisSession = false ∧
      exceeded p.limits.maxApprovalRequestsPerTurn s.approvalsThisTurn = false := by
  unfold enforceDecision at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals first
    | cases h; done
    | exact ⟨by simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none]
          using ‹¬(p.action? tool).isNone = true›,
        by simpa using ‹¬exceeded p.limits.maxApprovalRequestsPerSession _ = true›,
        by simpa using ‹¬exceeded p.limits.maxApprovalRequestsPerTurn _ = true›⟩

theorem shadowed_needsApproval {m : Mode} {d : Disposition}
    (h : (d.shadowed m).1.decision = .needsApproval rid) :
    d = .needsApproval rid ∧ m = .enforce := by
  cases m <;> cases d <;> simp only [Disposition.shadowed] at h
  all_goals (try split at h) <;> simp_all [Disposition.decision]

theorem propose_allowed (hk : s.calls[k]? = none) (hm : p.modeOf tool = .enforce)
    (hv : (handlePropose p s t k tool dg c g x).2 = .ok dc sh) (hd : ∀ r, dc ≠ .denied r) :
    exceeded p.limits.maxProposalsPerSession s.proposalsThisSession = false ∧
      exceeded p.limits.maxProposalsPerTurn s.proposalsThisTurn = false := by
  apply enforce_allowed (k := k) (dg := dg) (c := c) (g := g) (x := x)
  unfold handlePropose at hv
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk] at hv
  generalize enforceDecision p s t k tool dg c g x = E at hv ⊢
  obtain ⟨d, cc⟩ := E
  dsimp only at hv ⊢
  intro r hr
  subst hr
  split at hv
  · cases hv; exact hd r rfl
  · rw [hm] at hv; cases hv; exact hd r rfl

theorem propose_needsApproval (hk : s.calls[k]? = none)
    (hv : (handlePropose p s t k tool dg c g x).2 = .ok (.needsApproval rid) sh) :
    (handlePropose p s t k tool dg c g x).1.approvalsThisTurn = s.approvalsThisTurn + 1 ∧
      (handlePropose p s t k tool dg c g x).1.approvalsThisSession
        = s.approvalsThisSession + 1 ∧
      exceeded p.limits.maxApprovalRequestsPerSession s.approvalsThisSession = false ∧
      exceeded p.limits.maxApprovalRequestsPerTurn s.approvalsThisTurn = false := by
  unfold handlePropose at hv ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk] at hv ⊢
  generalize hE : enforceDecision p s t k tool dg c g x = E at hv ⊢
  obtain ⟨d, cc⟩ := E
  dsimp only at hv ⊢
  cases ha : p.action? tool with
  | none =>
    rw [ha] at hv
    injection hv with h₁
    cases d <;> cases h₁
    have := (enforce_needsApproval (by rw [hE])).1
    rw [ha] at this
    cases this
  | some r =>
    rw [ha] at hv
    dsimp only at hv ⊢
    injection hv with h₁
    obtain ⟨rfl, hm⟩ := shadowed_needsApproval h₁
    obtain ⟨_, h₂, h₃⟩ := enforce_needsApproval (by rw [hE])
    simp [hm, Disposition.needsApproval?, h₂, h₃]

theorem stepStart_accepted (h : (handleStepStart p s).2.accepted = true) :
    (handleStepStart p s).1.stepsThisTurn = s.stepsThisTurn + 1 ∧
      (p.mode = .enforce → ∀ n, p.limits.maxStepsPerTurn = some n → s.stepsThisTurn < n) := by
  unfold handleStepStart at h ⊢
  cases hL : p.limits.maxStepsPerTurn with
  | none => simp
  | some n =>
    cases hm : p.mode <;> by_cases hc : s.stepsThisTurn ≥ n <;>
      simp_all [Verdict.accepted, Nat.not_le]

theorem Le.upd {s' : State} (h : Le s s') (a b c : Nat) :
    Le s { s' with lastSeq := a, lastTime := b, version := c } :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

theorem step_le :
    ((¬∃ u, e.body = .turnStart u) ∨ (step p s e).2.accepted = false →
        Le s (step p s e).1) ∧
      s.proposalsThisSession ≤ (step p s e).1.proposalsThisSession ∧
      s.approvalsThisSession ≤ (step p s e).1.approvalsThisSession := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact ⟨fun _ => Le.of_ctr rfl, Nat.le_refl _, Nat.le_refl _⟩
  · rw [accepted_step ha]
    have hle : ∀ {P : Prop} {s' : State}, Le s s' → ∀ a b c,
        (P → Le s { s' with lastSeq := a, lastTime := b, version := c }) ∧
          s.proposalsThisSession ≤ s'.proposalsThisSession ∧
          s.approvalsThisSession ≤ s'.approvalsThisSession :=
      fun h a b c => ⟨fun _ => h.upd a b c, h.propsS, h.apprS⟩
    cases hc : counts e.body
    · exact hle (Le.of_ctr (stepHandle_ctr hc)) _ _ _
    · rcases counts_true hc with ⟨k, t, dg, c, g, x, hb⟩ | ⟨u, hb⟩ | hb <;>
        simp only [stepHandle, hb]
      · exact hle propose_le _ _ _
      · refine ⟨fun h => ?_, turnStart_le⟩
        rcases h with h | h
        · exact absurd ⟨u, rfl⟩ h
        · cases h
      · exact hle stepStart_le _ _ _

theorem newAllowed_eq {v : Verdict} (h : newAllowed p (s, e, v) = true) :
    ∃ k t dg c g x dc sh, e.body = .propose k t dg c g x ∧ v = .ok dc sh ∧
      s.calls[k]? = none ∧ p.modeOf t = .enforce ∧ ∀ r, dc ≠ .denied r := by
  obtain ⟨_, _, _, _, b⟩ := e
  cases b <;> cases v <;> simp only [newAllowed] at h <;> try (cases h; done)
  rename_i k t dg c g x dc sh
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at h
  refine ⟨k, t, dg, c, g, x, dc, sh, rfl, rfl, h.1.1, h.1.2, ?_⟩
  rintro r rfl
  simp at h

theorem newNeedsApproval_eq {v : Verdict} (h : newNeedsApproval (s, e, v) = true) :
    ∃ k t dg c g x rid sh, e.body = .propose k t dg c g x ∧ v = .ok (.needsApproval rid) sh ∧
      s.calls[k]? = none := by
  obtain ⟨_, _, _, _, b⟩ := e
  cases b <;> cases v <;> simp only [newNeedsApproval] at h <;> try (cases h; done)
  rename_i k t dg c g x dc sh
  cases dc <;> simp only at h <;> try (cases h; done)
  exact ⟨k, t, dg, c, g, x, _, sh, rfl, rfl, by simpa using h⟩

theorem stepAccepted_eq {v : Verdict} (h : stepAccepted (s, e, v) = true) :
    e.body = .stepStart ∧ v.accepted = true := by
  obtain ⟨_, _, _, _, b⟩ := e
  cases b <;> simp only [stepAccepted] at h <;> first | (cases h; done) | exact ⟨rfl, h⟩

theorem step_allowed (h : newAllowed p (s, e, (step p s e).2) = true) :
    (step p s e).1.proposalsThisTurn = s.proposalsThisTurn + 1 ∧
      (step p s e).1.proposalsThisSession = s.proposalsThisSession + 1 ∧
      exceeded p.limits.maxProposalsPerSession s.proposalsThisSession = false ∧
      exceeded p.limits.maxProposalsPerTurn s.proposalsThisTurn = false := by
  obtain ⟨k, t, dg, c, g, x, dc, sh, hb, hv, hk, hm, hd⟩ := newAllowed_eq h
  have ha : (step p s e).2.accepted = true := by rw [hv]; rfl
  rw [accepted_step ha] at hv ⊢
  simp only [stepHandle, hb] at hv ⊢
  exact ⟨(propose_new hk).1, (propose_new hk).2, propose_allowed hk hm hv hd⟩

theorem step_needsApproval (h : newNeedsApproval (s, e, (step p s e).2) = true) :
    (step p s e).1.approvalsThisTurn = s.approvalsThisTurn + 1 ∧
      (step p s e).1.approvalsThisSession = s.approvalsThisSession + 1 ∧
      exceeded p.limits.maxApprovalRequestsPerSession s.approvalsThisSession = false ∧
      exceeded p.limits.maxApprovalRequestsPerTurn s.approvalsThisTurn = false := by
  obtain ⟨k, t, dg, c, g, x, rid, sh, hb, hv, hk⟩ := newNeedsApproval_eq h
  have ha : (step p s e).2.accepted = true := by rw [hv]; rfl
  rw [accepted_step ha] at hv ⊢
  simp only [stepHandle, hb] at hv ⊢
  exact propose_needsApproval hk hv

theorem step_stepAccepted (h : stepAccepted (s, e, (step p s e).2) = true) :
    (step p s e).1.stepsThisTurn = s.stepsThisTurn + 1 ∧
      (p.mode = .enforce → ∀ n, p.limits.maxStepsPerTurn = some n → s.stepsThisTurn < n) := by
  obtain ⟨hb, ha⟩ := stepAccepted_eq h
  have ha' := ha
  rw [accepted_step ha] at ha' ⊢
  simp only [stepHandle, hb] at ha' ⊢
  exact stepStart_accepted ha'

theorem sinceTurn_reset {l : List (State × Event × Verdict)} {v : Verdict}
    (hb : e.body = .turnStart u) (hv : v.accepted = true) : sinceTurn (l ++ [(s, e, v)]) = [] := by
  unfold sinceTurn
  rw [List.foldl_append]
  cases v
  · simp [hb]
  · cases hv

theorem sinceTurn_keep {l : List (State × Event × Verdict)} {v : Verdict}
    (h : (¬∃ u, e.body = .turnStart u) ∨ v.accepted = false) :
    sinceTurn (l ++ [(s, e, v)]) = sinceTurn l ++ [(s, e, v)] := by
  unfold sinceTurn
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split
  · rename_i u _ _ hb
    rcases h with h | h
    · exact absurd ⟨u, hb⟩ h
    · cases h
  · rfl

/-- A count of entries in a segment of the trace stays within the counter `f` and the limit `L`
when each step either starts a new segment or keeps `f` from falling, raises it for each
counted entry, and counts an entry only below the limit. -/
theorem bound (seg : List (State × Event × Verdict) → List (State × Event × Verdict))
    (f : State → Nat) (L : Option Nat) (cnt : State × Event × Verdict → Bool)
    (hnil : seg [] = [])
    (hstep : ∀ l s e, seg (l ++ [(s, e, (step p s e).2)]) = [] ∨
      (seg (l ++ [(s, e, (step p s e).2)]) = seg l ++ [(s, e, (step p s e).2)] ∧
        f s + (if cnt (s, e, (step p s e).2) then 1 else 0) ≤ f (step p s e).1))
    (hcap : ∀ s e n, cnt (s, e, (step p s e).2) = true → L = some n → f s < n)
    (s : State) (es : List Event) :
    ((seg (trace p s es)).filter cnt).length ≤ f (run p s es).1 ∧
      ∀ n, L = some n → ((seg (trace p s es)).filter cnt).length ≤ n := by
  induction es using snoc_induction with
  | h₀ => simp [trace, hnil]
  | hs es e ih =>
    rw [trace_append_single, run_append]
    show _ ≤ f (step p (run p s es).1 e).1 ∧ _
    rcases hstep (trace p s es) (run p s es).1 e with h | ⟨h, hf⟩
    · simp [h]
    · rw [h, List.filter_append, List.length_append]
      obtain ⟨ih₁, ih₂⟩ := ih
      have hc := hcap (run p s es).1 e
      cases hx : cnt ((run p s es).1, e, (step p (run p s es).1 e).2) <;>
        simp only [hx, List.filter, List.length_cons, List.length_nil, ↓reduceIte] at hf ⊢
      · exact ⟨by omega, fun n hn => by have := ih₂ n hn; omega⟩
      · exact ⟨by omega, fun n hn => by have := ih₂ n hn; have := hc n hx hn; omega⟩

theorem turn_step {f : State → Nat} {cnt : State × Event × Verdict → Bool}
    (hle : ∀ {s s'}, Le s s' → f s ≤ f s')
    (hinc : ∀ s e, cnt (s, e, (step p s e).2) = true → f (step p s e).1 = f s + 1) :
    ∀ l s e, sinceTurn (l ++ [(s, e, (step p s e).2)]) = [] ∨
      (sinceTurn (l ++ [(s, e, (step p s e).2)]) = sinceTurn l ++ [(s, e, (step p s e).2)] ∧
        f s + (if cnt (s, e, (step p s e).2) then 1 else 0) ≤ f (step p s e).1) := by
  intro l s e
  by_cases hr : (∃ u, e.body = .turnStart u) ∧ (step p s e).2.accepted = true
  · obtain ⟨⟨u, hb⟩, hv⟩ := hr
    exact .inl (sinceTurn_reset hb hv)
  · have hk : (¬∃ u, e.body = .turnStart u) ∨ (step p s e).2.accepted = false := by
      by_cases hu : ∃ u, e.body = .turnStart u
      · exact .inr (by simpa using fun h => hr ⟨hu, h⟩)
      · exact .inl hu
    refine .inr ⟨sinceTurn_keep hk, ?_⟩
    split
    · exact Nat.le_of_eq (hinc s e ‹_›).symm
    · exact Nat.add_zero _ ▸ hle (step_le.1 hk)

theorem session_step {f : State → Nat} {cnt : State × Event × Verdict → Bool}
    (hle : ∀ s e, f s ≤ f (step p s e).1)
    (hinc : ∀ s e, cnt (s, e, (step p s e).2) = true → f (step p s e).1 = f s + 1) :
    ∀ (l : List (State × Event × Verdict)) s e, l ++ [(s, e, (step p s e).2)] = [] ∨
      (l ++ [(s, e, (step p s e).2)] = l ++ [(s, e, (step p s e).2)] ∧
        f s + (if cnt (s, e, (step p s e).2) then 1 else 0) ≤ f (step p s e).1) := by
  intro l s e
  refine .inr ⟨rfl, ?_⟩
  split
  · exact Nat.le_of_eq (hinc s e ‹_›).symm
  · exact Nat.add_zero _ ▸ hle s e

end Limits

open Limits

variable {p : Policy} {s : State} {es : List Event} {n : Nat}

theorem proposals_per_turn (hn : p.limits.maxProposalsPerTurn = some n) :
    ((sinceTurn (trace p s es)).filter (newAllowed p)).length ≤ n :=
  (bound sinceTurn (·.proposalsThisTurn) _ (newAllowed p) rfl
    (turn_step Le.props fun _ _ h => (step_allowed h).1)
    (fun _ _ _ h => exceeded_lt (step_allowed h).2.2.2) s es).2 n hn

theorem proposals_per_session (hn : p.limits.maxProposalsPerSession = some n) :
    ((trace p s es).filter (newAllowed p)).length ≤ n :=
  (bound id (·.proposalsThisSession) _ (newAllowed p) rfl
    (session_step (fun _ _ => step_le.2.1) fun _ _ h => (step_allowed h).2.1)
    (fun _ _ _ h => exceeded_lt (step_allowed h).2.2.1) s es).2 n hn

theorem approvals_per_turn (hn : p.limits.maxApprovalRequestsPerTurn = some n) :
    ((sinceTurn (trace p s es)).filter newNeedsApproval).length ≤ n :=
  (bound sinceTurn (·.approvalsThisTurn) _ newNeedsApproval rfl
    (turn_step Le.appr fun _ _ h => (step_needsApproval h).1)
    (fun _ _ _ h => exceeded_lt (step_needsApproval h).2.2.2) s es).2 n hn

theorem approvals_per_session (hn : p.limits.maxApprovalRequestsPerSession = some n) :
    ((trace p s es).filter newNeedsApproval).length ≤ n :=
  (bound id (·.approvalsThisSession) _ newNeedsApproval rfl
    (session_step (fun _ _ => step_le.2.2) fun _ _ h => (step_needsApproval h).2.1)
    (fun _ _ _ h => exceeded_lt (step_needsApproval h).2.2.1) s es).2 n hn

theorem steps_per_turn (hm : p.mode = .enforce) (hn : p.limits.maxStepsPerTurn = some n) :
    ((sinceTurn (trace p s es)).filter stepAccepted).length ≤ n :=
  (bound sinceTurn (·.stepsThisTurn) _ stepAccepted rfl
    (turn_step Le.steps fun _ _ h => (step_stepAccepted h).1)
    (fun _ _ _ h => (step_stepAccepted h).2 hm _) s es).2 n hn

namespace Limits

def limitPolicy : Policy :=
  { limits := { maxProposalsPerTurn := some 2, maxStepsPerTurn := some 1 }
    actions := [("t", {}), ("shadow", { mode := some .logOnly })] }

def turnEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "t" "d2" none [] []⟩
  , ⟨5, 5, 4, none, .turnEnd⟩
  , ⟨6, 6, 5, none, .propose "c3" "t" "d3" none [] []⟩
  , ⟨7, 7, 6, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨8, 8, 7, none, .propose "c4" "t" "d4" none [] []⟩
  , ⟨9, 9, 8, none, .propose "c5" "shadow" "d5" none [] []⟩ ]

def turnTrace : List (State × Event × Verdict) :=
  trace limitPolicy (State.initial "pd") turnEvents

#guard turnTrace.map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .allowed none, .ok .allowed none, .ok .none none,
       .ok (.denied .proposalLimit) none, .ok .allowed none, .ok (.denied .proposalLimit) none,
       .ok .allowed (some (.wouldDeny .proposalLimit)) ]
#guard (sinceTurn turnTrace).map (·.2.1.seq) == [3, 4, 5, 6, 7, 8, 9]
#guard (sinceTurn turnTrace).map (newAllowed limitPolicy)
  == [true, true, false, false, false, false, false]
#guard ((sinceTurn turnTrace).filter (newAllowed limitPolicy)).length == 2
#guard (turnTrace.getLast?.map fun x => x.1.proposalsThisTurn) == some 4

def sessionPolicy : Policy :=
  { limits := { maxProposalsPerSession := some 3 }, actions := [("t", {})] }

def sessionEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "t" "d2" none [] []⟩
  , ⟨5, 5, 4, none, .turnEnd⟩
  , ⟨6, 6, 5, none, .turnStart false⟩
  , ⟨7, 7, 6, none, .propose "c3" "t" "d3" none [] []⟩
  , ⟨8, 8, 7, none, .propose "c4" "t" "d4" none [] []⟩ ]

def sessionTrace : List (State × Event × Verdict) :=
  trace sessionPolicy (State.initial "pd") sessionEvents

#guard sessionTrace.map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .allowed none, .ok .allowed none, .ok .none none,
       .ok .none none, .ok .allowed none, .ok (.denied .sessionProposalLimit) none ]
#guard (sinceTurn sessionTrace).map (·.2.1.seq) == [7, 8]
#guard ((sinceTurn sessionTrace).filter (newAllowed sessionPolicy)).length == 1
#guard (sessionTrace.filter (newAllowed sessionPolicy)).length == 3

def stepEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .stepStart⟩
  , ⟨4, 4, 3, none, .stepStart⟩ ]

def stepTrace : List (State × Event × Verdict) :=
  trace limitPolicy (State.initial "pd") stepEvents

#guard stepTrace.map (·.2.2)
  == [.ok .none none, .ok .none none, .ok .none none, .rejected .stepLimit]
#guard ((sinceTurn stepTrace).filter stepAccepted).length == 1

/-- Under a `log_only` policy the second `step_start` is accepted, so `steps_per_turn` needs its
`enforce` hypothesis. -/
def shadowStepPolicy : Policy := { limitPolicy with mode := .logOnly }

#guard (trace shadowStepPolicy (State.initial "pd") stepEvents).map (·.2.2)
  == [.ok .none none, .ok .none none, .ok .none none, .ok .none (some (.wouldDeny .stepLimit))]
#guard ((sinceTurn (trace shadowStepPolicy (State.initial "pd") stepEvents)).filter
  stepAccepted).length == 2

def approvalPolicy : Policy :=
  { approverRoles := ["owner"]
    limits := { maxApprovalRequestsPerTurn := some 1, maxApprovalRequestsPerSession := some 2 }
    actions := [("pay", { consent := .perCall })] }

def approvalEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "pay" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "pay" "d2" none [] []⟩
  , ⟨5, 5, 4, none, .turnEnd⟩
  , ⟨6, 6, 5, none, .turnStart true⟩
  , ⟨7, 7, 6, none, .propose "c3" "pay" "d3" none [] []⟩
  , ⟨8, 8, 7, none, .turnEnd⟩
  , ⟨9, 9, 8, none, .turnStart true⟩
  , ⟨10, 10, 9, none, .propose "c4" "pay" "d4" none [] []⟩ ]

def approvalTrace : List (State × Event × Verdict) :=
  trace approvalPolicy (State.initial "pd") approvalEvents

#guard approvalTrace.map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) none,
       .ok (.denied .approvalBudget) none, .ok .none none, .ok .none none,
       .ok (.needsApproval ⟨"s1", "c3", 0⟩) none, .ok .none none, .ok .none none,
       .ok (.denied .sessionApprovalBudget) none ]
#guard ((sinceTurn (approvalTrace.take 4)).filter newNeedsApproval).length == 1
#guard (approvalTrace.filter newNeedsApproval).length == 2

def shadowApprovalPolicy : Policy :=
  { approvalPolicy with
    actions :=
      [("pay", { consent := .perCall }), ("note", { consent := .perCall, mode := some .logOnly })] }

def shadowApprovalEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "note" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "pay" "d2" none [] []⟩ ]

def shadowApprovalTrace : List (State × Event × Verdict) :=
  trace shadowApprovalPolicy (State.initial "pd") shadowApprovalEvents

#guard shadowApprovalTrace.map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .allowed (some .wouldNeedApproval),
       .ok (.needsApproval ⟨"s1", "c2", 0⟩) none ]
#guard shadowApprovalTrace.map (newAllowed shadowApprovalPolicy) == [false, false, false, true]
#guard ((sinceTurn shadowApprovalTrace).filter newNeedsApproval).length == 1

end Limits

end Writ.Proofs
