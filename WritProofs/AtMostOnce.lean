import WritProofs.Calls
import WritProofs.Dispatch
import WritProofs.WF

namespace Writ.Proofs

open Writ
open Basic

variable {p : Policy} {d : String} {s s' s₁ s₂ : State} {e : Event} {es : List Event} {k : String}
  {c c' c'' : CallRec} {r : Requirements} {st : CallStatus} {q q' : Prop}
  {u : String → Prop}

def claimOf (k : String) (x : State × Event × Verdict) : Option Nat :=
  match x.2.1.body with
  | .dispatch k' n .. => if k' = k ∧ x.2.2.claimed = true then some n else none
  | _ => none

def unknownAt (k : String) (x : State × Event × Verdict) : Bool :=
  x.2.1.body.unknownOf k && x.2.2.accepted

def claims (p : Policy) (d : String) (es : List Event) (k : String) : List Nat :=
  (trace p (State.initial d) es).filterMap (claimOf k)

def unknowns (p : Policy) (d : String) (es : List Event) (k : String) : Nat :=
  (trace p (State.initial d) es).countP (unknownAt k)

namespace AtMostOnce

def Open (st : CallStatus) : Prop := st = .awaiting ∨ st = .authorized

/-- Neither Open nor Unknown, so a handler that writes it opens no way to a claim. -/
def Done (st : CallStatus) : Prop := ¬Open st ∧ st ≠ .unknown

def rules (p : Policy) (c : CallRec) : Requirements := (p.action? c.tool).getD {}

/-- What a step other than a claim may do to a call record. A record turns Unknown only where
`u` holds: the call's own `outcome_unknown`, or a reset or session end. -/
structure RecKeep (u : Prop) (c c' : CallRec) : Prop where
  tool : c'.tool = c.tool
  epoch : c'.epoch = c.epoch
  attempts : c'.attempts = c.attempts
  isOpen : Open c'.status → Open c.status
  unknown : c'.status = .unknown → c.status = .unknown ∨ u

theorem RecKeep.refl : RecKeep q c c := ⟨rfl, rfl, rfl, id, .inl⟩

theorem RecKeep.trans (h : RecKeep q c c') (h' : RecKeep q c' c'') : RecKeep q c c'' where
  tool := h'.tool.trans h.tool
  epoch := h'.epoch.trans h.epoch
  attempts := h'.attempts.trans h.attempts
  isOpen o := h.isOpen (h'.isOpen o)
  unknown hu := (h'.unknown hu).elim h.unknown .inr

theorem RecKeep.mono (h : RecKeep q c c') (hq : q → q') : RecKeep q' c c' :=
  { h with unknown := fun hs => (h.unknown hs).imp_right hq }

theorem RecKeep.done (h : Done st) : RecKeep q c { c with status := st } :=
  ⟨rfl, rfl, rfl, fun o => absurd o h.1, fun hs => absurd hs h.2⟩

theorem RecKeep.opened (ho : Open c.status) (ho' : Open c'.status) (ht : c'.tool = c.tool)
    (he : c'.epoch = c.epoch) (ha : c'.attempts = c.attempts) : RecKeep q c c' :=
  ⟨ht, he, ha, fun _ => ho, fun hs => by rw [hs] at ho'; rcases ho' with h | h <;> cases h⟩

theorem RecKeep.unknownBy (h : q) : RecKeep q c { c with status := .unknown } :=
  ⟨rfl, rfl, rfl, fun o => (by rcases o with h | h <;> cases h), fun _ => .inr h⟩

structure Kept (u : String → Prop) (s s' : State) : Prop where
  calls : ∀ k c', s'.calls[k]? = some c' → ∃ c, s.calls[k]? = some c ∧ RecKeep (u k) c c'
  epoch : s.epoch ≤ s'.epoch
  ended : s.ended = true → s'.ended = true

structure Quiet (s s' : State) : Prop where
  calls : s'.calls = s.calls
  epoch : s'.epoch = s.epoch
  ended : s'.ended = s.ended

theorem Quiet.trans (h : Quiet s s₁) (h' : Quiet s₁ s₂) : Quiet s s₂ :=
  ⟨h'.calls.trans h.calls, h'.epoch.trans h.epoch, h'.ended.trans h.ended⟩

theorem Kept.refl : Kept u s s := ⟨fun _ c h => ⟨c, h, .refl⟩, Nat.le_refl _, id⟩

theorem Kept.trans (h : Kept u s s₁) (h' : Kept u s₁ s₂) : Kept u s s₂ where
  calls k c hc := by
    obtain ⟨c₁, h₁, r₁⟩ := h'.calls k c hc
    obtain ⟨c₀, h₀, r₀⟩ := h.calls k c₁ h₁
    exact ⟨c₀, h₀, r₀.trans r₁⟩
  epoch := Nat.le_trans h.epoch h'.epoch
  ended he := h'.ended (h.ended he)

theorem Quiet.kept (h : Quiet s s') : Kept u s s' :=
  ⟨fun _ c hc => ⟨c, by rw [← h.calls]; exact hc, .refl⟩, Nat.le_of_eq h.epoch.symm,
   fun he => by rw [h.ended]; exact he⟩

theorem Kept.quiet (h : Kept u s s₁) (h' : Quiet s₁ s₂) : Kept u s s₂ := h.trans h'.kept

theorem Kept.insert (hk : s.calls[k]? = some c) (hr : RecKeep (u k) c c') :
    Kept u s { s with calls := s.calls.insert k c' } := by
  refine ⟨fun x cx hx => ?_, Nat.le_refl _, id⟩
  simp only [Std.ExtTreeMap.getElem?_insert] at hx
  split at hx
  · rename_i he
    cases Std.LawfulEqCmp.eq_of_compare he
    cases hx
    exact ⟨c, hk, hr⟩
  · exact ⟨cx, hx, .refl⟩

theorem Kept.modify {f : CallRec → CallRec} (hf : ∀ c, RecKeep (u k) c (f c)) :
    Kept u s { s with calls := s.calls.modify k f } := by
  refine ⟨fun x cx hx => ?_, Nat.le_refl _, id⟩
  simp only [Std.ExtTreeMap.getElem?_modify] at hx
  split at hx
  · rename_i he
    cases Std.LawfulEqCmp.eq_of_compare he
    cases hk : s.calls[k]? with
    | none => simp [hk] at hx
    | some c =>
      simp only [hk, Option.map_some, Option.some.injEq] at hx; subst hx; exact ⟨c, rfl, hf c⟩
  · exact ⟨cx, hx, .refl⟩

theorem Kept.map {f : String → CallRec → CallRec} (hf : ∀ k c, RecKeep (u k) c (f k c)) :
    Kept u s { s with calls := s.calls.map f } := by
  refine ⟨fun x cx hx => ?_, Nat.le_refl _, id⟩
  simp only [Std.ExtTreeMap.getElem?_map] at hx
  cases hk : s.calls[x]? with
  | none => simp [hk] at hx
  | some c =>
    simp only [hk, Option.map_some, Option.some.injEq] at hx; subst hx; exact ⟨c, rfl, hf x c⟩

theorem releaseGrant_quiet : Quiet s (s.releaseGrant k) := by
  unfold State.releaseGrant; repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem consumeGrant_quiet : Quiet s (s.consumeGrant k) := by
  unfold State.consumeGrant; repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem recordFailure_quiet : Quiet s (s.recordFailure p t) := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem updateEntries_quiet : Quiet s (s.updateEntries p m t f) := by
  unfold State.updateEntries; split <;> exact ⟨rfl, rfl, rfl⟩

theorem settle_quiet : Quiet s (s.settle p ms k o a ne t).1 := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => Quiet s b.1) ?_ ms _ ⟨rfl, rfl, rfl⟩
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact h.trans updateEntries_quiet
  · split <;> exact h.trans updateEntries_quiet

theorem endCall_kept (h : Done st) : Kept u s (s.endCall k st) := by
  unfold State.endCall
  exact releaseGrant_quiet.kept.trans (Kept.modify fun _ => .done h)

local macro "rec_done" : tactic => `(tactic| exact ⟨by simp [Open], by simp⟩)

theorem cancelPending_kept : Kept u s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (Kept u s) ?_ _ _ Kept.refl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact ha.trans (endCall_kept (by rec_done))
  · exact ha.trans (endCall_kept (by rec_done))
  · exact ha

theorem interrupt_kept : Kept (fun _ => True) s s.interrupt := by
  unfold State.interrupt
  refine (cancelPending_kept.trans (Kept.map fun _ c => ?_)).quiet ⟨rfl, rfl, rfl⟩
  split
  · exact ⟨rfl, rfl, rfl, fun o => (by rcases o with h | h <;> cases h), fun _ => .inr trivial⟩
  · exact .refl

local macro "rec_kept" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Kept.refl
      | exact Quiet.kept ⟨rfl, rfl, rfl⟩
      | exact cancelPending_kept.quiet ⟨rfl, rfl, rfl⟩
      | exact endCall_kept (by rec_done)
      | exact (endCall_kept (by rec_done)).quiet ⟨rfl, rfl, rfl⟩)

theorem handleSessionStart_moved :
    Kept (fun _ => False) s (handleSessionStart s i a b ps as l).1 := by
  unfold handleSessionStart; rec_kept

theorem handleTurnStart_moved : Kept (fun _ => False) s (handleTurnStart s x).1 := by
  unfold handleTurnStart; rec_kept

theorem handleTurnEnd_moved : Kept (fun _ => False) s (handleTurnEnd s).1 := by
  unfold handleTurnEnd; rec_kept

theorem handleStepStart_moved : Kept (fun _ => False) s (handleStepStart p s).1 := by
  unfold handleStepStart; rec_kept

theorem handleApproverAttest_moved : Kept (fun _ => False) s (handleApproverAttest s a ai).1 := by
  unfold handleApproverAttest; rec_kept

theorem handlePermissionRevoke_moved : Kept (fun _ => False) s (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; rec_kept

theorem handleGrantCreate_moved :
    Kept (fun _ => False) s (handleGrantCreate p s n i a b dg sc mu mc nb ex rv).1 := by
  unfold handleGrantCreate; rec_kept

theorem handleGrantRevoke_moved : Kept (fun _ => False) s (handleGrantRevoke s i).1 := by
  unfold handleGrantRevoke; rec_kept

theorem handlePermissionAdd_moved : Kept (fun _ => False) s (handlePermissionAdd p s a b).1 := by
  unfold handlePermissionAdd; rec_kept

theorem handleEscalationAck_moved : Kept (fun _ => False) s (handleEscalationAck p s a n).1 := by
  unfold handleEscalationAck; rec_kept

theorem handleKill_moved : Kept (fun _ => False) s (handleKill p s).1 := by
  unfold handleKill; rec_kept

theorem handleLedgerSync_moved : Kept (fun _ => False) s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; rec_kept

theorem handleCancel_moved : Kept (fun _ => False) s (handleCancel s i).1 := by
  unfold handleCancel; rec_kept

theorem handleReject_moved : Kept (fun _ => False) s (handleReject p s i rid a).1 := by
  unfold handleReject; rec_kept

theorem handleApprovalExpire_moved : Kept (fun _ => False) s (handleApprovalExpire s i rid).1 := by
  unfold handleApprovalExpire; rec_kept

theorem handleSessionEnd_moved : Kept (fun _ => True) s (handleSessionEnd s).1 := by
  unfold handleSessionEnd
  exact ⟨interrupt_kept.calls, interrupt_kept.epoch, fun _ => rfl⟩

theorem handleReset_moved : Kept (fun _ => True) s (handleReset s).1 := by
  unfold handleReset
  exact ⟨interrupt_kept.calls, Nat.le_succ _, interrupt_kept.ended⟩

theorem get?_some {m : CallMap} (h : m.get? k = some c) : m[k]? = some c := by
  rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact h

theorem get?_none {m : CallMap} (h : m.get? k = none) : m[k]? = none := by
  rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact h

theorem handleOutcomeUnknown_moved : Kept (· = i) s (handleOutcomeUnknown p s i).1 := by
  unfold handleOutcomeUnknown
  split
  · exact Kept.refl
  · rename_i rc hrc
    split
    · exact Kept.refl
    · exact (Kept.insert (u := (· = i)) (get?_some hrc) (.unknownBy rfl)).quiet recordFailure_quiet

theorem outcome_done (o : Outcome) : Done o.status := by
  cases o <;> exact ⟨by simp [Open, Outcome.status], by simp [Outcome.status]⟩

theorem handleResult_moved : Kept (fun _ => False) s (handleResult p s t i o a ne).1 := by
  unfold handleResult
  split
  · exact Kept.refl
  · rename_i rc hrc
    split
    · exact Kept.refl
    · have h₁ : Kept (fun _ => False) s
          ((withStatus s i rc o.status).settle p (callMeters p rc) i o a ne t).1 :=
        (Kept.insert (get?_some hrc) (.done (outcome_done o))).quiet settle_quiet
      repeat' (first | (dsimp only) | split)
      all_goals first
        | exact h₁.quiet recordFailure_quiet
        | exact h₁.quiet ⟨rfl, rfl, rfl⟩
        | exact h₁

theorem handleReconcile_moved : Kept (fun _ => False) s (handleReconcile p s t i o a ne).1 := by
  unfold handleReconcile
  split
  · exact Kept.refl
  · rename_i rc hrc
    split
    · exact Kept.refl
    · split
      · exact Kept.refl
      · have h₁ : Kept (fun _ => False) s
            { s with calls := s.calls.insert i { rc with reconciled := some o } } :=
          Kept.insert (get?_some hrc) ⟨rfl, rfl, rfl, id, .inl⟩
        repeat' (first | (dsimp only) | split)
        all_goals first
          | exact (h₁.quiet settle_quiet).quiet recordFailure_quiet
          | exact h₁.quiet settle_quiet

theorem awaitingCheck_open (h : awaitingCheck p s k rid w = .ok rc) :
    s.calls[k]? = some rc ∧ Open rc.status := by
  unfold awaitingCheck at h
  cases hc : callCheck s k rid with
  | error => simp [hc, bind, Except.bind] at h
  | ok rc' =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    · cases h
      unfold callCheck at hc
      repeat' split at hc
      all_goals first
        | (cases hc; done)
        | (cases hc
           rename_i hrc hst _
           exact ⟨get?_some hrc, .inl (Classical.not_not.mp hst)⟩)

theorem applyApprove_moved (hk : s.calls[i]? = some rc) (ho : Open rc.status)
    (ha : applyApprove p s t i rc w pr dg cs ed = .ok res) : Kept (fun _ => False) s res.1 := by
  unfold applyApprove at ha
  dsimp only at ha
  iterate 6 (split at ha; · cases ha)
  next rc' hn =>
    have hf : rc'.tool = rc.tool ∧ rc'.epoch = rc.epoch ∧ rc'.attempts = rc.attempts ∧
        rc'.status = rc.status := by
      revert hn
      repeat' split
      all_goals (intro hn; cases hn <;> exact ⟨rfl, rfl, rfl, rfl⟩)
    split at ha <;> cases ha
    · exact Kept.insert hk (.opened ho (.inr rfl) hf.1 hf.2.1 hf.2.2.1)
    · exact Kept.insert hk (.opened ho (hf.2.2.2 ▸ ho) hf.1 hf.2.1 hf.2.2.1)

theorem handleApprove_moved : Kept (fun _ => False) s (handleApprove p s t i rid w dg cs ed).1 := by
  unfold handleApprove
  split
  · exact Kept.refl
  next rc hck =>
    dsimp only
    split
    · exact Kept.refl
    next ha => exact applyApprove_moved (awaitingCheck_open hck).1 (awaitingCheck_open hck).2 ha

/-- `Kept` plus the records a propose creates, which start with no attempts in the current epoch. -/
structure Moves (u : String → Prop) (s s' : State) : Prop where
  epoch : s.epoch ≤ s'.epoch
  ended : s.ended = true → s'.ended = true
  calls : ∀ k c', s'.calls[k]? = some c' →
    (∃ c, s.calls[k]? = some c ∧ RecKeep (u k) c c') ∨
      (s.calls[k]? = none ∧ c'.attempts = 0 ∧ c'.epoch = s.epoch)

theorem Kept.moves (h : Kept u s s') (hu : ∀ k, u k → u' k) : Moves u' s s' :=
  ⟨h.epoch, h.ended, fun k c' hc => by
    obtain ⟨c, hk, hr⟩ := h.calls k c' hc
    exact .inl ⟨c, hk, hr.mono (hu k)⟩⟩

theorem Kept.moves0 (h : Kept (fun _ => False) s s') : Moves u s s' := h.moves fun _ h => h.elim

theorem handlePropose_moved : Moves u s (handlePropose p s t k tool dg cs gs xs).1 := by
  unfold handlePropose
  split
  · repeat' (first | (dsimp only) | split)
    all_goals exact Kept.refl.moves0
  · rename_i hk
    split
    split
    · dsimp only
      refine (Quiet.kept ?_).moves0
      exact ⟨rfl, rfl, rfl⟩
    · dsimp only
      refine ⟨Nat.le_refl _, id, fun x c' hx => ?_⟩
      simp only [Std.ExtTreeMap.getElem?_insert] at hx
      split at hx
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        cases hx
        exact .inr ⟨get?_none hk, rfl, rfl⟩
      · exact .inl ⟨c', hx, .refl⟩

theorem handleDispatch_moved (h : (handleDispatch p s t i n dg cs g key).2.claimed = false) :
    Kept (fun _ => False) s (handleDispatch p s t i n dg cs g key).1 := by
  rcases Dispatch.handle_unclaimed h with he | ⟨-, st, -, -, hst, he⟩ <;> rw [he]
  · exact Kept.refl
  · exact endCall_kept (by rcases hst with rfl | ⟨_, rfl⟩ <;> rec_done)

theorem stepHandle_moves (hn : (stepHandle p s e).2.claimed = false) :
    Moves (fun k => e.body.unknownOf k = true ∨ s.epoch < (stepHandle p s e).1.epoch ∨
      (stepHandle p s e).1.ended = true) s (stepHandle p s e).1 := by
  revert hn
  unfold stepHandle
  split <;> rename_i hb <;> intro hn
  all_goals first
    | exact handleSessionEnd_moved.moves fun _ _ => .inr (.inr rfl)
    | exact handleReset_moved.moves fun _ _ => .inr (.inl (Nat.lt_succ_self _))
    | exact handleOutcomeUnknown_moved.moves fun k hk => .inl (by
        rw [hb, hk]; simp [EventBody.unknownOf])
    | exact (handleDispatch_moved hn).moves0
    | exact handlePropose_moved
    | with_reducible exact handleSessionStart_moved.moves0
    | with_reducible exact handleTurnStart_moved.moves0
    | with_reducible exact handleTurnEnd_moved.moves0
    | with_reducible exact handleStepStart_moved.moves0
    | with_reducible exact handleApproverAttest_moved.moves0
    | with_reducible exact handlePermissionRevoke_moved.moves0
    | with_reducible exact handleApprove_moved.moves0
    | with_reducible exact handleReject_moved.moves0
    | with_reducible exact handleApprovalExpire_moved.moves0
    | with_reducible exact handleGrantCreate_moved.moves0
    | with_reducible exact handleGrantRevoke_moved.moves0
    | with_reducible exact handleResult_moved.moves0
    | with_reducible exact handleReconcile_moved.moves0
    | with_reducible exact handleCancel_moved.moves0
    | with_reducible exact handleKill_moved.moves0
    | with_reducible exact handlePermissionAdd_moved.moves0
    | with_reducible exact handleEscalationAck_moved.moves0
    | with_reducible exact handleLedgerSync_moved.moves0

/-- What a claim needs of the stored record: a first attempt from Authorized, or a retry of an
Unknown call in the current epoch with attempts left. -/
def Claimable (p : Policy) (s : State) (rc : CallRec) : Prop :=
  rc.status = .authorized ∨
    rc.status = .unknown ∧ (rules p rc).retryAfterUnknown = true ∧ rc.epoch = s.epoch ∧
      rc.attempts < (rules p rc).maxAttempts

theorem claim_state :
    (claim p s t k rc r retry key).calls = s.calls.insert k
        { rc with status := .dispatched, attempts := rc.attempts + 1, idempotencyKey := some key } ∧
      (claim p s t k rc r retry key).epoch = s.epoch ∧
      (claim p s t k rc r retry key).ended = s.ended := by
  unfold claim
  dsimp only
  have hq : ∀ (f : State → String → State), (∀ s m, Quiet s (f s m)) →
      ∀ (l : List String) (s₀ : State), Quiet s s₀ → Quiet s (l.foldl f s₀) :=
    fun f hf l s₀ h₀ => foldl_invariant (Quiet s) (fun b m hb => hb.trans (hf b m)) l s₀ h₀
  split
  · have h := hq (fun s m => s.retime p m k t) (fun _ _ => updateEntries_quiet)
      (s.staleMeters p t r.meters k) s ⟨rfl, rfl, rfl⟩
    exact ⟨by rw [h.calls], h.epoch, h.ended⟩
  · have h := hq (fun s m => s.reserve p m k (p.callAmount m rc.cost) t)
      (fun _ _ => updateEntries_quiet) r.meters (s.consumeGrant k) consumeGrant_quiet
    exact ⟨by rw [h.calls], h.epoch, h.ended⟩

theorem step_claim (hr : Reachable p d s) (h : (step p s e).2.claimed = true) :
    ∃ i n dg cs g key rc, e.body = .dispatch i n dg cs g key ∧ s.calls[i]? = some rc ∧
      n = rc.attempts + 1 ∧ Claimable p s rc ∧ s.ended = false ∧
      (step p s e).1.calls = s.calls.insert i
        { rc with status := .dispatched, attempts := rc.attempts + 1, idempotencyKey := some key } ∧
      (step p s e).1.epoch = s.epoch ∧ (step p s e).1.ended = s.ended := by
  obtain ⟨i, n, dg, cs, g, key, hb⟩ := claimed_dispatch hr h
  obtain ⟨hen, rc, hrc, ⟨hst, hretry, hn, -⟩, -⟩ := (dispatch_claimed_iff hb).mp h
  have hc : Claimable p s rc := hst.elim .inl fun hu =>
    have ⟨_, ha, he, hat⟩ := hretry hu
    .inr ⟨hu, ha, he, hat⟩
  have hd : s.ended = false := by
    cases hs : s.ended
    · rfl
    · have := hen.2.1 hs
      rw [hb] at this
      cases this
  obtain ⟨hcalls, hep, hend⟩ := claim_state (p := p) (s := s) (t := e.time) (k := i) (rc := rc)
    (r := rules p rc) (retry := rc.status == .unknown) (key := key)
  rw [claim_post h hb hrc]
  exact ⟨i, n, dg, cs, g, key, rc, hb, hrc, hn, hc, hd, hcalls, hep, hend⟩

def UnknownSince (k : String) (T : List (State × Event × Verdict)) : Prop :=
  ∃ pre x post, T = pre ++ x :: post ∧ x.2.1.body.unknownOf k = true ∧ x.2.2.accepted = true ∧
    ∀ y ∈ post, y.2.2.claimed = true → y.2.1.body.dispatchOf k = false

variable {T : List (State × Event × Verdict)} {z : State × Event × Verdict}

theorem UnknownSince.snoc (h : UnknownSince k T)
    (hz : z.2.2.claimed = true → z.2.1.body.dispatchOf k = false) : UnknownSince k (T ++ [z]) := by
  obtain ⟨pre, x, post, hT, hx, ha, hp⟩ := h
  refine ⟨pre, x, post ++ [z], by rw [hT]; simp, hx, ha, fun y hy => ?_⟩
  rcases List.mem_append.mp hy with hy | hy
  · exact hp y hy
  · rw [List.mem_singleton.mp hy]; exact hz

theorem UnknownSince.last (hz : unknownAt k z = true) : UnknownSince k (T ++ [z]) := by
  simp only [unknownAt, Bool.and_eq_true] at hz
  exact ⟨T, z, [], rfl, hz.1, hz.2, fun _ hy => absurd hy List.not_mem_nil⟩

theorem claimOf_none (h : claimOf k z = none) :
    z.2.2.claimed = true → z.2.1.body.dispatchOf k = false := by
  intro hc
  obtain ⟨_, ⟨_, _, _, _, b⟩, v⟩ := z
  cases b <;> simp_all [claimOf, EventBody.dispatchOf]

theorem claimOf_unclaimed (h : z.2.2.claimed = false) : claimOf k z = none := by
  obtain ⟨_, ⟨_, _, _, _, b⟩, v⟩ := z
  cases b <;> simp_all [claimOf]

/-- What the trace so far says about call `k` while its record is `c`. An Unknown that a reset or
session end made is never retried (stale epoch, ended session), so only an Unknown in the
current epoch of a live session needs an `outcome_unknown` behind its last claim. -/
structure RecInv (p : Policy) (k : String) (s : State) (T : List (State × Event × Verdict))
    (c : CallRec) : Prop where
  claims : T.filterMap (claimOf k) = List.range' 1 c.attempts
  cap : c.attempts ≤ max 1 (rules p c).maxAttempts
  once : (rules p c).retryAfterUnknown = false → c.attempts ≤ 1
  unknowns : c.attempts ≤ T.countP (unknownAt k) + 1
  live : c.status = .unknown → c.epoch = s.epoch → s.ended = false →
    c.attempts ≤ T.countP (unknownAt k) ∧ (0 < c.attempts → UnknownSince k T)
  fresh : Open c.status → c.attempts = 0
  epoch : c.epoch ≤ s.epoch

structure TraceInv (p : Policy) (k : String) (s : State) (T : List (State × Event × Verdict)) :
    Prop where
  absent : s.calls[k]? = none → T.filterMap (claimOf k) = []
  present : ∀ c, s.calls[k]? = some c → RecInv p k s T c

theorem RecInv.moved (h : RecInv p k s T c)
    (hr : RecKeep (unknownAt k z = true ∨ s.epoch < s'.epoch ∨ s'.ended = true) c c')
    (hz : claimOf k z = none) (he : s.epoch ≤ s'.epoch) (hd : s.ended = true → s'.ended = true) :
    RecInv p k s' (T ++ [z]) c' where
  claims := by rw [List.filterMap_append, h.claims, hr.attempts]; simp [hz]
  cap := by unfold rules; rw [hr.attempts, hr.tool]; exact h.cap
  once := by unfold rules; rw [hr.attempts, hr.tool]; exact h.once
  unknowns := by rw [hr.attempts, List.countP_append]; have := h.unknowns; omega
  live hs hce hsd := by
    rw [hr.epoch] at hce
    have h₁ : c.epoch = s.epoch := by have := h.epoch; omega
    have h₂ : s.ended = false := by
      cases hx : s.ended
      · rfl
      · rw [hd hx] at hsd; cases hsd
    rw [hr.attempts, List.countP_append]
    rcases hr.unknown hs with hu | hu | hu | hu
    · obtain ⟨h₃, h₄⟩ := h.live hu h₁ h₂
      exact ⟨by omega, fun hp => (h₄ hp).snoc (claimOf_none hz)⟩
    · have h₃ := h.unknowns
      simp only [List.countP_singleton, hu, ite_true]
      exact ⟨by omega, fun _ => .last hu⟩
    · have := h.epoch; omega
    · rw [hu] at hsd; cases hsd
  fresh ho := by rw [hr.attempts]; exact h.fresh (hr.isOpen ho)
  epoch := by rw [hr.epoch]; exact Nat.le_trans h.epoch he

theorem RecInv.born (hT : T.filterMap (claimOf k) = []) (hz : claimOf k z = none)
    (ha : c.attempts = 0) (he : c.epoch ≤ s.epoch) : RecInv p k s (T ++ [z]) c where
  claims := by rw [List.filterMap_append, hT, ha]; simp [hz]
  cap := by rw [ha]; exact Nat.zero_le _
  once _ := by rw [ha]; exact Nat.zero_le _
  unknowns := by rw [ha]; exact Nat.zero_le _
  live _ _ _ :=
    ⟨by rw [ha]; exact Nat.zero_le _, fun hp => absurd hp (by rw [ha]; exact Nat.lt_irrefl 0)⟩
  fresh _ := ha
  epoch := he

theorem RecInv.claimed (h : RecInv p k s T rc) (hc : Claimable p s rc) (hd : s.ended = false)
    (hz : claimOf k z = some (rc.attempts + 1)) (hu : unknownAt k z = false)
    (he : s'.epoch = s.epoch) :
    RecInv p k s' (T ++ [z])
      { rc with status := .dispatched, attempts := rc.attempts + 1, idempotencyKey := some key }
    where
  claims := by
    rw [List.filterMap_append, h.claims]
    simp only [List.filterMap_cons, hz, List.filterMap_nil]
    rw [List.range'_concat]
    simp only [Nat.one_mul, Nat.add_comm]
  cap := by
    show rc.attempts + 1 ≤ max 1 (rules p rc).maxAttempts
    rcases hc with hst | ⟨_, _, _, hlt⟩
    · rw [h.fresh (.inr hst)]; exact Nat.le_max_left _ _
    · exact Nat.le_trans hlt (Nat.le_max_right _ _)
  once hn := by
    change (rules p rc).retryAfterUnknown = false at hn
    show rc.attempts + 1 ≤ 1
    rcases hc with hst | ⟨_, hy, _, _⟩
    · rw [h.fresh (.inr hst)]; exact Nat.le_refl _
    · rw [hn] at hy; cases hy
  unknowns := by
    show rc.attempts + 1 ≤ _
    rw [List.countP_append]
    simp only [List.countP_singleton, hu]
    rcases hc with hst | ⟨hst, _, hep, _⟩
    · rw [h.fresh (.inr hst)]; omega
    · have := (h.live hst hep hd).1; omega
  live hs := by cases hs
  fresh ho := by rcases ho with ho | ho <;> cases ho
  epoch := by rw [he]; exact h.epoch

theorem TraceInv.snoc (hr : Reachable p d s) (h : TraceInv p k s T) :
    TraceInv p k (step p s e).1 (T ++ [(s, e, (step p s e).2)]) := by
  by_cases hacc : (step p s e).2.accepted = true
  · by_cases hcl : (step p s e).2.claimed = true
    · obtain ⟨i, n, dg, cs, g, key, rc, hb, hrc, hn, hc, hd, hcalls, hep, hed⟩ := step_claim hr hcl
      have hu : unknownAt k (s, e, (step p s e).2) = false := by
        simp [unknownAt, hb, EventBody.unknownOf]
      by_cases hik : i = k
      · subst hik
        have hz : claimOf i (s, e, (step p s e).2) = some (rc.attempts + 1) := by
          simp [claimOf, hb, hcl, hn]
        refine ⟨fun hk => ?_, fun c hk => ?_⟩
        · rw [hcalls, Std.ExtTreeMap.getElem?_insert_self] at hk; cases hk
        · rw [hcalls, Std.ExtTreeMap.getElem?_insert_self] at hk
          cases hk
          exact (h.present rc hrc).claimed hc hd hz hu hep
      · have hz : claimOf k (s, e, (step p s e).2) = none := by simp [claimOf, hb, hik]
        have hk : (step p s e).1.calls[k]? = s.calls[k]? := by
          rw [hcalls, Std.ExtTreeMap.getElem?_insert]
          split
          · rename_i he; exact absurd (Std.LawfulEqCmp.eq_of_compare he) hik
          · rfl
        refine ⟨fun hk' => ?_, fun c hk' => ?_⟩
        · rw [hk] at hk'; rw [List.filterMap_append, h.absent hk']; simp [hz]
        · rw [hk] at hk'
          exact (h.present c hk').moved .refl hz (Nat.le_of_eq hep.symm)
            (fun hx => by rw [hed]; exact hx)
    · have hz : claimOf k (s, e, (step p s e).2) = none :=
        claimOf_unclaimed (Bool.eq_false_iff.mpr hcl)
      have hkeep : (step p s e).1.calls[k]? = none → s.calls[k]? = none := calls_keep
      have hacc' := hacc
      have hcl' := hcl
      rw [accepted_step hacc] at hacc' hcl' hz hkeep ⊢
      have hm := stepHandle_moves (Bool.eq_false_iff.mpr hcl')
      refine ⟨fun hk => ?_, fun c' hk => ?_⟩
      · rw [List.filterMap_append, h.absent (hkeep hk)]; simp [hz]
      · rcases hm.calls k c' hk with ⟨c, hc, hrk⟩ | ⟨hc, ha, he⟩
        · refine (h.present c hc).moved (hrk.mono fun hu => ?_) hz hm.epoch hm.ended
          rcases hu with hu | hu | hu
          · exact .inl (by simp [unknownAt, hu, hacc'])
          · exact .inr (.inl hu)
          · exact .inr (.inr hu)
        · exact RecInv.born (h.absent hc) hz ha (by rw [he]; exact hm.epoch)
  · have hf := frame (Bool.eq_false_iff.mpr hacc)
    have hz : claimOf k (s, e, (step p s e).2) = none := by
      refine claimOf_unclaimed ?_
      cases hv : (step p s e).2.claimed
      · rfl
      · exact absurd (claimed_accepted hv) hacc
    rw [hf]
    refine ⟨fun hk => ?_, fun c hk => (h.present c hk).moved .refl hz (Nat.le_refl _) id⟩
    rw [List.filterMap_append, h.absent hk]; simp [hz]

end AtMostOnce

open AtMostOnce

theorem traceInv (p : Policy) (d k : String) (es : List Event) :
    TraceInv p k (after p d es) (trace p (State.initial d) es) := by
  refine snoc_induction (P := fun es => TraceInv p k (after p d es) (trace p (State.initial d) es))
    ?_ (fun es e ih => ?_) es
  · exact ⟨fun _ => rfl, fun c hc => by simp [after_nil, State.initial] at hc⟩
  · rw [after_snoc, trace_snoc]
    exact ih.snoc reachable_after

theorem claims_need_call (h : (after p d es).calls[k]? = none) : claims p d es k = [] :=
  (traceInv p d k es).absent h

theorem at_most_once (hwf : p.WF) (hc : (after p d es).calls[k]? = some c)
    (hr : p.action? c.tool = some r) :
    (r.retryAfterUnknown = false → (claims p d es k).length ≤ 1) ∧
      (claims p d es k).length ≤ 1 + unknowns p d es k ∧
      (claims p d es k).length ≤ r.maxAttempts ∧
      claims p d es k = List.range' 1 (claims p d es k).length := by
  have h := (traceInv p d k es).present c hc
  have hrules : rules p c = r := by simp [rules, hr]
  have hlen : (claims p d es k).length = c.attempts := by
    rw [claims, h.claims, List.length_range']
  rw [hlen]
  refine ⟨fun hn => h.once (by rw [hrules]; exact hn), ?_, ?_, h.claims⟩
  · have := h.unknowns
    unfold unknowns
    omega
  · have := h.cap
    rw [hrules, Nat.max_eq_right (WF.maxAttempts_pos hwf hr)] at this
    exact this

theorem retry_after_unknown (hc : (step p (after p d es) e).2.claimed = true)
    (hk : e.body.dispatchOf k = true) (hn : claims p d es k ≠ []) :
    ∃ pre x post, trace p (State.initial d) es = pre ++ x :: post ∧
      x.2.1.body.unknownOf k = true ∧ x.2.2.accepted = true ∧
      ∀ y ∈ post, y.2.2.claimed = true → y.2.1.body.dispatchOf k = false := by
  obtain ⟨i, n, dg, cs, g, key, rc, hb, hrc, -, hst, hd, -⟩ := step_claim reachable_after hc
  have hik : i = k := by
    rw [hb] at hk
    simpa [EventBody.dispatchOf] using hk
  subst hik
  have h := (traceInv p d i es).present rc hrc
  have hpos : 0 < rc.attempts := by
    have hcl := h.claims
    cases ha : rc.attempts with
    | zero => rw [ha] at hcl; exact absurd hcl hn
    | succ => exact Nat.succ_pos _
  rcases hst with hst | ⟨hst, -, hep, -⟩
  · exact absurd (h.fresh (.inr hst)) (Nat.pos_iff_ne_zero.mp hpos)
  · exact (h.live hst hep hd).2 hpos

namespace AtMostOnce

def retryPolicy : Policy :=
  { actions := [("t", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 })] }

def retryOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" none [] "k1"⟩ ]

def retryUnknown : List Event := retryOpen ++ [⟨5, 5, 4, none, .outcomeUnknown "c1"⟩]

def retryEvent : Event := ⟨6, 6, 5, none, .dispatch "c1" 2 "d1" none [] "k1"⟩

def retryTwice : List Event :=
  retryUnknown ++ [retryEvent, ⟨7, 7, 6, none, .outcomeUnknown "c1"⟩]

def thirdEvent : Event := ⟨8, 8, 7, none, .dispatch "c1" 3 "d1" none [] "k1"⟩

def resetEvents : List Event := retryOpen ++ [⟨5, 5, 4, none, .reset⟩]

#guard decide retryPolicy.WF
#guard (trace retryPolicy (State.initial "pd") retryTwice).map (·.2.2.accepted)
  == [true, true, true, true, true, true, true]
#guard claims retryPolicy "pd" retryTwice "c1" == [1, 2]
#guard unknowns retryPolicy "pd" retryTwice "c1" == 2
#guard ((after retryPolicy "pd" retryTwice).calls["c1"]?).isSome
#guard (step retryPolicy (after retryPolicy "pd" retryUnknown) retryEvent).2.claimed
#guard retryEvent.body.dispatchOf "c1"
#guard claims retryPolicy "pd" retryUnknown "c1" == [1]
#guard (step retryPolicy (after retryPolicy "pd" retryTwice) thirdEvent).2
  == .rejected .attemptLimit
#guard (trace retryPolicy (State.initial "pd") resetEvents).map (·.2.2.accepted)
  == [true, true, true, true, true]
#guard (step retryPolicy (after retryPolicy "pd" resetEvents) retryEvent).2
  == .rejected .staleRequest

def endedEvents : List Event := retryOpen ++ [⟨5, 5, 4, none, .sessionEnd⟩]

#guard (trace retryPolicy (State.initial "pd") endedEvents).all (·.2.2.accepted)
#guard ((after retryPolicy "pd" endedEvents).calls["c1"]?.map (·.status)) == some .unknown
#guard (step retryPolicy (after retryPolicy "pd" endedEvents) retryEvent).2
  == .rejected .sessionEnded

#guard (witnessPolicy.action? "t").any (!·.retryAfterUnknown)
#guard (trace witnessPolicy (State.initial "pd") retryUnknown).all (·.2.2.accepted)
#guard claims witnessPolicy "pd" retryUnknown "c1" == [1]
#guard (step witnessPolicy (after witnessPolicy "pd" retryUnknown) retryEvent).2
  == .rejected .retryNotAllowed

end AtMostOnce

end Writ.Proofs
