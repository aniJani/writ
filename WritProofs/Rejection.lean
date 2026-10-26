import WritProofs.Escalation
import WritProofs.Origin

namespace Writ.Proofs

open Writ
open Basic

namespace Rejection

variable {p : Policy} {s : State} {e : Event} {x : String × String}

theorem releaseGrant_mem : (s.releaseGrant k).rejectedMemory = s.rejectedMemory := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem consumeGrant_mem : (s.consumeGrant k).rejectedMemory = s.rejectedMemory := by
  unfold State.consumeGrant; repeat' split
  all_goals rfl

theorem recordFailure_mem {tool : String} :
    (s.recordFailure p tool).rejectedMemory = s.rejectedMemory := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem updateEntries_mem : (s.updateEntries p m t f).rejectedMemory = s.rejectedMemory := by
  unfold State.updateEntries; split <;> rfl

theorem foldl_mem {α : Type _} {f : State → α → State}
    (hf : ∀ s a, (f s a).rejectedMemory = s.rejectedMemory) (l : List α) (s : State) :
    (l.foldl f s).rejectedMemory = s.rejectedMemory :=
  foldl_invariant (fun b : State => b.rejectedMemory = s.rejectedMemory)
    (fun b a hb => (hf b a).trans hb) l s rfl

theorem settle_mem : (s.settle p ms k o a ne t).1.rejectedMemory = s.rejectedMemory := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.rejectedMemory = s.rejectedMemory)
    ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact updateEntries_mem.trans h
  · split <;> exact updateEntries_mem.trans h

theorem endCall_mem : (s.endCall k st).rejectedMemory = s.rejectedMemory := releaseGrant_mem

theorem cancelPending_mem : (cancelPending s).rejectedMemory = s.rejectedMemory := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b : State => b.rejectedMemory = s.rejectedMemory) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact endCall_mem.trans ha
  · exact endCall_mem.trans ha
  · exact ha

theorem interrupt_mem : s.interrupt.rejectedMemory = s.rejectedMemory := cancelPending_mem

theorem claim_mem {r : Requirements} {key : String} {retry : Bool} :
    (claim p s t k rc r retry key).rejectedMemory = s.rejectedMemory := by
  unfold claim
  dsimp only
  split
  · exact foldl_mem (fun _ _ => updateEntries_mem) _ _
  · exact (foldl_mem (fun _ _ => updateEntries_mem) _ _).trans consumeGrant_mem

local macro "mem_keeps" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | rfl
      | exact cancelPending_mem
      | exact interrupt_mem
      | exact endCall_mem
      | exact claim_mem
      | (simp only [recordFailure_mem, settle_mem, withStatus, State.recordSuccess]; done)
      | (rw [recordFailure_mem]; exact settle_mem)
      | exact settle_mem)

theorem applyApprove_mem (h : applyApprove p s t k rc w pr dg c ed = .ok r) :
    r.1.rejectedMemory = s.rejectedMemory := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

theorem handleApprove_mem :
    (handleApprove p s t i r w dg c ed).1.rejectedMemory = s.rejectedMemory := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | rfl
    | exact applyApprove_mem (by assumption)

theorem mem_add_of {m : List (String × String)} {y : String × String} (h : x ∈ m) :
    x ∈ (if y ∈ m then m else m ++ [y]) := by
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_add_self {m : List (String × String)} {y : String × String} :
    y ∈ (if y ∈ m then m else m ++ [y]) := by
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_elim_of {m : List (String × String)} {o : Option String}
    {f : String → List (String × String)} (h : x ∈ m) (hf : ∀ d, x ∈ m → x ∈ f d) :
    x ∈ o.elim m f := by
  cases o
  · exact h
  · exact hf _ h

theorem vetoCheck_ok (h : vetoCheck p s k rid w = .ok rc) : s.calls[k]? = some rc := by
  unfold vetoCheck at h
  repeat' split at h
  all_goals (cases h <;> assumption)

theorem handleReject_records (ha : (handleReject p s k rid w).2.accepted = true)
    (hc : s.calls[k]? = some c) :
    (c.tool, c.proposedDigest) ∈ (handleReject p s k rid w).1.rejectedMemory ∧
      (c.tool, c.digest) ∈ (handleReject p s k rid w).1.rejectedMemory ∧
      ∀ y, c.generations[rid.generation]? = some y →
        (c.tool, y.1) ∈ (handleReject p s k rid w).1.rejectedMemory := by
  revert ha
  unfold handleReject
  split
  · simp [Verdict.accepted]
  rename_i rc hv
  rw [vetoCheck_ok hv] at hc
  cases hc
  intro _
  dsimp only
  refine ⟨mem_elim_of (mem_add_of mem_add_self) (fun _ => mem_add_of),
    mem_elim_of mem_add_self (fun _ => mem_add_of), fun y hy => ?_⟩
  rw [hy]
  exact mem_add_self

theorem handleReject_mem (hx : x ∈ s.rejectedMemory) :
    x ∈ (handleReject p s k rid w).1.rejectedMemory := by
  unfold handleReject
  split
  · exact hx
  · exact mem_elim_of (mem_add_of (mem_add_of hx)) (fun _ => mem_add_of)

theorem handleDispatch_mem :
    (handleDispatch p s t i n dg c g key).1.rejectedMemory = s.rejectedMemory := by
  rcases Dispatch.handle_cases with he | ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] <;>
    mem_keeps

theorem keep_of {s' : State} (h : s'.rejectedMemory = s.rejectedMemory)
    (hx : x ∈ s.rejectedMemory) : x ∈ s'.rejectedMemory := h ▸ hx

theorem stepHandle_mem (hx : x ∈ s.rejectedMemory) :
    x ∈ (stepHandle p s e).1.rejectedMemory ∨ e.body = .turnStart true := by
  unfold stepHandle
  split <;> rename_i hb
  · exact .inl (keep_of (by unfold handleSessionStart; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleSessionEnd; mem_keeps) hx)
  · unfold handleTurnStart
    split
    · exact .inl hx
    · rename_i u _
      cases u
      · exact .inl hx
      · exact .inr hb
  · exact .inl (keep_of (by unfold handleTurnEnd; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleStepStart; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleApproverAttest; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handlePermissionRevoke; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handlePropose; mem_keeps) hx)
  · exact .inl (keep_of handleApprove_mem hx)
  · exact .inl (handleReject_mem hx)
  · exact .inl (keep_of (by unfold handleApprovalExpire; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleGrantCreate; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleGrantRevoke; mem_keeps) hx)
  · exact .inl (keep_of handleDispatch_mem hx)
  · exact .inl (keep_of (by unfold handleResult; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleOutcomeUnknown; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleReconcile; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleCancel; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleReset; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleKill; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handlePermissionAdd; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleEscalationAck; mem_keeps) hx)
  · exact .inl (keep_of (by unfold handleLedgerSync; mem_keeps) hx)

theorem enforce_rejected {tool dg : String} {gs es : List (String × Bool)}
    (hx : (tool, dg) ∈ s.rejectedMemory) :
    ∃ x, (enforceDecision p s t k tool dg cost gs es).1 = .denied x := by
  have hpre : preConsentDenial p s t ((p.action? tool).getD {}) tool dg cost gs ≠ none := by
    unfold preConsentDenial
    repeat' split
    all_goals simp_all
  unfold enforceDecision
  dsimp only
  repeat' split
  all_goals first
    | exact ⟨_, rfl⟩
    | exact (hpre (by assumption)).elim

theorem applyApprove_fresh (h : applyApprove p s t k rc w pr dg c ed = .ok r) :
    (rc.tool, rc.digest) ∉ s.rejectedMemory ∧
      ∀ y, ed = some y → (rc.tool, y.newDigest) ∉ s.rejectedMemory := by
  unfold applyApprove at h
  dsimp only at h
  split at h
  · cases h
  rename_i hn
  exact ⟨fun hm => hn (by simp [hm]), fun y hy hm => hn (by simp [hy, hm])⟩

theorem handleApprove_fresh (ha : (handleApprove p s t k rid w dg c ed).2.accepted = true)
    (hc : s.calls[k]? = some rc) :
    (rc.tool, rc.digest) ∉ s.rejectedMemory ∧
      ∀ y, ed = some y → (rc.tool, y.newDigest) ∉ s.rejectedMemory := by
  unfold handleApprove at ha
  split at ha
  · simp [Verdict.accepted] at ha
  rename_i rc' hk
  rw [awaitingCheck_ok hk] at hc
  cases hc
  dsimp only at ha
  split at ha
  · simp [Verdict.accepted] at ha
  · exact applyApprove_fresh (by assumption)

theorem mem_add_cases {m : List (String × String)} {y : String × String}
    (h : x ∈ (if y ∈ m then m else m ++ [y])) : x ∈ m ∨ x = y := by
  split at h
  · exact .inl h
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · exact .inr (List.mem_singleton.mp h)

/-- Pair `x` comes from the record of call `k` that a `reject` echoing `rid` read: the call's tool
with its proposed digest, its current digest or the digest of the echoed generation. -/
def Recorded (s : State) (k : String) (rid : RequestId) (x : String × String) : Prop :=
  ∃ c, s.calls[k]? = some c ∧ x.1 = c.tool ∧
    (x.2 = c.proposedDigest ∨ x.2 = c.digest ∨
      (c.generations[rid.generation]?.map (·.1)) = some x.2)

theorem handleReject_back (hx : x ∈ (handleReject p s k rid w).1.rejectedMemory) :
    x ∈ s.rejectedMemory ∨
      ((handleReject p s k rid w).2.accepted = true ∧ Recorded s k rid x) := by
  revert hx
  unfold handleReject
  split
  · exact .inl
  · rename_i rc hv
    have hc := vetoCheck_ok hv
    intro hx
    dsimp only at hx
    have hM : ∀ {y : String × String}, y ∈ (if (rc.tool, rc.digest) ∈
        (if (rc.tool, rc.proposedDigest) ∈ s.rejectedMemory then s.rejectedMemory
          else s.rejectedMemory ++ [(rc.tool, rc.proposedDigest)])
        then (if (rc.tool, rc.proposedDigest) ∈ s.rejectedMemory then s.rejectedMemory
          else s.rejectedMemory ++ [(rc.tool, rc.proposedDigest)])
        else (if (rc.tool, rc.proposedDigest) ∈ s.rejectedMemory then s.rejectedMemory
          else s.rejectedMemory ++ [(rc.tool, rc.proposedDigest)]) ++ [(rc.tool, rc.digest)]) →
        y ∈ s.rejectedMemory ∨ (Verdict.ok .none none).accepted = true ∧ Recorded s k rid y := by
      intro y hy
      rcases mem_add_cases hy with hy | rfl
      · rcases mem_add_cases hy with hy | rfl
        · exact .inl hy
        · exact .inr ⟨rfl, rc, hc, rfl, .inl rfl⟩
      · exact .inr ⟨rfl, rc, hc, rfl, .inr (.inl rfl)⟩
    cases ho : rc.generations[rid.generation]? with
    | none =>
      rw [ho] at hx
      exact hM hx
    | some y =>
      rw [ho] at hx
      rcases mem_add_cases hx with hx | rfl
      · exact hM hx
      · exact .inr ⟨rfl, rc, hc, rfl, .inr (.inr (by rw [ho]; rfl))⟩

theorem back_of {s' : State} (h : s'.rejectedMemory = s.rejectedMemory)
    (hx : x ∈ s'.rejectedMemory) : x ∈ s.rejectedMemory := h ▸ hx

theorem stepHandle_back :
    x ∈ (stepHandle p s e).1.rejectedMemory → x ∈ s.rejectedMemory ∨
      ∃ k rid a, e.body = .reject k rid a ∧ (stepHandle p s e).2.accepted = true ∧
        Recorded s k rid x := by
  unfold stepHandle
  split <;> rename_i hb
  · exact fun hx => .inl (back_of (by unfold handleSessionStart; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleSessionEnd; mem_keeps) hx)
  · intro hx
    unfold handleTurnStart at hx
    split at hx
    · exact .inl hx
    · dsimp only at hx
      split at hx
      · simp at hx
      · exact .inl hx
  · exact fun hx => .inl (back_of (by unfold handleTurnEnd; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleStepStart; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleApproverAttest; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handlePermissionRevoke; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handlePropose; mem_keeps) hx)
  · exact fun hx => .inl (back_of handleApprove_mem hx)
  · intro hx
    rcases handleReject_back hx with h | ⟨ha, hrec⟩
    · exact .inl h
    · exact .inr ⟨_, _, _, hb, ha, hrec⟩
  · exact fun hx => .inl (back_of (by unfold handleApprovalExpire; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleGrantCreate; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleGrantRevoke; mem_keeps) hx)
  · exact fun hx => .inl (back_of handleDispatch_mem hx)
  · exact fun hx => .inl (back_of (by unfold handleResult; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleOutcomeUnknown; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleReconcile; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleCancel; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleReset; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleKill; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handlePermissionAdd; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleEscalationAck; mem_keeps) hx)
  · exact fun hx => .inl (back_of (by unfold handleLedgerSync; mem_keeps) hx)

end Rejection

open Rejection

variable {p : Policy} {s : State} {e : Event}

/-- Section 8, theorem 12: an accepted `reject` records the call's tool with its proposed digest,
its current digest and the digest of the generation the reject echoed. -/
theorem reject_records {k a : String} {rid : RequestId} {c : CallRec}
    (h : (step p s e).2.accepted = true) (he : e.body = .reject k rid a)
    (hc : s.calls[k]? = some c) :
    (c.tool, c.proposedDigest) ∈ (step p s e).1.rejectedMemory ∧
      (c.tool, c.digest) ∈ (step p s e).1.rejectedMemory ∧
      ∀ x, c.generations[rid.generation]? = some x →
        (c.tool, x.1) ∈ (step p s e).1.rejectedMemory := by
  have ha : (stepHandle p s e).2.accepted = true := by
    have h' := h; rw [accepted_step h] at h'; exact h'
  rw [accepted_step h]
  simp only [stepHandle, he] at ha ⊢
  exact handleReject_records ha hc

/-- Section 8, theorem 12: a rejected pair leaves the memory only at an accepted `turn_start`
with `user_initiated: true`. -/
theorem memory_persists {x : String × String} (hx : x ∈ s.rejectedMemory)
    (hgone : x ∉ (step p s e).1.rejectedMemory) :
    e.body = .turnStart true ∧ (step p s e).2.accepted = true := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha] at hgone; exact absurd hx hgone
  · rw [accepted_step ha] at hgone
    rcases stepHandle_mem (p := p) (e := e) hx with h | h
    · exact absurd h hgone
    · exact ⟨h, rfl⟩

/-- Section 8, theorem 12 at propose: a new call of an enforced action with a rejected pair is
denied. -/
theorem rejected_propose {k t dg : String} {cost : Option Cost} {gs esc : List (String × Bool)}
    (hx : (t, dg) ∈ s.rejectedMemory) (he : e.body = .propose k t dg cost gs esc)
    (hnew : s.calls[k]? = none) (hm : p.modeOf t = .enforce) :
    ∀ dc sh, (step p s e).2 = .ok dc sh → ∃ r, dc = .denied r := by
  intro dc sh hv
  have ha : (step p s e).2.accepted = true := by rw [hv]; rfl
  rw [accepted_step ha] at hv
  simp only [stepHandle, he] at hv
  exact Escalation.handlePropose_new hnew (enforce_rejected hx) hm hv

/-- Section 8, theorem 12 at approval: an accepted approval, in any mode, is of a call whose
current digest was not rejected, and an edit's new digest was not rejected either. -/
theorem rejected_approve {k a dg : String} {rid : RequestId} {cost : Option Cost}
    {ed : Option Edit} {c : CallRec} (h : (step p s e).2.accepted = true)
    (he : e.body = .approve k rid a dg cost ed) (hc : s.calls[k]? = some c) :
    (c.tool, c.digest) ∉ s.rejectedMemory ∧
      ∀ x, ed = some x → (c.tool, x.newDigest) ∉ s.rejectedMemory := by
  have ha : (stepHandle p s e).2.accepted = true := by
    have h' := h; rw [accepted_step h] at h'; exact h'
  simp only [stepHandle, he] at ha
  exact handleApprove_fresh ha hc

/-- Section 8, theorem 12 at dispatch: a claimed first attempt of an enforced action has a pair
that was not rejected, whenever the call was proposed. -/
theorem rejected_claim {k dg key : String} {n : Nat} {cost : Option Cost}
    {g : List (String × Bool)} {c : CallRec} (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .authorized) (hm : p.modeOf c.tool = .enforce) :
    (c.tool, c.digest) ∉ s.rejectedMemory := by
  obtain ⟨-, c', hc', -, hok⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  exact (hok hm).1.2.2.1 (by rw [hst]; nofun)

theorem Rejection.memory_run {es : List Event} {x : String × String} (hx : x ∈ s.rejectedMemory)
    (hturn : ∀ y ∈ trace p s es, y.2.2.accepted = true → y.2.1.body ≠ .turnStart true) :
    x ∈ (run p s es).1.rejectedMemory := by
  induction es generalizing s with
  | nil => exact hx
  | cons e es ih =>
    rw [Basic.run_cons_fst]
    refine ih ?_ fun y hy => hturn y (List.mem_cons_of_mem _ hy)
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨hb, ha⟩ := memory_persists hx hn
    exact hturn _ List.mem_cons_self ha hb

variable {d : String} {es : List Event}

/-- Section 8, theorem 12: every pair in rejection memory was recorded by an accepted `reject` of
the trace from the record `c` of the call it rejected: the call's tool with its proposed digest,
its current digest or the digest of the generation the reject echoed. That digest is the digest
the events carried for some generation of the call. -/
theorem memory_origin {x : String × String} (hx : x ∈ (after p d es).rejectedMemory) :
    ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
      ∃ k rid a c, e₀.body = .reject k rid a ∧ s₀.calls[k]? = some c ∧ x.1 = c.tool ∧
        (x.2 = c.proposedDigest ∨ x.2 = c.digest ∨
          (c.generations[rid.generation]?.map (·.1)) = some x.2) ∧
        ∃ g, GenerationDigest p d es k x.1 g x.2 := by
  refine snoc_induction (P := fun es => ∀ x, x ∈ (after p d es).rejectedMemory →
    ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
      ∃ k rid a c, e₀.body = .reject k rid a ∧ s₀.calls[k]? = some c ∧ x.1 = c.tool ∧
        (x.2 = c.proposedDigest ∨ x.2 = c.digest ∨
          (c.generations[rid.generation]?.map (·.1)) = some x.2) ∧
        ∃ g, GenerationDigest p d es k x.1 g x.2)
    (fun x h => by simp [after_nil, State.initial] at h) ?_ es x hx
  intro es e ih x hx
  rw [after_snoc] at hx
  have hold : x ∈ (after p d es).rejectedMemory → ∃ s₀ e₀ v₀,
      (s₀, e₀, v₀) ∈ trace p (State.initial d) (es ++ [e]) ∧ v₀.accepted = true ∧
      ∃ k rid a c, e₀.body = .reject k rid a ∧ s₀.calls[k]? = some c ∧ x.1 = c.tool ∧
        (x.2 = c.proposedDigest ∨ x.2 = c.digest ∨
          (c.generations[rid.generation]?.map (·.1)) = some x.2) ∧
        ∃ g, GenerationDigest p d (es ++ [e]) k x.1 g x.2 := fun h => by
    obtain ⟨s₀, e₀, v₀, hm, ha, k, rid, a, c, hb, hc, ht, hd, g, hg⟩ := ih x h
    exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, ha, k, rid, a, c, hb, hc, ht, hd, g,
      Origin.generation_mono hg⟩
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at hx
    exact hold hx
  rw [accepted_step ha] at hx
  rcases stepHandle_back hx with h | ⟨k, rid, a, hb, -, c, hc, ht, hd⟩
  · exact hold h
  obtain ⟨-, -, h0, hcur, hgd⟩ := call_origin hc
  refine ⟨_, _, _, trace_mem_last, ha, k, rid, a, c, hb, hc, ht, hd, ?_⟩
  rw [ht]
  rcases hd with hd | hd | hd
  · exact ⟨0, Origin.generation_mono (hd ▸ hgd 0 _ h0)⟩
  · exact ⟨c.generation, Origin.generation_mono (hd ▸ hgd c.generation _ hcur)⟩
  · cases hy : c.generations[rid.generation]? with
    | none => rw [hy] at hd; cases hd
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at hd
      exact ⟨rid.generation, Origin.generation_mono (hd ▸ hgd _ y hy)⟩

/-- Section 8, theorem 12 over events: after an accepted `reject` of call `k`, until an accepted
`turn_start` with `user_initiated: true`, a new call of an enforced action that proposes the
call's tool `t` with the digest of its generation 0, of the generation the reject echoed, or of
its last generation before the reject, as the events carried them, is denied. -/
theorem rejected_until_user_turn {es₁ es₂ : List Event} {e₀ : Event} {k k' t dg a : String}
    {rid : RequestId} {g : Nat} {cost : Option Cost} {gs esc : List (String × Bool)}
    (hr : (step p (after p d es₁) e₀).2.accepted = true) (hb : e₀.body = .reject k rid a)
    (hg : GenerationDigest p d es₁ k t g dg)
    (hwhich : g = 0 ∨ g = rid.generation ∨
      ∀ g' dg', GenerationDigest p d es₁ k t g' dg' → g' ≤ g)
    (hturn : ∀ x ∈ trace p (after p d (es₁ ++ [e₀])) es₂, x.2.2.accepted = true →
      x.2.1.body ≠ .turnStart true)
    (he : e.body = .propose k' t dg cost gs esc)
    (hnew : (after p d (es₁ ++ e₀ :: es₂)).calls[k']? = none) (hm : p.modeOf t = .enforce) :
    ∀ dc sh, (step p (after p d (es₁ ++ e₀ :: es₂)) e).2 = .ok dc sh → ∃ r, dc = .denied r := by
  obtain ⟨c, hc, ht, hdg⟩ := generation_recorded hg
  obtain ⟨-, hlen, h0, hcur, hgd⟩ := call_origin hc
  obtain ⟨hp, hd, hecho⟩ := reject_records hr hb hc
  have hx : (t, dg) ∈ (step p (after p d es₁) e₀).1.rejectedMemory := by
    rw [← ht]
    rcases hwhich with rfl | rfl | hlast
    · rw [h0] at hdg
      cases hdg
      exact hp
    · cases hy : c.generations[rid.generation]? with
      | none => rw [hy] at hdg; cases hdg
      | some y =>
        rw [hy] at hdg
        cases hdg
        exact hecho y hy
    · have hle := hlast c.generation c.digest (ht ▸ hgd c.generation _ hcur)
      have hlt : g < c.generations.length := by
        cases hy : c.generations[g]? with
        | none => rw [hy] at hdg; cases hdg
        | some y => exact (List.getElem?_eq_some_iff.mp hy).1
      have hge : g = c.generation := by omega
      subst hge
      rw [hcur] at hdg
      cases hdg
      exact hd
  have hrun : after p d (es₁ ++ e₀ :: es₂) = (run p (step p (after p d es₁) e₀).1 es₂).1 := by
    rw [after_append, Basic.run_cons_fst]
  rw [after_snoc] at hturn
  rw [hrun] at hnew ⊢
  exact rejected_propose (Rejection.memory_run hx hturn) he hnew hm

namespace Rejection

def rejPolicy : Policy :=
  { approverRoles := ["owner"]
    actions := [("t", { consent := .perCall }), ("u", {}),
      ("q", { consent := .quorum 2 none true false })] }

def ev (n : Nat) (b : EventBody) : Event := ⟨n, n, n - 1, none, b⟩

def start : Event :=
  ev 1 (.sessionStart "s1" "pd" "u1" []
    [("a1", ⟨"alice", .human, ["owner"]⟩), ("a2", ⟨"bob", .human, ["owner"]⟩)] {})

/-- `c2` and `c4` of `t` share the digest `d1` of `c1`; `c2` is authorized before `c1` is
rejected. `c5` of `u` needs no approval and is rejected while authorized. -/
def rejOpen : List Event :=
  [ start
  , ev 2 (.turnStart true)
  , ev 3 (.propose "c1" "t" "d1" none [] [])
  , ev 4 (.propose "c2" "t" "d1" none [] [])
  , ev 5 (.propose "c4" "t" "d1" none [] [])
  , ev 6 (.propose "c3" "t" "d3" none [] [])
  , ev 7 (.propose "c5" "u" "d5" none [] [])
  , ev 8 (.approve "c2" ⟨"s1", "c2", 0⟩ "a1" "d1" none none)
  , ev 9 (.reject "c1" ⟨"s1", "c1", 0⟩ "a2")
  , ev 10 (.reject "c5" ⟨"s1", "c5", 0⟩ "a2") ]

def sRej : State := after rejPolicy "pd" rejOpen

def proposeT : Nat → Event := fun n => ev n (.propose "c9" "t" "d1" none [] [])
def proposeU : Nat → Event := fun n => ev n (.propose "c6" "u" "d5" none [] [])
def dispatchC2 : Event := ev 11 (.dispatch "c2" 1 "d1" none [] "k2")

#guard decide rejPolicy.WF
#guard ["t", "u", "q"].all (rejPolicy.modeOf · == .enforce)
#guard (trace rejPolicy (State.initial "pd") rejOpen).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) none
     , .ok (.needsApproval ⟨"s1", "c2", 0⟩) none, .ok (.needsApproval ⟨"s1", "c4", 0⟩) none
     , .ok (.needsApproval ⟨"s1", "c3", 0⟩) none, .ok .allowed none
     , .ok .authorized none, .ok .none none, .ok .none none ]
#guard sRej.rejectedMemory == [("t", "d1"), ("u", "d5")]
#guard (sRej.calls["c9"]?).isNone && (sRej.calls["c6"]?).isNone
#guard (step rejPolicy sRej (proposeT 11)).2 == .ok (.denied .previouslyRejected) none
#guard (step rejPolicy sRej (proposeU 11)).2 == .ok (.denied .previouslyRejected) none
#guard (step rejPolicy (after rejPolicy "pd" (rejOpen.take 8)) (ev 9 (proposeT 9).body)).2
  == .ok (.needsApproval ⟨"s1", "c9", 0⟩) none
#guard (sRej.calls["c2"]?).any fun c => c.status == .authorized && c.attempts == 0
#guard (step rejPolicy (after rejPolicy "pd" (rejOpen.take 8)) (ev 9 dispatchC2.body)).2.claimed
#guard (step rejPolicy sRej dispatchC2).2 == .ok (.dispatchDenied .previouslyRejected) none
#guard ((step rejPolicy sRej dispatchC2).1.calls["c2"]?).any
  (·.status == .deniedAtDispatch .previouslyRejected)
#guard (step rejPolicy sRej (ev 11 (.propose "c2" "t" "d1" none [] []))).2
  == .ok (.denied .previouslyRejected) none
#guard (step rejPolicy sRej (ev 11 .reset)).2 == .ok .none none
#guard (step rejPolicy sRej (ev 11 .reset)).1.rejectedMemory == sRej.rejectedMemory
#guard (sRej.calls["c4"]?).any (·.status == .awaiting)
#guard (step rejPolicy sRej (ev 11 (.approve "c4" ⟨"s1", "c4", 0⟩ "a1" "d1" none none))).2
  == .rejected .previouslyRejected
#guard (step rejPolicy sRej
    (ev 11 (.approve "c3" ⟨"s1", "c3", 0⟩ "a1" "d3" none (some { newDigest := "d1" })))).2
  == .rejected .previouslyRejected
#guard (step rejPolicy sRej
    (ev 11 (.approve "c3" ⟨"s1", "c3", 0⟩ "a1" "d3" none (some { newDigest := "d7" })))).2
  == .ok .authorized none

def agentTurn : List Event := rejOpen ++ [ev 11 .turnEnd, ev 12 (.turnStart false)]
def userTurn : List Event := agentTurn ++ [ev 13 .turnEnd, ev 14 (.turnStart true)]

#guard (trace rejPolicy (State.initial "pd") userTurn).all (·.2.2.accepted)
#guard (after rejPolicy "pd" agentTurn).rejectedMemory == sRej.rejectedMemory
#guard (step rejPolicy (after rejPolicy "pd" agentTurn) (proposeT 13)).2
  == .ok (.denied .previouslyRejected) none
#guard (step rejPolicy (after rejPolicy "pd" agentTurn) (proposeU 13)).2
  == .ok (.denied .previouslyRejected) none
#guard (after rejPolicy "pd" userTurn).rejectedMemory.isEmpty
#guard (step rejPolicy (after rejPolicy "pd" userTurn) (proposeU 15)).2 == .ok .allowed none
#guard (step rejPolicy (after rejPolicy "pd" userTurn) (proposeT 15)).2
  == .ok (.needsApproval ⟨"s1", "c9", 0⟩) none

/-- Two edits take `c7` through generations `e0`, `e1`, `e2`; the reject echoes generation 1. -/
def echoEvents : List Event :=
  [ start
  , ev 2 (.turnStart true)
  , ev 3 (.propose "c7" "q" "e0" none [] [])
  , ev 4 (.approve "c7" ⟨"s1", "c7", 0⟩ "a1" "e0" none (some { newDigest := "e1" }))
  , ev 5 (.approve "c7" ⟨"s1", "c7", 1⟩ "a1" "e1" none (some { newDigest := "e2" }))
  , ev 6 (.reject "c7" ⟨"s1", "c7", 1⟩ "a2") ]

#guard (trace rejPolicy (State.initial "pd") echoEvents).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c7", 0⟩) none
     , .ok .pending none, .ok .pending none, .ok .none none ]
#guard ((after rejPolicy "pd" (echoEvents.take 5)).calls["c7"]?).any fun c =>
  c.proposedDigest == "e0" && c.digest == "e2" && c.generation == 2 &&
    (c.generations[1]?.map (·.1)) == some "e1"
#guard (after rejPolicy "pd" echoEvents).rejectedMemory == [("q", "e0"), ("q", "e2"), ("q", "e1")]
#guard (step rejPolicy (after rejPolicy "pd" echoEvents)
    (ev 7 (.propose "c8" "q" "e1" none [] []))).2 == .ok (.denied .previouslyRejected) none

/-- `Proposed` as a check. -/
def proposedIn (p : Policy) (d : String) (es : List Event) (k t dg : String) : Bool :=
  (trace p (State.initial d) es).any fun (s₀, e₀, v₀) =>
    v₀.accepted && s₀.calls[k]?.isNone && (p.action? t).isSome &&
      match e₀.body with
      | .propose k' t' dg' .. => k' == k && t' == t && dg' == dg
      | _ => false

/-- `GenerationDigest` as a check. -/
def generationIn (p : Policy) (d : String) (es : List Event) (k t : String) (g : Nat)
    (dg : String) : Bool :=
  (g == 0 && proposedIn p d es k t dg) ||
    ((trace p (State.initial d) es).any (fun x =>
        match x.2.1.body with
        | .propose _ _ dg₀ .. => proposedIn p d es k t dg₀
        | _ => false) &&
      (trace p (State.initial d) es).any fun x =>
        x.2.2.accepted && match x.2.1.body with
          | .approve k' rid _ _ _ (some y) =>
            k' == k && rid.generation + 1 == g && y.newDigest == dg
          | _ => false)

def echoTurn : List Event := [ev 7 .turnEnd, ev 8 (.turnStart false)]

def echoRepeat : Event := ev 9 (.propose "c8" "q" "e1" none [] [])

#guard ((after rejPolicy "pd" (echoEvents.take 5)).calls["c7"]?).any fun c =>
  c.generations.length == c.generation + 1 && c.generations.map (·.1) == ["e0", "e1", "e2"] &&
    (List.range c.generations.length).all fun g =>
      (c.generations[g]?).any fun x =>
        generationIn rejPolicy "pd" (echoEvents.take 5) "c7" c.tool g x.1
#guard !generationIn rejPolicy "pd" (echoEvents.take 5) "c7" "q" 1 "e2"
#guard (after rejPolicy "pd" echoEvents).rejectedMemory.all fun x =>
  (List.range 3).any fun g => generationIn rejPolicy "pd" echoEvents "c7" x.1 g x.2
#guard (trace rejPolicy (State.initial "pd") (echoEvents ++ echoTurn)).all (·.2.2.accepted)
#guard echoEvents.drop 5 == [ev 6 (.reject "c7" ⟨"s1", "c7", 1⟩ "a2")]
#guard generationIn rejPolicy "pd" (echoEvents.take 5) "c7" "q" 1 "e1"
#guard (trace rejPolicy (after rejPolicy "pd" echoEvents) echoTurn).all fun x =>
  !(x.2.2.accepted && x.2.1.body == .turnStart true)
#guard rejPolicy.modeOf "q" == .enforce
#guard ((after rejPolicy "pd" (echoEvents ++ echoTurn)).calls["c8"]?).isNone
#guard (step rejPolicy (after rejPolicy "pd" (echoEvents ++ echoTurn)) echoRepeat).2
  == .ok (.denied .previouslyRejected) none

end Rejection

end Writ.Proofs
