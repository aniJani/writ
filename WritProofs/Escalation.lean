import WritProofs.Permission

namespace Writ.Proofs

open Writ
open Basic

/-- Section 8, theorem 11: the session is escalated, or tool `t` is blocked under tool scope. -/
def Blocked (s : State) (t : String) : Prop := s.escalated = true ∨ t ∈ s.blockedTools

/-- Section 6, Failures and escalation: approver `a` is attested with a principal other than
`agent` and holds an escalation role (by default, any approver role). -/
def EscalationEligible (p : Policy) (s : State) (a : String) : Prop :=
  ∃ info, s.approvers[a]? = some info ∧ info.principal ≠ "agent" ∧
    ∃ x ∈ info.roles, x ∈ p.escalationRoles.getD p.approverRoles

/-- Section 8, theorem 11: a failure counter at its limit has escalated the session, or under
tool scope blocked the tool. -/
structure EscalationInv (p : Policy) (s : State) : Prop where
  session_total : ∀ n, p.limits.maxFailuresPerSession = some n → n ≤ s.failuresThisSession →
    s.escalated = true
  tool_session : p.limits.escalationScope = .session → ∀ n t,
    p.limits.maxConsecutiveFailures = some n → n ≤ s.failures.getD t 0 → s.escalated = true
  tool_scope : p.limits.escalationScope = .tool → ∀ n t,
    p.limits.maxConsecutiveFailures = some n → n ≤ s.failures.getD t 0 → t ∈ s.blockedTools

namespace Escalation

variable {p : Policy} {s s' : State} {e : Event} {tool : String}

def view (s : State) : Bool × List String × Std.ExtTreeMap String Nat compare × Nat :=
  (s.escalated, s.blockedTools, s.failures, s.failuresThisSession)

local macro "rf_simp" : tactic =>
  `(tactic| (unfold State.recordFailure; cases hsc : p.limits.escalationScope <;>
    simp_all [apply_ite State.escalated, apply_ite State.failures,
      apply_ite State.failuresThisSession, apply_ite State.blockedTools]))

theorem recordFailure_failures :
    (s.recordFailure p tool).failures = s.failures.insert tool (s.failures.getD tool 0 + 1) := by
  rf_simp

theorem recordFailure_total :
    (s.recordFailure p tool).failuresThisSession = s.failuresThisSession + 1 := by
  rf_simp

theorem recordFailure_escalated (h : s.escalated = true) :
    (s.recordFailure p tool).escalated = true := by
  rf_simp

theorem recordFailure_blockedTools (h : t ∈ s.blockedTools) :
    t ∈ (s.recordFailure p tool).blockedTools := by
  rf_simp
  split <;> simp_all

theorem recordFailure_total_hit (hn : p.limits.maxFailuresPerSession = some n)
    (hle : n ≤ s.failuresThisSession + 1) : (s.recordFailure p tool).escalated = true := by
  rf_simp

theorem recordFailure_session_hit (hs : p.limits.escalationScope = .session)
    (hn : p.limits.maxConsecutiveFailures = some n) (hle : n ≤ s.failures.getD tool 0 + 1) :
    (s.recordFailure p tool).escalated = true := by
  rf_simp

theorem recordFailure_tool_hit (hs : p.limits.escalationScope = .tool)
    (hn : p.limits.maxConsecutiveFailures = some n) (hle : n ≤ s.failures.getD tool 0 + 1) :
    tool ∈ (s.recordFailure p tool).blockedTools := by
  rf_simp
  split <;> simp_all

theorem inv_congr (h : view s' = view s) (hi : EscalationInv p s) : EscalationInv p s' := by
  simp only [view, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨i1, i2, i3⟩ := hi
  constructor <;> simp only [h1, h2, h3, h4] <;> assumption

theorem inv_recordFailure (h : EscalationInv p s) : EscalationInv p (s.recordFailure p tool) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun n hn hle => ?_, fun hs n t hn hle => ?_, fun hs n t hn hle => ?_⟩
  · rw [recordFailure_total] at hle
    exact recordFailure_total_hit hn hle
  · rw [recordFailure_failures, Std.ExtTreeMap.getD_insert] at hle
    split at hle
    · rename_i ht
      rw [Std.LawfulEqCmp.compare_eq_iff_eq] at ht
      subst ht
      exact recordFailure_session_hit hs hn hle
    · exact recordFailure_escalated (h2 hs n t hn hle)
  · rw [recordFailure_failures, Std.ExtTreeMap.getD_insert] at hle
    split at hle
    · rename_i ht
      rw [Std.LawfulEqCmp.compare_eq_iff_eq] at ht
      subst ht
      exact recordFailure_tool_hit hs hn hle
    · exact recordFailure_blockedTools (h3 hs n t hn hle)

theorem inv_recordSuccess (hwf : p.WF) (h : EscalationInv p s) :
    EscalationInv p (s.recordSuccess tool) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun hs n t hn hle => ?_, fun hs n t hn hle => ?_⟩ <;>
  · simp only [State.recordSuccess, Std.ExtTreeMap.getD_insert] at hle
    split at hle
    · have hz : n = 0 := by omega
      subst hz
      exact absurd hn (WF.failureLimit_pos hwf)
    · first | exact h2 hs n t hn hle | exact h3 hs n t hn hle

theorem releaseGrant_view : view (s.releaseGrant k) = view s := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem consumeGrant_view : view (s.consumeGrant k) = view s := by
  unfold State.consumeGrant; repeat' split
  all_goals rfl

theorem updateEntries_view : view (s.updateEntries p m t f) = view s := by
  unfold State.updateEntries; split <;> rfl

theorem foldl_view {α : Type _} {f : State → α → State} (hf : ∀ s a, view (f s a) = view s)
    (l : List α) (s : State) : view (l.foldl f s) = view s :=
  foldl_invariant (fun b => view b = view s) (fun b a hb => (hf b a).trans hb) l s rfl

theorem settle_view : view (s.settle p ms k o a ne t).1 = view s := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => view b.1 = view s) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact updateEntries_view.trans h
  · split <;> exact updateEntries_view.trans h

theorem endCall_view : view (s.endCall k st) = view s := releaseGrant_view

theorem cancelPending_view : view (cancelPending s) = view s := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b => view b = view s) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact endCall_view.trans ha
  · exact endCall_view.trans ha
  · exact ha

theorem interrupt_view : view s.interrupt = view s := cancelPending_view

theorem claim_view {r : Requirements} {key : String} {retry : Bool} :
    view (claim p s t k rc r retry key) = view s := by
  unfold claim
  dsimp only
  split
  · exact foldl_view (fun _ _ => updateEntries_view) _ _
  · exact (foldl_view (fun _ _ => updateEntries_view) _ _).trans consumeGrant_view

/-- How a handler other than `escalation_ack` moves the escalation state: it keeps it, or records
one failure or one success. -/
inductive Evolves (p : Policy) (s : State) : State → Prop
  | keep {s' : State} : view s' = view s → Evolves p s s'
  | fail {s₁ : State} (tool : String) : view s₁ = view s → Evolves p s (s₁.recordFailure p tool)
  | succ {s₁ : State} (tool : String) : view s₁ = view s → Evolves p s (s₁.recordSuccess tool)

theorem blocked_congr (h : view s' = view s) (hb : Blocked s t) : Blocked s' t := by
  simp only [view, Prod.mk.injEq] at h
  unfold Blocked
  rw [h.1, h.2.1]
  exact hb

theorem Evolves.blocked (h : Evolves p s s') (hb : Blocked s t) : Blocked s' t := by
  cases h with
  | keep h => exact blocked_congr h hb
  | fail _ h =>
    rcases blocked_congr h hb with hb | hb
    · exact .inl (recordFailure_escalated hb)
    · exact .inr (recordFailure_blockedTools hb)
  | @succ s₁ _ h => exact blocked_congr (s' := s₁) h hb

theorem Evolves.inv (hwf : p.WF) (h : Evolves p s s') (hi : EscalationInv p s) :
    EscalationInv p s' := by
  cases h with
  | keep h => exact inv_congr h hi
  | fail _ h => exact inv_recordFailure (inv_congr h hi)
  | succ _ h => exact inv_recordSuccess hwf (inv_congr h hi)

local macro "evolves" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact .keep rfl
      | exact .keep cancelPending_view
      | exact .keep interrupt_view
      | exact .keep endCall_view
      | exact .keep claim_view
      | exact .keep settle_view
      | exact .fail _ settle_view
      | exact .succ _ settle_view
      | exact .fail _ rfl)

theorem applyApprove_view (h : applyApprove p s t k rc w pr dg c ed = .ok r) :
    view r.1 = view s := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

theorem handleApprove_evolves : Evolves p s (handleApprove p s t i r w dg c ed).1 := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact .keep rfl
    | exact .keep (applyApprove_view (by assumption))

theorem handleReject_evolves : Evolves p s (handleReject p s i r w).1 := by
  unfold handleReject
  split
  · exact .keep rfl
  · exact .keep (endCall_view (s := s) (k := i) (st := .rejected))

theorem stepHandle_evolves (hne : ∀ a n, e.body ≠ .escalationAck a n) :
    Evolves p s (stepHandle p s e).1 := by
  unfold stepHandle
  split <;> rename_i hb
  · unfold handleSessionStart; evolves
  · unfold handleSessionEnd; evolves
  · unfold handleTurnStart; evolves
  · unfold handleTurnEnd; evolves
  · unfold handleStepStart; evolves
  · unfold handleApproverAttest; evolves
  · unfold handlePermissionRevoke; evolves
  · unfold handlePropose; evolves
  · exact handleApprove_evolves
  · exact handleReject_evolves
  · unfold handleApprovalExpire; evolves
  · unfold handleGrantCreate; evolves
  · unfold handleGrantRevoke; evolves
  · rcases Dispatch.handle_cases with he | ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] <;>
      evolves
  · unfold handleResult; evolves
  · unfold handleOutcomeUnknown; evolves
  · unfold handleReconcile; evolves
  · unfold handleCancel; evolves
  · unfold handleReset; evolves
  · unfold handleKill; evolves
  · unfold handlePermissionAdd; evolves
  · exact absurd hb (hne _ _)
  · unfold handleLedgerSync; evolves

theorem inv_zero (hwf : p.WF) (h1 : s.failuresThisSession = 0)
    (h2 : ∀ t, s.failures.getD t 0 = 0) : EscalationInv p s := by
  refine ⟨fun n hn hle => ?_, fun _ n t hn hle => ?_, fun _ n t hn hle => ?_⟩
  · rw [h1, Nat.le_zero] at hle
    subst hle
    exact absurd hn (WF.sessionFailureLimit_pos hwf)
  all_goals
    rw [h2, Nat.le_zero] at hle
    subst hle
    exact absurd hn (WF.failureLimit_pos hwf)

theorem eligible_of {a : String} (h : s.escalationEligible p a = none) :
    EscalationEligible p s a := by
  unfold State.escalationEligible at h
  rw [Std.ExtTreeMap.get?_eq_getElem?] at h
  cases hi : s.approvers[a]? with
  | none => rw [hi] at h; cases h
  | some info =>
    rw [hi] at h
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, decide_eq_true_eq] at hc
      exact ⟨info, hi, hc.1, hc.2⟩
    · cases h

theorem ack_accepted {a : String} (h : (handleEscalationAck p s a n).2.accepted = true) :
    n = s.escalations ∧ EscalationEligible p s a := by
  unfold handleEscalationAck at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hel
  split at h
  · cases h
  rename_i hn
  exact ⟨Decidable.of_not_not hn, eligible_of hel⟩

theorem ack_inv {a : String} (hwf : p.WF) (hi : EscalationInv p s) :
    EscalationInv p (handleEscalationAck p s a n).1 := by
  unfold handleEscalationAck
  repeat' split
  all_goals first
    | exact hi
    | exact inv_zero hwf rfl fun _ => Std.ExtTreeMap.getD_empty

theorem blocked_bool (hb : Blocked s tool) : s.blocked tool = true := by
  unfold State.blocked
  rcases hb with h | h <;> simp [h]

theorem enforce_blocked {tool dg : String} {gs es : List (String × Bool)}
    (hb : s.blocked tool = true) :
    ∃ x, (enforceDecision p s t k tool dg cost gs es).1 = .denied x := by
  unfold enforceDecision
  dsimp only
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  exact ⟨_, rfl⟩

theorem repeat_blocked (hb : s.blocked rc.tool = true) (hm : p.modeOf rc.tool = .enforce) :
    ∃ x, (repeatDecision p s t k rc).1 = .denied x := by
  unfold repeatDecision
  simp only [hb, hm, ↓reduceIte]
  split <;> exact ⟨_, rfl⟩

theorem handlePropose_new {tool dg : String} {gs es : List (String × Bool)}
    (hk : s.calls[k]? = none) (hd : ∃ x, (enforceDecision p s t k tool dg cost gs es).1 = .denied x)
    (hm : p.modeOf tool = .enforce)
    (hv : (handlePropose p s t k tool dg cost gs es).2 = .ok dc sh) : ∃ x, dc = .denied x := by
  unfold handlePropose at hv
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk] at hv
  dsimp only at hv
  obtain ⟨x, hx⟩ := hd
  revert hv
  generalize enforceDecision p s t k tool dg cost gs es = r at hx
  obtain ⟨dd, cs⟩ := r
  dsimp only at hx ⊢
  subst hx
  split
  · intro hv; injection hv with hdc; exact ⟨x, hdc.symm⟩
  · simp only [hm, Disposition.shadowed]
    intro hv; injection hv with hdc; exact ⟨x, hdc.symm⟩

theorem handlePropose_denied {tool dg : String} {gs es : List (String × Bool)}
    (hb : s.blocked tool = true) (hm : p.modeOf tool = .enforce)
    (hv : (handlePropose p s t k tool dg cost gs es).2 = .ok dc sh) : ∃ x, dc = .denied x := by
  cases hk : s.calls[k]? with
  | none => exact handlePropose_new hk (enforce_blocked hb) hm hv
  | some rc =>
    unfold handlePropose at hv
    rw [Std.ExtTreeMap.get?_eq_getElem?, hk] at hv
    dsimp only at hv
    split at hv
    · rename_i hmatch
      obtain ⟨ht, -⟩ := hmatch
      subst ht
      have hd : (repeatDecision p s t k rc).1 = dc := by injection hv
      obtain ⟨x, hx⟩ := repeat_blocked (t := t) (k := k) hb hm
      exact ⟨x, by rw [← hd, hx]⟩
    · cases hv

theorem view_failures (h : view s' = view s) :
    s'.failuresThisSession = s.failuresThisSession ∧ s'.failures = s.failures := by
  simp only [view, Prod.mk.injEq] at h
  exact ⟨h.2.2.2, h.2.2.1⟩

theorem recordFailure_counted (h : view s' = view s) :
    (s'.recordFailure p tool).failuresThisSession = s.failuresThisSession + 1 ∧
      (s'.recordFailure p tool).failures[tool]? = some (s.failures.getD tool 0 + 1) := by
  obtain ⟨h1, h2⟩ := view_failures h
  rw [recordFailure_total, recordFailure_failures, Std.ExtTreeMap.getElem?_insert_self, h1, h2]
  exact ⟨rfl, rfl⟩

theorem handleResult_failed {act : Option Nat} {ne : Bool}
    (ha : (handleResult p s t k .failed act ne).2.accepted = true) :
    ∃ c, s.calls[k]? = some c ∧
      (handleResult p s t k .failed act ne).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (handleResult p s t k .failed act ne).1.failures[c.tool]? =
        some (s.failures.getD c.tool 0 + 1) := by
  revert ha
  unfold handleResult
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hc : s.calls[k]? with
  | none => intro h; cases h
  | some c =>
    intro ha
    refine ⟨c, rfl, ?_⟩
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hd
      simp only [hd, ↓reduceIte]
      exact recordFailure_counted settle_view

theorem handleOutcomeUnknown_failed (ha : (handleOutcomeUnknown p s k).2.accepted = true) :
    ∃ c, s.calls[k]? = some c ∧
      (handleOutcomeUnknown p s k).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (handleOutcomeUnknown p s k).1.failures[c.tool]? = some (s.failures.getD c.tool 0 + 1) := by
  revert ha
  unfold handleOutcomeUnknown
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hc : s.calls[k]? with
  | none => intro h; cases h
  | some c =>
    intro ha
    refine ⟨c, rfl, ?_⟩
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hd
      simp only [hd, ↓reduceIte]
      exact recordFailure_counted rfl

end Escalation

open Escalation

variable {p : Policy} {d : String} {s : State} {e : Event} {t : String}

/-- Section 8, theorem 11: in every reachable state, a session failure total at its limit, or a
tool's consecutive failures at their limit under session scope, has escalated the session; under
tool scope a tool at its limit is blocked. A limit of 0 is a check error. -/
theorem escalationInv_reachable (hwf : p.WF) (h : Reachable p d s) : EscalationInv p s := by
  induction h with
  | init => exact inv_zero hwf rfl fun _ => Std.ExtTreeMap.getD_empty
  | @step s e _ ih =>
    cases ha : (step p s e).2.accepted
    · rw [frame ha]; exact ih
    · rw [accepted_step ha]
      refine inv_congr (s := (stepHandle p s e).1) rfl ?_
      by_cases hack : ∃ a n, e.body = .escalationAck a n
      · obtain ⟨a, n, hb⟩ := hack
        simp only [stepHandle, hb]
        exact ack_inv hwf ih
      · exact (stepHandle_evolves fun a n hb => hack ⟨a, n, hb⟩).inv hwf ih

/-- Section 8, theorem 11 at propose: while the session is escalated or the tool blocked, every
proposal of an enforced action, new or repeated, is answered with a denial, never `existing`. -/
theorem blocked_propose {k dg : String} {cost : Option Cost} {gs esc : List (String × Bool)}
    {dc : Decision} {sh : Option Shadow} (hb : Blocked s t)
    (he : e.body = .propose k t dg cost gs esc) (hm : p.modeOf t = .enforce)
    (hv : (step p s e).2 = .ok dc sh) : (∃ x, dc = .denied x) ∧ dc.nonDenied = false := by
  have ha : (step p s e).2.accepted = true := by rw [hv]; rfl
  rw [accepted_step ha] at hv
  simp only [stepHandle, he] at hv
  obtain ⟨x, rfl⟩ := handlePropose_denied (blocked_bool hb) hm hv
  exact ⟨⟨x, rfl⟩, rfl⟩

/-- Section 8, theorem 11 at dispatch: while the session is escalated or the call's tool blocked,
no dispatch of an enforced action is claimed. -/
theorem blocked_claim {k dg key : String} {n : Nat} {cost : Option Cost}
    {g : List (String × Bool)} {c : CallRec} (hb : Blocked s c.tool)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) : (step p s e).2.claimed = false := by
  cases h : (step p s e).2.claimed
  · rfl
  exfalso
  obtain ⟨-, c', hc', -, hok⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  obtain ⟨h1, h2, -⟩ := (hok hm).2
  rcases hb with hb | hb
  · rw [h1] at hb; cases hb
  · exact h2 hb

/-- Section 8, theorem 11: a block is lifted only by an accepted `escalation_ack` from an eligible
approver that echoes the escalation count current at the acknowledgment. -/
theorem unblock (hb : Blocked s t) (hb' : ¬ Blocked (step p s e).1 t) :
    (step p s e).2.accepted = true ∧
      ∃ a, e.body = .escalationAck a s.escalations ∧ EscalationEligible p s a := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha] at hb'; exact absurd hb hb'
  refine ⟨rfl, ?_⟩
  have ha' : (stepHandle p s e).2.accepted = true := by
    have h' := ha; rw [accepted_step ha] at h'; exact h'
  rw [accepted_step ha] at hb'
  by_cases hack : ∃ a n, e.body = .escalationAck a n
  · obtain ⟨a, n, hbody⟩ := hack
    simp only [stepHandle, hbody] at ha'
    obtain ⟨rfl, hel⟩ := ack_accepted ha'
    exact ⟨a, hbody, hel⟩
  · exact absurd ((stepHandle_evolves fun a n hb => hack ⟨a, n, hb⟩).blocked hb) hb'

/-- Section 8, theorem 11, what counts as a failure: an accepted `result` with outcome `failed`
(with or without an overrun, which then counts once) and an accepted `outcome_unknown` each count
one failure of the session and one of the reported call's tool. -/
theorem failed_fails {k : String}
    (ha : (step p s e).2.accepted = true)
    (hb : (∃ act ne, e.body = .result k .failed act ne) ∨ e.body = .outcomeUnknown k) :
    ∃ c : CallRec, s.calls[k]? = some c ∧
      (step p s e).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (step p s e).1.failures[c.tool]? = some (s.failures.getD c.tool 0 + 1) := by
  have ha' : (stepHandle p s e).2.accepted = true := by
    have h' := ha; rw [accepted_step ha] at h'; exact h'
  rw [accepted_step ha]
  rcases hb with ⟨act, ne, hb⟩ | hb <;> simp only [stepHandle, hb] at ha' ⊢
  · exact handleResult_failed ha'
  · exact handleOutcomeUnknown_failed ha'

namespace Escalation

def escPolicy (scope : EscalationScope) (total : Option Nat) : Policy :=
  { approverRoles := ["owner", "ops"], escalationRoles := some ["ops"]
    actions := [("t", {}), ("u", {})]
    limits := { maxConsecutiveFailures := some 2, maxFailuresPerSession := total
                escalationScope := scope } }

def sessionPolicy : Policy := escPolicy .session none
def toolPolicy : Policy := escPolicy .tool (some 3)

def ev (n : Nat) (b : EventBody) : Event := ⟨n, n, n - 1, none, b⟩

/-- Two failed results of `t`, with calls `c3` of `u` and `c5` of `t` authorized in between. -/
def failTwice : List Event :=
  [ ev 1 (.sessionStart "s1" "pd" "u1" []
      [("a1", ⟨"alice", .human, ["ops"]⟩), ("a2", ⟨"bob", .human, ["owner"]⟩)] {})
  , ev 2 (.turnStart true)
  , ev 3 (.propose "c1" "t" "d1" none [] [])
  , ev 4 (.dispatch "c1" 1 "d1" none [] "k1")
  , ev 5 (.result "c1" .failed none false)
  , ev 6 (.propose "c2" "t" "d2" none [] [])
  , ev 7 (.propose "c3" "u" "d3" none [] [])
  , ev 8 (.propose "c5" "t" "d5" none [] [])
  , ev 9 (.dispatch "c2" 1 "d2" none [] "k2")
  , ev 10 (.result "c2" .failed none false) ]

def newT : Event := ev 11 (.propose "c4" "t" "d4" none [] [])
def newU : Event := ev 11 (.propose "c4" "u" "d4" none [] [])
def repeatT : Event := ev 11 (.propose "c5" "t" "d5" none [] [])
def repeatU : Event := ev 11 (.propose "c3" "u" "d3" none [] [])
def dispatchT : Event := ev 11 (.dispatch "c5" 1 "d5" none [] "k5")
def dispatchU : Event := ev 11 (.dispatch "c3" 1 "d3" none [] "k3")
def ackBy (a : String) (n : Nat) : Event := ev 11 (.escalationAck a n)

def sAfter : State := after sessionPolicy "pd" failTwice
def tAfter : State := after toolPolicy "pd" failTwice

#guard decide sessionPolicy.WF && decide toolPolicy.WF
#guard ["t", "u"].all fun x => sessionPolicy.modeOf x == .enforce && toolPolicy.modeOf x == .enforce
#guard (trace sessionPolicy (State.initial "pd") failTwice).all (·.2.2.accepted)
#guard sAfter.failures.getD "t" 0 == 2 && sAfter.escalated && sAfter.escalations == 1
#guard (step sessionPolicy sAfter newU).2 == .ok (.denied .escalated) none
#guard (step sessionPolicy sAfter repeatU).2 == .ok (.denied .escalated) none
#guard (sAfter.calls["c3"]?).any (·.status == .authorized)
#guard (step sessionPolicy sAfter dispatchU).2 == .rejected .escalated
#guard (step sessionPolicy sAfter (ackBy "a1" 0)).2 == .rejected .staleRequest
#guard (step sessionPolicy sAfter (ackBy "a2" 1)).2 == .rejected .approverNotEligible
#guard (step sessionPolicy sAfter (ackBy "a1" 1)).2 == .ok .none none

def sAcked : State := after sessionPolicy "pd" (failTwice ++ [ackBy "a1" 1])

#guard !sAcked.escalated && sAcked.blockedTools.isEmpty
#guard (step sessionPolicy sAcked (ev 12 (.propose "c4" "u" "d4" none [] []))).2
  == .ok .allowed none
#guard (step sessionPolicy sAcked (ev 12 (.dispatch "c3" 1 "d3" none [] "k3"))).2.claimed

#guard (trace toolPolicy (State.initial "pd") failTwice).all (·.2.2.accepted)
#guard tAfter.failures.getD "t" 0 == 2 && !tAfter.escalated && tAfter.blockedTools == ["t"]
#guard tAfter.escalations == 1
#guard (step toolPolicy tAfter newT).2 == .ok (.denied .escalated) none
#guard (step toolPolicy tAfter repeatT).2 == .ok (.denied .escalated) none
#guard (step toolPolicy tAfter dispatchT).2 == .rejected .escalated
#guard (step toolPolicy tAfter newU).2 == .ok .allowed none
#guard (step toolPolicy tAfter repeatU).2 == .ok .allowed none
#guard (step toolPolicy tAfter dispatchU).2.claimed

def tToolAcked : State := after toolPolicy "pd" (failTwice ++ [ackBy "a1" 1])

#guard (step toolPolicy tAfter (ackBy "a1" 0)).2 == .rejected .staleRequest
#guard (step toolPolicy tAfter (ackBy "a1" 1)).2 == .ok .none none
#guard !tToolAcked.escalated && tToolAcked.blockedTools.isEmpty
#guard (step toolPolicy tToolAcked (ev 12 (.propose "c4" "t" "d4" none [] []))).2
  == .ok .allowed none

/-- `c5` of `t` is dispatched before the second failure blocks `t`, and succeeds after it. -/
def inFlight : List Event :=
  failTwice.take 9 ++
    [ ev 10 (.dispatch "c5" 1 "d5" none [] "k5"), ev 11 (.result "c2" .failed none false)
    , ev 12 (.result "c5" .succeeded none false) ]

def tInFlight : State := after toolPolicy "pd" inFlight

#guard (trace toolPolicy (State.initial "pd") inFlight).all (·.2.2.accepted)
#guard (after toolPolicy "pd" (inFlight.take 11)).blockedTools == ["t"]
#guard (tInFlight.calls["c5"]?).any (·.status == .succeeded)
#guard tInFlight.failures.getD "t" 0 == 0 && tInFlight.blockedTools == ["t"]
#guard (step toolPolicy tInFlight (ev 13 (.propose "c4" "t" "d4" none [] []))).2
  == .ok (.denied .escalated) none

/-- A third failure, on `u`, reaches the session total of 3 under tool scope. -/
def failThrice : List Event :=
  failTwice ++ [dispatchU, ev 12 (.result "c3" .failed none false)]

def tTotal : State := after toolPolicy "pd" failThrice

#guard (trace toolPolicy (State.initial "pd") failThrice).all (·.2.2.accepted)
#guard tTotal.failuresThisSession == 3 && tTotal.failures.getD "u" 0 == 1 && tTotal.escalated
#guard tTotal.escalations == 2
#guard (step toolPolicy tTotal (ev 13 (.propose "c6" "u" "d6" none [] []))).2
  == .ok (.denied .escalated) none
#guard (step toolPolicy tTotal (ev 13 (.escalationAck "a1" 1))).2 == .rejected .staleRequest

def tAcked : State := after toolPolicy "pd" (failThrice ++ [ev 13 (.escalationAck "a1" 2)])

#guard (step toolPolicy tTotal (ev 13 (.escalationAck "a1" 2))).2 == .ok .none none
#guard !tAcked.escalated && tAcked.blockedTools.isEmpty && tAcked.failuresThisSession == 0
#guard (step toolPolicy tAcked (ev 14 (.propose "c6" "t" "d6" none [] []))).2 == .ok .allowed none

def counted (s s' : State) (tool : String) : Bool :=
  s'.failuresThisSession == s.failuresThisSession + 1 &&
    s'.failures[tool]? == some (s.failures.getD tool 0 + 1)

#guard (List.range 10).all fun n => (failTwice[n]?).any fun e =>
  let s := after sessionPolicy "pd" (failTwice.take n)
  let x := step sessionPolicy s e
  x.2.accepted && (n != 4 && n != 9 || counted s x.1 "t")
#guard (after sessionPolicy "pd" (failTwice.take 4)).failures.getD "t" 0 == 0

def unknownT : List Event := failTwice.take 4 ++ [ev 5 (.outcomeUnknown "c1")]

#guard (step sessionPolicy (after sessionPolicy "pd" (failTwice.take 4))
  (ev 5 (.outcomeUnknown "c1"))).2 == .ok .none none
#guard counted (after sessionPolicy "pd" (failTwice.take 4)) (after sessionPolicy "pd" unknownT) "t"
#guard ((after sessionPolicy "pd" unknownT).calls["c1"]?).any (·.status == .unknown)

def overPolicy : Policy :=
  { meters := [("usd", { unit := .money "USD" })], actions := [("t", { meters := ["usd"] })] }

def overOpen : List Event := failTwice.take 2 ++
  [ ev 3 (.propose "c1" "t" "d1" (some ⟨5, "USD"⟩) [] [])
  , ev 4 (.dispatch "c1" 1 "d1" (some ⟨5, "USD"⟩) [] "k1") ]

def overFailed : Event := ev 5 (.result "c1" .failed (some 9) false)

#guard (step overPolicy (after overPolicy "pd" overOpen) overFailed).2
  == .ok (.overrun ["usd"]) none
#guard counted (after overPolicy "pd" overOpen)
  (step overPolicy (after overPolicy "pd" overOpen) overFailed).1 "t"

end Escalation

end Writ.Proofs
