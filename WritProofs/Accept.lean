import WritProofs.Dispatch
import WritProofs.ConsentMeaning
import WritProofs.Escalation

namespace Writ.Proofs

open Writ
open Basic

variable {p : Policy} {s : State} {e : Event}

/-- The clauses an approver's eligibility is checked against. For a consent with no clauses,
section 6 (Approve) falls back to the clause `{ k := 1, humanOnly := false }`, which an attested
approver meets exactly when it holds an approver role and its principal is not `agent`.
`permission_add`, a `grant_create` whose consents have no clauses and a `reject` of an Authorized
call that needed no consent see the fallback; an Awaiting call always has clauses, so `approve`
never does. -/
def ClausesOrOne (c : Consent) : List Clause :=
  if c.clauses = [] then [{ k := 1, humanOnly := false }] else c.clauses

/-- Approver `a` is attested and eligible for at least one clause of `c`. -/
def EligibleSome (p : Policy) (s : State) (c : Consent) (a : String) : Prop :=
  ∃ info, s.approvers[a]? = some info ∧
    ∃ cl ∈ ClausesOrOne c, EligibleFor p s cl (info.principal, a)

/-- Approver `a` is attested and eligible for every clause of `c`. -/
def EligibleEvery (p : Policy) (s : State) (c : Consent) (a : String) : Prop :=
  ∃ info, s.approvers[a]? = some info ∧
    ∀ cl ∈ ClausesOrOne c, EligibleFor p s cl (info.principal, a)

/-- Section 6, Propose step 8 and Approve (an edit's `new_cost`): meter `m` is defined and, when
it is a money meter, `cost` is present, in the meter's currency and within its `max_per_call`. -/
def CostShapeOk (p : Policy) (m : String) (cost : Option Cost) : Prop :=
  ∃ spec, p.meter? m = some spec ∧ ∀ cur, spec.unit = .money cur → ∃ cc, cost = some cc ∧
    cc.currency = cur ∧ ∀ mx, spec.maxPerCall = some mx → cc.amount ≤ mx

namespace Accept

theorem eligibleFor_iff {cl : Clause} {a : String} :
    s.eligibleFor p cl a = true ↔
      ∃ info, s.approvers[a]? = some info ∧ EligibleFor p s cl (info.principal, a) := by
  constructor
  · intro h
    cases hi : s.approvers[a]? with
    | none =>
      unfold State.eligibleFor at h
      rw [Std.ExtTreeMap.get?_eq_getElem?, hi] at h
      cases h
    | some info => exact ⟨info, rfl, eligibleFor_sound h hi⟩
  · rintro ⟨info, hi, info', hi', -, hag, hrole, hcl, hh, hreq⟩
    rw [hi] at hi'
    cases hi'
    unfold State.eligibleFor
    rw [Std.ExtTreeMap.get?_eq_getElem?, hi]
    cases hr : cl.roles <;> cases hhu : cl.humanOnly <;> cases hx : cl.excludeRequester <;>
      simp_all

theorem clausesOrOne_eq {c : Consent} :
    (if c.clauses.isEmpty then [{ k := 1, humanOnly := false }] else c.clauses) =
      ClausesOrOne c := by
  unfold ClausesOrOne
  cases c.clauses <;> rfl

theorem contains_of {a : String} {info : ApproverInfo} (hi : s.approvers[a]? = some info) :
    s.approvers.contains a = true := by
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hi]
  rfl

theorem eligibleAny_iff {c : Consent} {a : String} :
    s.eligibleAny p c a = none ↔ EligibleSome p s c a := by
  show (if (!s.approvers.contains a) = true then some Reason.unknownApprover
      else if ((if c.clauses.isEmpty then [{ k := 1, humanOnly := false }] else c.clauses).any
        (s.eligibleFor p · a)) = true then none else some Reason.approverNotEligible) = none ↔ _
  rw [clausesOrOne_eq]
  constructor
  · intro h
    split at h
    · cases h
    split at h
    · rename_i hany
      obtain ⟨cl, hcl, he⟩ := List.any_eq_true.mp hany
      obtain ⟨info, hi, hel⟩ := eligibleFor_iff.mp he
      exact ⟨info, hi, cl, hcl, hel⟩
    · cases h
  · rintro ⟨info, hi, cl, hcl, hel⟩
    have hany : (ClausesOrOne c).any (s.eligibleFor p · a) = true :=
      List.any_eq_true.mpr ⟨cl, hcl, eligibleFor_iff.mpr ⟨info, hi, hel⟩⟩
    simp [contains_of hi, hany]

theorem eligibleAll_iff {c : Consent} {a : String} :
    s.eligibleAll p c a = none ↔ EligibleEvery p s c a := by
  show (if (!s.approvers.contains a) = true then some Reason.unknownApprover
      else if ((if c.clauses.isEmpty then [{ k := 1, humanOnly := false }] else c.clauses).all
        (s.eligibleFor p · a)) = true then none else some Reason.approverNotEligible) = none ↔ _
  rw [clausesOrOne_eq]
  constructor
  · intro h
    split at h
    · cases h
    rename_i hcon
    split at h
    · rename_i hall
      have hm : a ∈ s.approvers := Std.ExtTreeMap.contains_iff_mem.mp (by simpa using hcon)
      obtain ⟨info, hi⟩ := Option.isSome_iff_exists.mp
        (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hm)
      refine ⟨info, hi, fun cl hcl => ?_⟩
      obtain ⟨info', hi', hel⟩ := eligibleFor_iff.mp (List.all_eq_true.mp hall cl hcl)
      rw [hi] at hi'
      cases hi'
      exact hel
    · cases h
  · rintro ⟨info, hi, hel⟩
    have hall : (ClausesOrOne c).all (s.eligibleFor p · a) = true :=
      List.all_eq_true.mpr fun cl hcl => eligibleFor_iff.mpr ⟨info, hi, hel cl hcl⟩
    simp [contains_of hi, hall]

theorem step_iff : (step p s e).2.accepted = true ↔
    EnvelopeOk s e ∧ (stepHandle p s e).2.accepted = true := by
  rw [Dispatch.step_accepted_iff, envelope_iff]

theorem callCheck_ok {k : String} {rid : RequestId} {c : CallRec} :
    callCheck s k rid = .ok c ↔ s.calls[k]? = some c ∧ c.status = .awaiting ∧
      rid = ⟨s.sessionId, k, c.generation⟩ ∧ c.epoch = s.epoch := by
  unfold callCheck
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases s.calls[k]? with
  | none => simp
  | some c' =>
    simp only [Option.some.injEq]
    split
    · constructor
      · intro h; cases h
      · rintro ⟨rfl, h, -⟩; contradiction
    · split
      · constructor
        · intro h; cases h
        · rintro ⟨rfl, -, h1, h2⟩; simp_all
      · constructor
        · intro h; cases h; simp_all
        · rintro ⟨rfl, -⟩; rfl

theorem vetoCheck_ok {k a : String} {rid : RequestId} {c : CallRec} :
    vetoCheck p s k rid a = .ok c ↔ s.calls[k]? = some c ∧
      (c.status = .awaiting ∨ (c.status = .authorized ∧ c.attempts = 0)) ∧
      rid.session = s.sessionId ∧ rid.call = k ∧ rid.generation ≤ c.generation ∧
      c.epoch = s.epoch ∧ EligibleSome p s c.consent a := by
  unfold vetoCheck
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases s.calls[k]? with
  | none => simp
  | some c' =>
    simp only [Option.some.injEq]
    split
    · rename_i hst
      constructor
      · intro h; cases h
      · rintro ⟨rfl, h, -⟩; simp [h] at hst
    · rename_i hst
      have hst' : c'.status = .awaiting ∨ (c'.status = .authorized ∧ c'.attempts = 0) := by
        have h' : ¬c'.status = .awaiting → c'.status = .authorized ∧ c'.attempts = 0 := by
          simpa using hst
        exact Decidable.or_iff_not_imp_left.mpr h'
      split
      · rename_i hr
        constructor
        · intro h; cases h
        · rintro ⟨rfl, -, h1, h2, h3, h4, -⟩
          exact absurd hr (by simp [h1, h2, h4, Nat.not_lt.mpr h3])
      · rename_i hr
        have hr' : rid.session = s.sessionId ∧ rid.call = k ∧ rid.generation ≤ c'.generation ∧
            c'.epoch = s.epoch := by
          simpa [Nat.not_lt] using hr
        rw [← eligibleAny_iff]
        split
        · constructor
          · intro h; cases h
          · rintro ⟨rfl, -, -, -, -, -, h⟩; simp_all
        · rename_i he
          constructor
          · intro h; cases h; exact ⟨rfl, hst', hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2, he⟩
          · rintro ⟨rfl, -⟩; rfl

theorem awaitingCheck_ok {k a : String} {rid : RequestId} {c : CallRec} :
    awaitingCheck p s k rid a = .ok c ↔
      callCheck s k rid = .ok c ∧ EligibleSome p s c.consent a := by
  unfold awaitingCheck
  cases h : callCheck s k rid with
  | error r => simp [bind, Except.bind]
  | ok c' =>
    simp only [bind, Except.bind]
    rw [← eligibleAny_iff]
    split <;> simp_all [pure, Except.pure] <;> (rintro rfl; simp_all)

theorem ite_error {α : Type} {q : Prop} [Decidable q] {r : Reason} {x : Except Reason α} :
    (∃ v, (if q then Except.error r else x) = .ok v) ↔ ¬q ∧ ∃ v, x = .ok v := by
  split <;> simp_all

theorem ok_ite {α : Type} {q : Prop} [Decidable q] {a b : α} :
    (∃ v, (if q then (Except.ok a : Except Reason α) else .ok b) = .ok v) ↔ True :=
  ⟨fun _ => trivial, fun _ => by split <;> exact ⟨_, rfl⟩⟩

theorem shape_none {m : String} {cost : Option Cost} :
    meterShapeDenial p m cost = none ↔ CostShapeOk p m cost := by
  unfold meterShapeDenial CostShapeOk
  cases p.meter? m with
  | none => simp
  | some spec => simpa using Dispatch.shape_iff

theorem editCost_none {t : String} {cost : Option Cost} :
    editCostDenial p t cost = none ↔
      ∀ m ∈ ((p.action? t).getD {}).meters, CostShapeOk p m cost := by
  unfold editCostDenial
  rw [List.findSome?_eq_none_iff]
  have hm : ((p.action? t).map (·.meters)).getD [] = ((p.action? t).getD {}).meters := by
    cases p.action? t <;> rfl
  rw [hm]
  exact forall_congr' fun m => imp_congr_right fun _ => shape_none

theorem apply_ok {t : Nat} {k a pr rd : String} {c : CallRec} {rc : Option Cost}
    {ed : Option Edit} :
    (∃ v, applyApprove p s t k c a pr rd rc ed = .ok v) ↔
      (c.tool, c.digest) ∉ s.rejectedMemory ∧
      (∀ x, ed = some x → (c.tool, x.newDigest) ∉ s.rejectedMemory) ∧
      (∀ ttl, p.approvalTtl ((p.action? c.tool).getD {}) = some ttl → t < c.requestedAt + ttl) ∧
      rd = c.digest ∧ rc = c.cost ∧ (ed = none → ∀ w ∈ c.tally, w.1 ≠ pr) ∧
      ∀ x, ed = some x → p.bindingMutable = true ∧
        (∀ m ∈ ((p.action? c.tool).getD {}).meters, CostShapeOk p m x.newCost) ∧
        EligibleSome p s (c.consent.join (((p.action? c.tool).getD {}).effectiveConsent
          (x.newCost <|> c.cost) x.escalators)) a := by
  unfold applyApprove
  simp only [ite_error, Dispatch.any_ne, ne_eq, Decidable.not_not]
  cases ed with
  | none =>
    simp only [Option.any_none, Bool.or_false, decide_eq_true_eq, Option.isNone_none,
      Bool.true_and, List.any_eq_true, beq_iff_eq, Prod.exists, exists_and_right, exists_eq_right,
      not_exists, ok_ite, and_true, reduceCtorEq, false_implies, implies_true, forall_const,
      decide_eq_false_iff_not, Nat.not_le, true_and]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ⟨fun h w hw hp => h w.2 (hp ▸ hw), fun h b hb => h _ hb rfl⟩
  | some x =>
    simp only [Option.any_some, Bool.or_eq_true, decide_eq_true_eq, not_or,
      Option.isNone_some, Bool.false_and, Bool.false_eq_true, not_false_eq_true, true_and,
      Option.some.injEq, forall_eq', reduceCtorEq, false_implies, decide_eq_false_iff_not,
      Nat.not_le, and_assoc]
    rw [← editCost_none, ← eligibleAny_iff]
    by_cases hb : p.bindingMutable = true <;> cases hc : editCostDenial p c.tool x.newCost <;>
      cases State.eligibleAny p s (c.consent.join (((p.action? c.tool).getD {}).effectiveConsent
        (x.newCost <|> c.cost) x.escalators)) a <;> simp [hb, ok_ite]

theorem apply_accepted {t : Nat} {k a pr rd : String} {c : CallRec} {rc : Option Cost}
    {ed : Option Edit} {v : State × Verdict}
    (h : applyApprove p s t k c a pr rd rc ed = .ok v) : v.2.accepted = true := by
  revert h
  unfold applyApprove
  repeat' (first | (intro h; cases h; rfl) | (intro h; cases h) | (dsimp only) | split)

theorem grantDenial_none {t : Nat} {gid a tool : String} {dg : Option String} {sc : GrantScope}
    {n : Nat} {mc : Option Cost} {ex : Option Nat} :
    grantDenial p s t gid a tool dg sc n mc ex = none ↔ s.grants[gid]? = none ∧
      ∃ r, p.action? tool = some r ∧ ∃ gr, r.grantable = some gr ∧
        EligibleEvery p s r.grantConsent a ∧ (sc = .turn → s.turnActive = true) ∧
        sc.le gr.scope = true ∧ 0 < n ∧ (∀ m, mc = some m → 0 < m.amount) ∧ n ≤ gr.maxUses ∧
        (dg = none → gr.anyArgs = true ∧ (r.meters ≠ [] → gr.allowAnyArgsMetered = true)) ∧
        ∀ d, gr.maxDurationMs = some d → ∃ y, ex = some y ∧ y ≤ t + d := by
  unfold grantDenial
  cases hr : p.action? tool with
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, and_false, iff_false]
    split <;> simp
  | some r =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases hg : s.grants[gid]? = none
    · have hc : s.grants.contains gid = false := by
        rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hg]; rfl
      simp only [hc, hg, Bool.false_eq_true, ite_false, true_and]
      cases hgr : r.grantable with
      | none => simp
      | some gr =>
        simp only [Option.some.injEq, exists_eq_left']
        cases hel : s.eligibleAll p r.grantConsent a with
        | some _ =>
          simp only [reduceCtorEq, false_iff, not_and]
          intro h
          rw [← eligibleAll_iff, hel] at h
          cases h
        | none =>
          simp only [eligibleAll_iff.mp hel, true_and, Envelope.ite_none, Bool.or_eq_true, not_or,
            and_true, and_assoc]
          refine and_congr (by cases s.turnActive <;> simp) (and_congr (by simp)
            (and_congr (by simp [Nat.pos_iff_ne_zero]) (and_congr ?_ (and_congr (by simp) ?_))))
          · cases mc <;> simp [Nat.pos_iff_ne_zero]
          rw [← and_assoc]
          refine and_congr ?_ ?_
          · cases dg <;> cases gr.anyArgs <;> cases r.meters <;> simp
          · cases gr.maxDurationMs <;> cases ex <;> simp
    · have hc : s.grants.contains gid = true := by
        rw [Std.ExtTreeMap.contains_eq_isSome_getElem?]
        cases h : s.grants[gid]? with
        | none => exact absurd h hg
        | some _ => rfl
      simp [hc, hg]

end Accept

theorem accepted_iff_sessionStart {i pd req : String} {perms : List String}
    {apprs : List (String × ApproverInfo)} {l : Ledger}
    (he : e.body = .sessionStart i pd req perms apprs l) :
    (step p s e).2.accepted = true ↔
      EnvelopeOk s e ∧ pd = s.expectedPolicyDigest ∧ ∀ x ∈ l.entries, x.session ≠ i := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleSessionStart]
  refine and_congr_right fun _ => ?_
  split
  · simp_all [Verdict.accepted]
  · split <;> simp_all [Verdict.accepted]

theorem accepted_iff_sessionEnd (he : e.body = .sessionEnd) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e := by
  rw [Accept.step_iff]
  simp [stepHandle, he, handleSessionEnd, Verdict.accepted]

theorem accepted_iff_turnStart {u : Bool} (he : e.body = .turnStart u) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ s.turnActive = false := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleTurnStart]
  split <;> simp_all [Verdict.accepted]

theorem accepted_iff_turnEnd (he : e.body = .turnEnd) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ s.turnActive = true := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleTurnEnd]
  split <;> simp_all [Verdict.accepted]

theorem accepted_iff_stepStart (he : e.body = .stepStart) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧
      (p.mode = .logOnly ∨ ∀ n, p.limits.maxStepsPerTurn = some n → s.stepsThisTurn < n) := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleStepStart]
  refine and_congr_right fun _ => ?_
  cases hn : p.limits.maxStepsPerTurn with
  | none => simp [Verdict.accepted]
  | some n =>
    by_cases h : s.stepsThisTurn < n
    · simp [h, Verdict.accepted]
    · cases p.mode <;> simp [h, Verdict.accepted]

theorem accepted_iff_approverAttest {a : String} {i : ApproverInfo}
    (he : e.body = .approverAttest a i) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∀ j, s.approvers[a]? = some j → j = i := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleApproverAttest, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  split <;> rename_i h
  · simp only [Verdict.accepted, Bool.false_eq_true, false_iff]
    obtain ⟨j, hj, hne⟩ := (Option.any_eq_true _ _).mp h
    exact fun hall => by simp [hall j hj] at hne
  · simp only [Verdict.accepted, true_iff]
    intro j hj
    rw [hj] at h
    simpa using h

theorem accepted_iff_permissionRevoke {perm : String} (he : e.body = .permissionRevoke perm) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e := by
  rw [Accept.step_iff]
  simp [stepHandle, he, handlePermissionRevoke, Verdict.accepted]

theorem accepted_iff_reset (he : e.body = .reset) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e := by
  rw [Accept.step_iff]
  simp [stepHandle, he, handleReset, Verdict.accepted]

theorem accepted_iff_kill (he : e.body = .kill) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e := by
  rw [Accept.step_iff]
  simp [stepHandle, he, handleKill, Verdict.accepted]

theorem accepted_iff_permissionAdd {perm a : String} (he : e.body = .permissionAdd perm a) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∃ info, s.approvers[a]? = some info ∧
      info.principal ≠ "agent" ∧ ∃ x ∈ info.roles, x ∈ p.approverRoles := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handlePermissionAdd]
  refine and_congr_right fun _ => ?_
  have h : s.eligibleAny p .none a = none ↔ _ := Accept.eligibleAny_iff
  have hc : ClausesOrOne .none = [{ k := 1, humanOnly := false }] := rfl
  simp only [EligibleSome, hc, List.mem_singleton, exists_eq_left, EligibleFor] at h
  split
  · rename_i r hr
    simp only [Verdict.accepted, Bool.false_eq_true, false_iff]
    intro ⟨info, hi, hag, hrole⟩
    have := h.mpr ⟨info, hi, info, hi, rfl, hag, hrole, by simp, by simp, by simp⟩
    rw [hr] at this
    cases this
  · rename_i hr
    obtain ⟨info, hi, info', hi', -, hag, hrole, -⟩ := h.mp hr
    rw [hi] at hi'
    cases hi'
    split <;> simpa [Verdict.accepted] using ⟨info, hi, hag, hrole⟩

theorem accepted_iff_escalationAck {a : String} {n : Nat} (he : e.body = .escalationAck a n) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧
      (∃ t, Blocked s t) ∧ EscalationEligible p s a ∧ n = s.escalations := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleEscalationAck]
  refine and_congr_right fun _ => ?_
  have hb : s.anyBlocked = true ↔ ∃ t, Blocked s t := by
    unfold State.anyBlocked Blocked
    cases hs : s.blockedTools with
    | nil => simp
    | cons t ts =>
      simp only [List.isEmpty_cons, Bool.not_false, Bool.or_true, true_iff]
      exact ⟨t, by simp⟩
  have hel : s.escalationEligible p a = none ↔ EscalationEligible p s a := by
    refine ⟨Escalation.eligible_of, fun ⟨info, hi, hag, hrole⟩ => ?_⟩
    unfold State.escalationEligible
    rw [Std.ExtTreeMap.get?_eq_getElem?, hi]
    simp_all
  split
  · rename_i h
    simp only [Verdict.accepted, Bool.false_eq_true, false_iff]
    rintro ⟨hx, -⟩
    rw [← hb] at hx
    simp [hx] at h
  · rename_i h
    have hx : s.anyBlocked = true := by simpa using h
    rw [hb] at hx
    simp only [hx, true_and]
    split
    · rename_i r hr
      simp only [Verdict.accepted, Bool.false_eq_true, false_iff]
      rintro ⟨he', -⟩
      rw [← hel, hr] at he'
      cases he'
    · rename_i hr
      simp only [hel.mp hr, true_and]
      split <;> simp_all [Verdict.accepted]

theorem accepted_iff_ledgerSync {l : Ledger} (he : e.body = .ledgerSync l) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ s.ledger.version ≤ l.version ∧
      (∀ x ∈ l.entries, x.session = s.sessionId → l.entries.count x ≤ s.ledger.entries.count x) ∧
      (∀ x ∈ s.ledger.entries, x.session = s.sessionId → x ∉ l.entries → x.committed = true) ∧
      ¬(s.ledger.tombstone = true ∧ l.tombstone = false ∧ s.ended = false) := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleLedgerSync]
  refine and_congr_right fun _ => ?_
  have hcount : ∀ x ∈ l.entries.filter (·.session == s.sessionId),
      (l.entries.filter (·.session == s.sessionId)).count x ≤
        (s.ledger.entries.filter (·.session == s.sessionId)).count x ↔
      l.entries.count x ≤ s.ledger.entries.count x := by
    intro x hx
    have hs := (List.mem_filter.mp hx).2
    rw [List.count_filter (p := fun y : MeterEntry => y.session == s.sessionId) hs,
      List.count_filter (p := fun y : MeterEntry => y.session == s.sessionId) hs]
  have hA : ((l.entries.filter (·.session == s.sessionId)).all fun x =>
      decide ((l.entries.filter (·.session == s.sessionId)).count x ≤
        (s.ledger.entries.filter (·.session == s.sessionId)).count x)) = true ↔
      ∀ x ∈ l.entries, x.session = s.sessionId → l.entries.count x ≤ s.ledger.entries.count x := by
    rw [List.all_eq_true]
    constructor
    · intro h x hx hs
      have hm : x ∈ l.entries.filter (·.session == s.sessionId) :=
        List.mem_filter.mpr ⟨hx, by simpa using hs⟩
      have := h x hm
      rwa [decide_eq_true_eq, hcount x hm] at this
    · intro h x hm
      rw [decide_eq_true_eq, hcount x hm]
      have ⟨hx, hs⟩ := List.mem_filter.mp hm
      exact h x hx (by simpa using hs)
  have hB : (((s.ledger.entries.filter (·.session == s.sessionId)).filter fun x =>
      !(l.entries.filter (·.session == s.sessionId)).contains x).all (·.committed)) = true ↔
      ∀ x ∈ s.ledger.entries, x.session = s.sessionId → x ∉ l.entries → x.committed = true := by
    rw [List.all_eq_true]
    constructor
    · intro h x hx hs hn
      refine h x (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hx, by simpa using hs⟩, ?_⟩)
      simp [List.mem_filter, hn]
    · intro h x hm
      obtain ⟨hm1, hm2⟩ := List.mem_filter.mp hm
      obtain ⟨hx, hs⟩ := List.mem_filter.mp hm1
      refine h x hx (by simpa using hs) fun hl => ?_
      simp [List.mem_filter, hl, hs] at hm2
  split
  · rename_i h
    simp only [Verdict.accepted, Bool.false_eq_true, false_iff]
    rintro ⟨hv, hc, hm, ht⟩
    rw [hA.mpr hc, hB.mpr hm] at h
    cases hlt : s.ledger.tombstone <;> cases hl : l.tombstone <;> cases hen : s.ended <;>
      simp_all <;> omega
  · rename_i h
    simp only [Verdict.accepted, true_iff]
    refine ⟨Nat.not_lt.mp fun hlt => h (by simp [hlt]), hA.mp ?_, hB.mp ?_,
      fun ⟨h1, h2, h3⟩ => h (by simp [h1, h2, h3])⟩
    · refine Classical.byContradiction fun hn => h ?_
      rw [Bool.eq_false_iff.mpr hn]
      simp
    · refine Classical.byContradiction fun hn => h ?_
      rw [Bool.eq_false_iff.mpr hn]
      simp

theorem accepted_iff_propose {k t dg : String} {cost : Option Cost} {gs es : List (String × Bool)}
    (he : e.body = .propose k t dg cost gs es) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∀ c, s.calls[k]? = some c → c.tool = t ∧
      ((c.proposedDigest = dg ∧ c.proposedCost = cost) ∨ (c.digest = dg ∧ c.cost = cost)) := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handlePropose, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  cases s.calls[k]? with
  | none =>
    simp only [reduceCtorEq, false_implies, implies_true, iff_true]
    repeat' (first | rfl | split)
  | some c =>
    simp only [Option.some.injEq, forall_eq', Prod.mk.injEq]
    split <;> simp_all [Verdict.accepted]

theorem accepted_iff_grantRevoke {gid : String} (he : e.body = .grantRevoke gid) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∃ gr, s.grants[gid]? = some gr := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleGrantRevoke, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  cases s.grants[gid]? <;> simp [Verdict.accepted]

theorem accepted_iff_result {k : String} {o : Outcome} {ac : Option Nat} {ne : Bool}
    (he : e.body = .result k o ac ne) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧
      ∃ c, s.calls[k]? = some c ∧ c.status = .dispatched := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleResult, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  cases s.calls[k]? with
  | none => simp [Verdict.accepted]
  | some c =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases h : c.status = .dispatched
    · simp only [h, ne_eq, not_true_eq_false, ite_false, iff_true]
      repeat' (first | rfl | split)
    · simp [h, Verdict.accepted]

theorem accepted_iff_outcomeUnknown {k : String} (he : e.body = .outcomeUnknown k) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧
      ∃ c, s.calls[k]? = some c ∧ c.status = .dispatched := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleOutcomeUnknown, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  cases s.calls[k]? with
  | none => simp [Verdict.accepted]
  | some c => by_cases h : c.status = .dispatched <;> simp [h, Verdict.accepted]

theorem accepted_iff_reconcile {k : String} {o : Outcome} {ac : Option Nat} {ne : Bool}
    (he : e.body = .reconcile k o ac ne) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧
      ∃ c, s.calls[k]? = some c ∧ c.status = .unknown ∧ c.reconciled = none := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleReconcile, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  cases s.calls[k]? with
  | none => simp [Verdict.accepted]
  | some c =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases h : c.status = .unknown
    · cases hr : c.reconciled with
      | some _ => simp [h, Verdict.accepted]
      | none =>
        simp only [h, ne_eq, not_true_eq_false, ite_false, Option.isSome_none,
          Bool.false_eq_true, and_self, iff_true]
        repeat' (first | rfl | split)
    · simp [h, Verdict.accepted]

theorem accepted_iff_cancel {k : String} (he : e.body = .cancel k) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧
      ∃ c, s.calls[k]? = some c ∧ (c.status = .awaiting ∨ c.status = .authorized) := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleCancel, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  cases s.calls[k]? with
  | none => simp [Verdict.accepted]
  | some c =>
    simp only [Option.some.injEq, exists_eq_left']
    split <;> simp_all [Verdict.accepted]

theorem accepted_iff_approvalExpire {k : String} {rid : RequestId}
    (he : e.body = .approvalExpire k rid) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∃ c, s.calls[k]? = some c ∧
      c.status = .awaiting ∧ rid = ⟨s.sessionId, k, c.generation⟩ ∧ c.epoch = s.epoch := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleApprovalExpire]
  refine and_congr_right fun _ => ?_
  simp only [← Accept.callCheck_ok]
  split <;> simp_all [Verdict.accepted]

theorem accepted_iff_reject {k a : String} {rid : RequestId} (he : e.body = .reject k rid a) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∃ c, s.calls[k]? = some c ∧
      (c.status = .awaiting ∨ (c.status = .authorized ∧ c.attempts = 0)) ∧
      rid.session = s.sessionId ∧ rid.call = k ∧ rid.generation ≤ c.generation ∧
      c.epoch = s.epoch ∧ EligibleSome p s c.consent a := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleReject]
  refine and_congr_right fun _ => ?_
  simp only [← Accept.vetoCheck_ok]
  split <;> simp_all [Verdict.accepted]

theorem accepted_iff_approve {k a rd : String} {rid : RequestId} {rc : Option Cost}
    {ed : Option Edit} (he : e.body = .approve k rid a rd rc ed) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∃ c, s.calls[k]? = some c ∧
      c.status = .awaiting ∧ rid = ⟨s.sessionId, k, c.generation⟩ ∧ c.epoch = s.epoch ∧
      EligibleSome p s c.consent a ∧
      (c.tool, c.digest) ∉ s.rejectedMemory ∧
      (∀ x, ed = some x → (c.tool, x.newDigest) ∉ s.rejectedMemory) ∧
      (∀ ttl, p.approvalTtl ((p.action? c.tool).getD {}) = some ttl →
        e.time < c.requestedAt + ttl) ∧
      rd = c.digest ∧ rc = c.cost ∧
      (ed = none → ∀ info, s.approvers[a]? = some info → ∀ w ∈ c.tally, w.1 ≠ info.principal) ∧
      ∀ x, ed = some x → p.bindingMutable = true ∧
        (∀ m ∈ ((p.action? c.tool).getD {}).meters, CostShapeOk p m x.newCost) ∧
        EligibleSome p s (c.consent.join (((p.action? c.tool).getD {}).effectiveConsent
          (x.newCost <|> c.cost) x.escalators)) a := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleApprove, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    split at h
    · simp [Verdict.accepted] at h
    · rename_i c hc
      obtain ⟨hcc, hel⟩ := Accept.awaitingCheck_ok.mp hc
      obtain ⟨hk, hst, hrid, hep⟩ := Accept.callCheck_ok.mp hcc
      obtain ⟨info, hi, hcl⟩ := hel
      split at h
      · simp [Verdict.accepted] at h
      · rename_i v hv
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Accept.apply_ok.mp ⟨v, hv⟩
        rw [hi] at h6
        refine ⟨c, hk, hst, hrid, hep, ⟨info, hi, hcl⟩, h1, h2, h3, h4, h5, ?_, h7⟩
        intro hn info' hi'
        rw [hi] at hi'
        cases hi'
        exact h6 hn
  · rintro ⟨c, hk, hst, hrid, hep, hel, h1, h2, h3, h4, h5, h6, h7⟩
    rw [Accept.awaitingCheck_ok.mpr ⟨Accept.callCheck_ok.mpr ⟨hk, hst, hrid, hep⟩, hel⟩]
    obtain ⟨info, hi, -⟩ := hel
    obtain ⟨v, hv⟩ := (Accept.apply_ok (k := k) (pr := info.principal)).mpr
      ⟨h1, h2, h3, h4, h5, fun hn => h6 hn info hi, h7⟩
    have hpr : ((s.approvers[a]?).map (·.principal)).getD a = info.principal := by rw [hi]; rfl
    dsimp only
    rw [hpr, hv]
    exact Accept.apply_accepted hv

theorem accepted_iff_grantCreate {gid a t : String} {dg : Option String} {sc : GrantScope}
    {n : Nat} {mc : Option Cost} {nb ex : Option Nat} {rsd : String}
    (he : e.body = .grantCreate gid a t dg sc n mc nb ex rsd) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ s.grants[gid]? = none ∧
      ∃ r, p.action? t = some r ∧ ∃ gr, r.grantable = some gr ∧
        EligibleEvery p s r.grantConsent a ∧ (sc = .turn → s.turnActive = true) ∧
        sc.le gr.scope = true ∧ 0 < n ∧ (∀ m, mc = some m → 0 < m.amount) ∧ n ≤ gr.maxUses ∧
        (dg = none → gr.anyArgs = true ∧ (r.meters ≠ [] → gr.allowAnyArgsMetered = true)) ∧
        ∀ d, gr.maxDurationMs = some d → ∃ y, ex = some y ∧ y ≤ e.time + d := by
  rw [Accept.step_iff]
  simp only [stepHandle, he, handleGrantCreate]
  refine and_congr_right fun _ => ?_
  rw [← Accept.grantDenial_none]
  split <;> simp_all [Verdict.accepted]

namespace Accept

def aPolicy : Policy :=
  { approverRoles := ["owner"]
    meters := [("usd", { unit := .money "USD", cap := some 100, scope := .principal })]
    limits := { maxStepsPerTurn := some 1, maxConsecutiveFailures := some 2 }
    actions :=
      [ ("t", { consent := .perCall
                grantable := some { scope := .session, maxUses := 2, maxDurationMs := some 50 } })
      , ("u", {}), ("m", { meters := ["usd"] })
      , ("v", { consent := .perCall, meters := ["usd"] })
      , ("q", { consent := .quorum 2 none true false }) ] }

def ev (n : Nat) (b : EventBody) : Event := ⟨n, n, n - 1, none, b⟩

def alice : ApproverInfo := ⟨"alice", .human, ["owner"]⟩

def start : EventBody :=
  .sessionStart "s1" "pd" "u1" [] [("a1", alice), ("bot", ⟨"agent", .automated, ["owner"]⟩)] {}

/-- `c1` and `c4` await approval, `c2` and `c5` are dispatched (`c5` holds a principal
reservation), `c3` is Unknown. Its `outcome_unknown` counts one failure of `u`, so a failed `c2`
escalates the session. -/
def base : List Event :=
  [ ev 1 start
  , ev 2 (.turnStart true)
  , ev 3 (.propose "c1" "t" "d1" none [] [])
  , ev 4 (.propose "c2" "u" "d2" none [] [])
  , ev 5 (.dispatch "c2" 1 "d2" none [] "k2")
  , ev 6 (.propose "c3" "u" "d3" none [] [])
  , ev 7 (.dispatch "c3" 1 "d3" none [] "k3")
  , ev 8 (.outcomeUnknown "c3")
  , ev 9 (.propose "c4" "t" "d4" none [] [])
  , ev 10 (.propose "c5" "m" "d5" (some ⟨5, "USD"⟩) [] [])
  , ev 11 (.dispatch "c5" 1 "d5" (some ⟨5, "USD"⟩) [] "k5") ]

def sA : State := after aPolicy "pd" base

def next (b : EventBody) : Verdict := (step aPolicy sA (ev 12 b)).2

def after1 (b : EventBody) : State := (step aPolicy sA (ev 12 b)).1

def then2 (b b' : EventBody) : Verdict := (step aPolicy (after1 b) (ev 13 b')).2

#guard (trace aPolicy (State.initial "pd") base).all (·.2.2.accepted)
#guard (sA.calls["c1"]?.map (·.status)) == some .awaiting
#guard (sA.calls["c2"]?.map (·.status)) == some .dispatched
#guard (sA.calls["c3"]?.map (·.status)) == some .unknown
#guard (sA.calls["c5"]?.map (·.status)) == some .dispatched
#guard sA.ledger.entries.length == 1 && !sA.ledger.entries.all (·.committed)

#guard (step aPolicy (State.initial "pd") (ev 1 start)).2 == .ok .none none
#guard (step aPolicy (State.initial "pd")
  (ev 1 (.sessionStart "s1" "other" "u1" [] [] {}))).2 == .rejected .policyDigestMismatch
#guard (step aPolicy (State.initial "pd")
  (ev 1 (.sessionStart "s1" "pd" "u1" [] [] sA.ledger))).2 == .rejected .alreadyStarted

#guard next .sessionEnd == .ok .none none
#guard next (.permissionRevoke "p1") == .ok .none none
#guard next .reset == .ok .none none
#guard next .kill == .ok .none none

#guard next .turnEnd == .ok .none none
#guard then2 .turnEnd .turnEnd == .rejected .turnState
#guard then2 .turnEnd (.turnStart false) == .ok .none none
#guard next (.turnStart false) == .rejected .turnState

#guard next .stepStart == .ok .none none
#guard then2 .stepStart .stepStart == .rejected .stepLimit
#guard (step { aPolicy with mode := .logOnly } (after1 .stepStart) (ev 13 .stepStart)).2
  == .ok .none (some (.wouldDeny .stepLimit))

#guard next (.propose "c1" "t" "d1" none [] []) == .ok (.needsApproval ⟨"s1", "c1", 0⟩) none
#guard next (.propose "c1" "t" "d9" none [] []) == .rejected .duplicateCall
#guard next (.propose "c1" "u" "d1" none [] []) == .rejected .duplicateCall

#guard next (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none none) == .ok .authorized none
#guard next (.approve "c1" ⟨"s1", "c1", 0⟩ "bot" "d1" none none)
  == .rejected .approverNotEligible
#guard next (.approve "c1" ⟨"s1", "c1", 1⟩ "a1" "d1" none none) == .rejected .staleRequest
#guard next (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d9" none none) == .rejected .digestMismatch

/-- The verdicts of `bs` taken in order from `sA`, from event 12 on. -/
def run₂ (q : Policy) (bs : List EventBody) : List Verdict :=
  (trace q sA (bs.zipIdx.map fun (b, i) => ev (12 + i) b)).map (·.2.2)

def editD9 : Edit := { newDigest := "d9" }

#guard next (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none (some editD9)) == .ok .authorized none
#guard (step { aPolicy with bindingMutable := false } sA
  (ev 12 (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none (some editD9)))).2
  == .rejected .editNotAllowed
#guard run₂ aPolicy
  [ .propose "c6" "v" "d6" (some ⟨5, "USD"⟩) [] []
  , .approve "c6" ⟨"s1", "c6", 0⟩ "a1" "d6" (some ⟨5, "USD"⟩) (some { newDigest := "d7" }) ]
  == [.ok (.needsApproval ⟨"s1", "c6", 0⟩) none, .rejected .costMissing]
-- `c1` was proposed at time 3, so a 9 ms approval TTL ends at time 12.
#guard (step { aPolicy with limits.approvalTtlMs := some 9 } sA
  (ev 12 (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none none))).2 == .rejected .approvalExpired
#guard (step { aPolicy with limits.approvalTtlMs := some 10 } sA
  (ev 12 (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none none))).2 == .ok .authorized none
#guard run₂ aPolicy
  [ .propose "c6" "q" "d6" none [] []
  , .approve "c6" ⟨"s1", "c6", 0⟩ "a1" "d6" none none
  , .approve "c6" ⟨"s1", "c6", 0⟩ "a1" "d6" none none ]
  == [.ok (.needsApproval ⟨"s1", "c6", 0⟩) none, .ok .pending none, .rejected .alreadyApproved]

#guard next (.reject "c4" ⟨"s1", "c4", 0⟩ "a1") == .ok .none none
#guard next (.reject "c4" ⟨"s1", "c4", 0⟩ "bot") == .rejected .approverNotEligible
#guard next (.reject "c2" ⟨"s1", "c2", 0⟩ "a1") == .rejected .callDispatched
-- `u` needs no consent, so `c6` is Authorized and its veto is checked against the fallback.
#guard ((after1 (.propose "c6" "u" "d6" none [] [])).calls["c6"]?).any fun c =>
  c.status == .authorized && c.consent.clauses.isEmpty
#guard then2 (.propose "c6" "u" "d6" none [] []) (.reject "c6" ⟨"s1", "c6", 0⟩ "a1")
  == .ok .none none
#guard ((step aPolicy (after1 (.propose "c6" "u" "d6" none [] []))
  (ev 13 (.reject "c6" ⟨"s1", "c6", 0⟩ "a1"))).1.calls["c6"]?).any (·.status == .rejected)
#guard then2 (.propose "c6" "u" "d6" none [] []) (.reject "c6" ⟨"s1", "c6", 0⟩ "bot")
  == .rejected .approverNotEligible

#guard next (.approvalExpire "c1" ⟨"s1", "c1", 0⟩) == .ok .none none
#guard next (.approvalExpire "c1" ⟨"s1", "c1", 1⟩) == .rejected .staleRequest

/-- Event time 12 plus `max_duration_ms` 50 bounds `expires_at`. -/
def grantT (uses : Nat) (exp : Option Nat) : EventBody :=
  .grantCreate "g1" "a1" "t" (some "d9") .session uses none none exp "rs"

#guard next (grantT 2 (some 62)) == .ok .none none
#guard next (grantT 2 (some 63)) == .rejected .grantNotAllowed
#guard next (grantT 2 none) == .rejected .grantNotAllowed
#guard next (grantT 3 (some 62)) == .rejected .grantNotAllowed
#guard next (.grantCreate "g1" "a1" "u" none .session 1 none none none "rs")
  == .rejected .grantNotAllowed

#guard then2 (grantT 2 (some 62)) (.grantRevoke "g1") == .ok .none none
#guard next (.grantRevoke "g1") == .rejected .unknownGrant

#guard next (.approverAttest "a1" alice) == .ok .none none
#guard next (.approverAttest "a1" { alice with roles := [] }) == .rejected .approverChanged

#guard next (.permissionAdd "p1" "a1") == .ok .none none
#guard next (.permissionAdd "p1" "bot") == .rejected .approverNotEligible

#guard next (.result "c2" .succeeded none false) == .ok .none none
#guard next (.result "c1" .succeeded none false) == .rejected .callAwaiting

#guard next (.outcomeUnknown "c2") == .ok .none none
#guard next (.outcomeUnknown "c3") == .rejected .callUnknown

#guard next (.reconcile "c3" .failed none false) == .ok .none none
#guard next (.reconcile "c2" .failed none false) == .rejected .callDispatched
#guard then2 (.reconcile "c3" .failed none false) (.reconcile "c3" .failed none false)
  == .rejected .alreadyReconciled

#guard next (.cancel "c1") == .ok .none none
#guard next (.cancel "c2") == .rejected .callDispatched

#guard next (.escalationAck "a1" 0) == .rejected .notEscalated
#guard (after1 (.result "c2" .failed none false)).escalated
#guard (after1 (.result "c2" .failed none false)).escalations == 1
#guard then2 (.result "c2" .failed none false) (.escalationAck "a1" 1) == .ok .none none
#guard then2 (.result "c2" .failed none false) (.escalationAck "a1" 0)
  == .rejected .staleRequest
#guard then2 (.result "c2" .failed none false) (.escalationAck "bot" 1)
  == .rejected .approverNotEligible

#guard next (.ledgerSync sA.ledger) == .ok .none none
#guard next (.ledgerSync { sA.ledger with version := sA.ledger.version + 3 }) == .ok .none none
#guard next (.ledgerSync { sA.ledger with version := 0 }) == .rejected .ledgerConflict
#guard next (.ledgerSync { sA.ledger with entries := sA.ledger.entries ++ sA.ledger.entries })
  == .rejected .ledgerConflict
#guard next (.ledgerSync { sA.ledger with entries := [] }) == .rejected .ledgerConflict
#guard then2 (.ledgerSync { sA.ledger with tombstone := true }) (.ledgerSync sA.ledger)
  == .rejected .ledgerConflict
#guard then2 (.ledgerSync { sA.ledger with tombstone := true })
  (.ledgerSync { sA.ledger with tombstone := true }) == .ok .none none

end Accept

end Writ.Proofs
