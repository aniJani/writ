import WritProofs.Consent

namespace Writ.Proofs

open Writ
open Basic Calls Proofs.Consent

/-- Section 8, theorem 1(a): tally entry `w` of call `k`, read against the call's record `c`, was
counted by an accepted `approve` in the trace that echoed the request, digest and cost of the
generation it approved, within the action's approval TTL of that request (`c₀`, the record the
approve read) and of the record `c`. An editor answers the request of the generation it replaces
and approves the new one. -/
def ApprovedBy (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec)
    (w : String × String) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    ∃ rid dg₀ cost₀ ed, e₀.body = .approve k rid w.2 dg₀ cost₀ ed ∧
      rid.session = s₀.sessionId ∧ rid.call = k ∧ c.requestedAt ≤ e₀.time ∧
      (∀ ttl, p.approvalTtl ((p.action? c.tool).getD {}) = some ttl →
        e₀.time < c.requestedAt + ttl) ∧
      (∃ c₀, s₀.calls[k]? = some c₀ ∧ c₀.tool = c.tool ∧ c₀.generation = rid.generation ∧
        c₀.requestedAt ≤ e₀.time ∧
        ∀ ttl, p.approvalTtl ((p.action? c₀.tool).getD {}) = some ttl →
          e₀.time < c₀.requestedAt + ttl) ∧
      ((ed = none ∧ rid.generation = c.generation ∧ dg₀ = c.digest ∧ cost₀ = c.cost) ∨
        ∃ x, ed = some x ∧ rid.generation + 1 = c.generation ∧ x.newDigest = c.digest ∧
          (x.newCost <|> cost₀) = c.cost)

variable {p : Policy} {d : String} {s s' : State} {e : Event} {es : List Event} {k : String}
  {c c' : CallRec} {w : String × String}

theorem ApprovedBy.mono (h : ApprovedBy p d es k c w) : ApprovedBy p d (es ++ [e]) k c w := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem ApprovedBy.congr (h : ApprovedBy p d es k c w) (ht : c'.tool = c.tool)
    (hr : c'.requestedAt = c.requestedAt) (hg : c'.generation = c.generation)
    (hd : c'.digest = c.digest) (hc : c'.cost = c.cost) : ApprovedBy p d es k c' w := by
  unfold ApprovedBy
  rw [ht, hr, hg, hd, hc]
  exact h

theorem ApprovedBy.same (h : ApprovedBy p d es k c w) (hs : RecSame c c') :
    ApprovedBy p d es k c' w :=
  h.congr hs.tool hs.requestedAt hs.generation hs.digest hs.cost

/-- The history-linked invariant behind `approvals`: every tally entry of every call has its
`approve` in the trace so far, read against the call's current record. -/
structure ApprovalInv (p : Policy) (d : String) (es : List Event) : Prop where
  tally : ∀ (k : String) (c : CallRec), (after p d es).calls[k]? = some c →
    ∀ w ∈ c.tally, ApprovedBy p d es k c w
  requestedAt : ∀ (k : String) (c : CallRec), (after p d es).calls[k]? = some c →
    c.requestedAt ≤ (after p d es).lastTime

namespace Approvals

/-- What an accepted `e` may leave in a call record: one from before the step up to `RecSame`, or
one whose tally entries already have their witness in the trace ending with `e`. -/
def Settled (p : Policy) (d : String) (es : List Event) (e : Event) (s' : State) : Prop :=
  ∀ (k : String) (c' : CallRec), s'.calls[k]? = some c' →
    (∃ c, (after p d es).calls[k]? = some c ∧ RecSame c c') ∨
      ((∀ w ∈ c'.tally, ApprovedBy p d (es ++ [e]) k c' w) ∧ c'.requestedAt ≤ e.time)

theorem Settled.of_keeps (h : Keeps (after p d es) s') : Settled p d es e s' :=
  fun k c' hc => .inl (h.calls k c' hc)

theorem Settled.of_calls (h : s'.calls = (after p d es).calls) : Settled p d es e s' :=
  fun _ c' hc => .inl ⟨c', h ▸ hc, .refl⟩

theorem envelope_time (h : stepEnvelope s e = none) : s.lastTime ≤ e.time := by
  unfold stepEnvelope at h
  dsimp only at h
  repeat' split at h
  all_goals first | (cases h; done) | omega

theorem applyApprove_spec (h : applyApprove p s t k rc a pr dg cost ed = .ok r) :
    ∃ x, r.1 = { s with calls := s.calls.insert k x } ∧ x.tool = rc.tool ∧
      (∀ ttl, p.approvalTtl ((p.action? rc.tool).getD {}) = some ttl → t < rc.requestedAt + ttl) ∧
      dg = rc.digest ∧ cost = rc.cost ∧
      ((ed = none ∧ x.tally = rc.tally ++ [(pr, a)] ∧ x.generation = rc.generation ∧
          x.digest = rc.digest ∧ x.cost = rc.cost ∧ x.requestedAt = rc.requestedAt) ∨
        ∃ ed', ed = some ed' ∧ x.tally = [(pr, a)] ∧ x.generation = rc.generation + 1 ∧
          x.digest = ed'.newDigest ∧ x.cost = (ed'.newCost <|> rc.cost) ∧ x.requestedAt = t) := by
  unfold applyApprove at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i httl
  split at h
  · cases h
  rename_i hdg
  split at h
  · cases h
  rename_i hcost
  split at h
  · cases h
  have httl' : ∀ ttl, p.approvalTtl ((p.action? rc.tool).getD {}) = some ttl →
      t < rc.requestedAt + ttl := by
    intro ttl ho
    rw [ho] at httl
    simp only [Option.any_some, decide_eq_true_eq] at httl
    omega
  have hdg' : dg = rc.digest := Classical.not_not.mp hdg
  have hcost' : cost = rc.cost := Classical.not_not.mp hcost
  cases ed with
  | none =>
    dsimp only at h
    split at h <;> cases h
    · exact ⟨_, rfl, rfl, httl', hdg', hcost', .inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨_, rfl, rfl, httl', hdg', hcost', .inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | some ed' =>
    dsimp only at h
    split at h
    · cases h
    rename_i rec' hn
    have hx : rec'.tool = rc.tool ∧ rec'.tally = [(pr, a)] ∧ rec'.generation = rc.generation + 1 ∧
        rec'.digest = ed'.newDigest ∧ rec'.cost = (ed'.newCost <|> rc.cost) ∧
        rec'.requestedAt = t := by
      revert hn
      repeat' split
      all_goals (intro hn; cases hn)
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
    split at h <;> cases h
    · exact ⟨_, rfl, h₁, httl', hdg', hcost', .inr ⟨ed', rfl, h₂, h₃, h₄, h₅, h₆⟩⟩
    · exact ⟨_, rfl, h₁, httl', hdg', hcost', .inr ⟨ed', rfl, h₂, h₃, h₄, h₅, h₆⟩⟩

theorem awaitingCheck_rid (h : awaitingCheck p s k rid a = .ok rc) :
    rid = ⟨s.sessionId, k, rc.generation⟩ := by
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
           rename_i hn
           simp only [ne_eq, not_or, Classical.not_not] at hn
           exact hn.1)

theorem settled_approve (h : ApprovalInv p d es) (ha : (step p (after p d es) e).2.accepted = true)
    (hb : e.body = .approve i rid a dg cost ed) :
    Settled p d es e (handleApprove p (after p d es) e.time i rid a dg cost ed).1 := by
  have hle := envelope_time (accepted_open ha)
  unfold handleApprove
  split
  · exact .of_calls rfl
  · rename_i rc hck
    have hk := awaitingCheck_ok hck
    have hrid := awaitingCheck_rid hck
    have hreq := h.requestedAt i rc hk
    subst hrid
    dsimp only
    split
    · exact .of_calls rfl
    · rename_i r hr
      obtain ⟨x, hx, htool, httl, hdg, hcost, hcase⟩ := applyApprove_spec hr
      rw [hx]
      intro k' c' hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        cases hc'
        right
        rcases hcase with ⟨hed, htally, hgen, hdig, hcst, hra⟩ |
          ⟨ed', hed, htally, hgen, hdig, hcst, hra⟩
        · refine ⟨fun v hv => ?_, by omega⟩
          rw [htally] at hv
          rcases List.mem_append.mp hv with hv | hv
          · exact ((h.tally i rc hk v hv).congr htool hra hgen hdig hcst).mono
          · rw [List.mem_singleton.mp hv]
            refine ⟨_, _, _, trace_mem_last, ha, _, dg, cost, ed, hb, rfl, rfl, by omega, ?_,
              ⟨rc, hk, htool.symm, rfl, by omega, httl⟩,
              .inl ⟨hed, hgen.symm, hdig.symm ▸ hdg, hcst.symm ▸ hcost⟩⟩
            rw [htool, hra]
            exact httl
        · refine ⟨fun v hv => ?_, by omega⟩
          rw [htally, List.mem_singleton] at hv
          subst hv
          refine ⟨_, _, _, trace_mem_last, ha, _, dg, cost, ed, hb, rfl, rfl, by omega, ?_,
            ⟨rc, hk, htool.symm, rfl, by omega, httl⟩,
            .inr ⟨ed', hed, hgen.symm, hdig.symm, by rw [hcst, hcost]⟩⟩
          intro ttl ht
          rw [htool] at ht
          have := httl ttl ht
          omega
      · exact .inl ⟨c', hc', .refl⟩

theorem settled_propose {tool dg : String} {cs : Option Cost} {gs xs : List (String × Bool)} :
    Settled p d es e (handlePropose p (after p d es) e.time i tool dg cs gs xs).1 := by
  unfold handlePropose
  split
  · split <;> exact .of_calls rfl
  · split
    split
    · exact .of_calls rfl
    · intro k' c' hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · cases hc'
        refine .inr ⟨fun _ hw => (nomatch hw), ?_⟩
        dsimp only
        split <;> omega
      · exact .inl ⟨c', hc', .refl⟩

theorem sessionStart_calls_eq : (handleSessionStart s i pd r ps as l).1.calls = s.calls := by
  unfold handleSessionStart
  split
  · rfl
  · split <;> rfl

theorem grantCreate_calls_eq :
    (handleGrantCreate p s t gid a tool dg sc n mc nb ex rv).1.calls = s.calls := by
  unfold handleGrantCreate
  split <;> rfl

theorem settled_stepHandle (h : ApprovalInv p d es)
    (ha : (step p (after p d es) e).2.accepted = true) :
    Settled p d es e (stepHandle p (after p d es) e).1 := by
  unfold Writ.stepHandle
  split <;> rename_i hb
  all_goals first
    | with_reducible exact .of_calls sessionStart_calls_eq
    | with_reducible exact .of_calls grantCreate_calls_eq
    | with_reducible exact settled_approve h ha hb
    | with_reducible exact settled_propose
    | with_reducible exact .of_keeps handleSessionEnd_kept
    | with_reducible exact .of_keeps handleTurnStart_kept
    | with_reducible exact .of_keeps handleTurnEnd_kept
    | with_reducible exact .of_keeps handleStepStart_kept
    | with_reducible exact .of_keeps handleApproverAttest_kept
    | with_reducible exact .of_keeps handlePermissionRevoke_kept
    | with_reducible exact .of_keeps handleReject_kept
    | with_reducible exact .of_keeps handleApprovalExpire_kept
    | with_reducible exact .of_keeps handleGrantRevoke_kept
    | with_reducible exact .of_keeps handleDispatch_kept
    | with_reducible exact .of_keeps handleResult_kept
    | with_reducible exact .of_keeps handleOutcomeUnknown_kept
    | with_reducible exact .of_keeps handleReconcile_kept
    | with_reducible exact .of_keeps handleCancel_kept
    | with_reducible exact .of_keeps handleReset_kept
    | with_reducible exact .of_keeps handleKill_kept
    | with_reducible exact .of_keeps handlePermissionAdd_kept
    | with_reducible exact .of_keeps handleEscalationAck_kept
    | with_reducible exact .of_keeps handleLedgerSync_kept

/-- The consent an edit of `c` by `y` records: the current consent joined with the effective
consent of the edited arguments. -/
def edited (p : Policy) (c : CallRec) (y : Edit) : Consent :=
  c.consent.join (((p.action? c.tool).getD {}).effectiveConsent (y.newCost <|> c.cost) y.escalators)

theorem applyApprove_consent (h : applyApprove p s t k rc a pr dg cost ed = .ok r) :
    ∃ x, r.1 = { s with calls := s.calls.insert k x } ∧
      (ed = none → x.consent = rc.consent) ∧ ∀ y, ed = some y → x.consent = edited p rc y := by
  unfold applyApprove at h
  dsimp only at h
  iterate 5 (split at h; · cases h)
  cases ed with
  | none =>
    dsimp only at h
    split at h <;> cases h
    · exact ⟨_, rfl, (fun _ => rfl), fun _ hy => by cases hy⟩
    · exact ⟨_, rfl, (fun _ => rfl), fun _ hy => by cases hy⟩
  | some y =>
    dsimp only at h
    split at h
    · cases h
    rename_i rec' hn
    have hx : rec'.consent = edited p rc y := by
      revert hn
      repeat' split
      all_goals (intro hn; cases hn)
      rfl
    split at h <;> cases h
    · exact ⟨_, rfl, (fun hy => by cases hy), fun _ hy => by cases hy; exact hx⟩
    · exact ⟨_, rfl, (fun hy => by cases hy), fun _ hy => by cases hy; exact hx⟩

/-- What step `e` may do to a record that existed before it: keep it up to `RecSame`, or, on an
`approve` of an Awaiting call, change its consent only by an edit. -/
def Old (p : Policy) (s : State) (e : Event) (s' : State) : Prop :=
  ∀ (k : String) (c c' : CallRec), s.calls[k]? = some c → s'.calls[k]? = some c' →
    RecSame c c' ∨ c.status = .awaiting ∧ ∃ rid a dg cost ed,
      e.body = .approve k rid a dg cost ed ∧ (ed = none → c'.consent = c.consent) ∧
        ∀ y, ed = some y → c'.consent = edited p c y

theorem Old.of_keeps (h : Keeps s s') : Old p s e s' := fun k c c' hc hc' => by
  obtain ⟨c₀, h₀, hs⟩ := h.calls k c' hc'
  rw [hc] at h₀
  cases h₀
  exact .inl hs

theorem Old.of_calls (h : s'.calls = s.calls) : Old p s e s' := fun _ _ _ hc hc' => by
  rw [h, hc] at hc'
  cases hc'
  exact .inl .refl

theorem old_propose {tool dg : String} {cs : Option Cost} {gs xs : List (String × Bool)} :
    Old p s e (handlePropose p s e.time i tool dg cs gs xs).1 := by
  unfold handlePropose
  split
  · split <;> exact .of_calls rfl
  · rename_i hk
    split
    split
    · exact .of_calls rfl
    · intro k' c c' hc hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        rw [Std.ExtTreeMap.get?_eq_getElem?, hc] at hk
        cases hk
      · rw [hc] at hc'
        cases hc'
        exact .inl .refl

theorem old_approve (hb : e.body = .approve i rid a dg cost ed) :
    Old p s e (handleApprove p s e.time i rid a dg cost ed).1 := by
  unfold handleApprove
  split
  · exact .of_calls rfl
  · rename_i rc hck
    have hk := awaitingCheck_ok hck
    have hst := (awaitingCheck_facts hck).1
    dsimp only
    split
    · exact .of_calls rfl
    · rename_i r hr
      obtain ⟨x, hx, hn, hy⟩ := applyApprove_consent hr
      rw [hx]
      intro k' c c' hc hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        rw [hk] at hc
        cases hc
        cases hc'
        exact .inr ⟨hst, rid, a, dg, cost, ed, hb, hn, hy⟩
      · rw [hc] at hc'
        cases hc'
        exact .inl .refl

theorem old_stepHandle : Old p s e (stepHandle p s e).1 := by
  unfold Writ.stepHandle
  split <;> rename_i hb
  all_goals first
    | with_reducible exact .of_calls sessionStart_calls_eq
    | with_reducible exact .of_calls grantCreate_calls_eq
    | with_reducible exact old_approve hb
    | with_reducible exact old_propose
    | with_reducible exact .of_keeps handleSessionEnd_kept
    | with_reducible exact .of_keeps handleTurnStart_kept
    | with_reducible exact .of_keeps handleTurnEnd_kept
    | with_reducible exact .of_keeps handleStepStart_kept
    | with_reducible exact .of_keeps handleApproverAttest_kept
    | with_reducible exact .of_keeps handlePermissionRevoke_kept
    | with_reducible exact .of_keeps handleReject_kept
    | with_reducible exact .of_keeps handleApprovalExpire_kept
    | with_reducible exact .of_keeps handleGrantRevoke_kept
    | with_reducible exact .of_keeps handleDispatch_kept
    | with_reducible exact .of_keeps handleResult_kept
    | with_reducible exact .of_keeps handleOutcomeUnknown_kept
    | with_reducible exact .of_keeps handleReconcile_kept
    | with_reducible exact .of_keeps handleCancel_kept
    | with_reducible exact .of_keeps handleReset_kept
    | with_reducible exact .of_keeps handleKill_kept
    | with_reducible exact .of_keeps handlePermissionAdd_kept
    | with_reducible exact .of_keeps handleEscalationAck_kept
    | with_reducible exact .of_keeps handleLedgerSync_kept

theorem old_step : Old p s e (step p s e).1 := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact .of_calls rfl
  · rw [accepted_step ha]; exact old_stepHandle

end Approvals

open Approvals

theorem ApprovalInv.snoc (h : ApprovalInv p d es) : ApprovalInv p d (es ++ [e]) := by
  suffices hs : ∀ (k : String) (c' : CallRec), (step p (after p d es) e).1.calls[k]? = some c' →
      (∀ w ∈ c'.tally, ApprovedBy p d (es ++ [e]) k c' w) ∧
        c'.requestedAt ≤ (step p (after p d es) e).1.lastTime by
    refine ⟨fun k c hc => ?_, fun k c hc => ?_⟩ <;> simp only [after_snoc] at hc ⊢
    · exact (hs k c hc).1
    · exact (hs k c hc).2
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha]
    exact fun k c hc => ⟨fun w hw => (h.tally k c hc w hw).mono, h.requestedAt k c hc⟩
  · have hle := envelope_time (accepted_open ha)
    have hs := settled_stepHandle h ha
    rw [accepted_step ha]
    intro k c' hc'
    rcases hs k c' hc' with ⟨c, hc, hr⟩ | hn
    · refine ⟨fun w hw => ((h.tally k c hc w (hr.tally ▸ hw)).same hr).mono, ?_⟩
      have := h.requestedAt k c hc
      dsimp only
      rw [hr.requestedAt]
      omega
    · exact hn

theorem approvalInv (es : List Event) : ApprovalInv p d es :=
  snoc_induction ⟨fun k c hc => by simp [after_nil, State.initial] at hc,
      fun k c hc => by simp [after_nil, State.initial] at hc⟩ (fun _ _ ih => ih.snoc) es

theorem approvals (h : (step p (after p d es) e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : (after p d es).calls[k]? = some c) :
    dg = c.digest ∧ cost = c.cost ∧ ∀ w ∈ c.tally, ApprovedBy p d es k c w := by
  obtain ⟨-, c', hc', ⟨-, -, -, hdg, hcost, -⟩, -⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  exact ⟨hdg, hcost, (approvalInv es).tally k c hc⟩

namespace Approvals

theorem endCall_self (hk : s.calls[k]? = some c) :
    (s.endCall k st).calls[k]? = some { c with status := st } := by
  unfold State.endCall
  dsimp only
  rw [releaseGrant_calls, Std.ExtTreeMap.getElem?_modify_self, hk]
  rfl

theorem reject_rejected (ha : (step p s e).2.accepted = true) (hb : e.body = .reject k rid a) :
    ∃ c, (step p s e).1.calls[k]? = some c ∧ c.status = .rejected := by
  have hv := ha
  rw [accepted_step ha] at hv ⊢
  dsimp only at hv ⊢
  simp only [Writ.stepHandle, hb] at hv ⊢
  unfold handleReject at hv ⊢
  split at hv
  · cases hv
  · rename_i rc hck
    exact ⟨_, endCall_self (vetoCheck_ok hck).1, rfl⟩

theorem rejected_after {x : State × Event × Verdict} (hx : x ∈ trace p (State.initial d) es)
    (ha : x.2.2.accepted = true) (hb : x.2.1.body = .reject k rid a) :
    ∃ c, (after p d es).calls[k]? = some c ∧ c.status = .rejected := by
  refine snoc_induction (P := fun es => ∀ x ∈ trace p (State.initial d) es,
    x.2.2.accepted = true → x.2.1.body = .reject k rid a →
      ∃ c, (after p d es).calls[k]? = some c ∧ c.status = .rejected) ?_ ?_ es x hx ha hb
  · intro x hx; simp [trace] at hx
  · intro es e ih x hx ha hb
    rw [after_snoc]
    rcases trace_mem_snoc_iff.mp hx with hx | hx
    · obtain ⟨c, hc, hst⟩ := ih x hx ha hb
      obtain ⟨c', hc', -⟩ := calls_step_some (p := p) (e := e) hc
      exact ⟨c', hc', (calls_terminal hc (by rw [hst]; rfl) (by rw [hst]; nofun) hc').trans hst⟩
    · subst hx
      exact reject_rejected ha hb

end Approvals

theorem no_reject_before_claim (h : (step p (after p d es) e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) :
    ∀ x ∈ trace p (State.initial d) es,
      ¬ (x.2.2.accepted = true ∧ ∃ rid a, x.2.1.body = .reject k rid a) := by
  rintro x hx ⟨ha, rid, a, hb⟩
  obtain ⟨c, hc, hst⟩ := rejected_after hx ha hb
  obtain ⟨-, c', hc', ⟨hs, -⟩, -⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  rcases hs with hs | hs <;> rw [hst] at hs <;> cases hs

namespace Approvals

def editEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] consentApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "pay" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none (some { newDigest := "d2" })⟩ ]

def editDispatch : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d2" none [] "k1"⟩

def rejectEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] consentApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "pay" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .reject "c1" ⟨"s1", "c1", 0⟩ "a1"⟩ ]

def rejectDispatch : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

end Approvals

#guard (trace consentPolicy (State.initial "pd") (editEvents ++ [editDispatch])).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) none,
       .ok .authorized none, .ok .dispatchClaimed none ]
#guard (step consentPolicy (after consentPolicy "pd" editEvents) editDispatch).2.claimed
#guard ((after consentPolicy "pd" editEvents).calls["c1"]?).any fun c =>
  c.tally == [("alice", "a1")] && c.generation == 1 && c.digest == "d2" && c.cost.isNone &&
    c.requestedAt == 4
#guard ((after consentPolicy "pd" (editEvents.take 3)).calls["c1"]?).any fun c₀ =>
  c₀.tool == "pay" && c₀.generation == 0 && c₀.requestedAt == 3 && c₀.digest == "d1"
#guard editDispatch.body == .dispatch "c1" 1 "d2" none [] "k1"
#guard (step consentPolicy (after consentPolicy "pd" rejectEvents) rejectDispatch).2
  == .rejected .callEnded

end Writ.Proofs
