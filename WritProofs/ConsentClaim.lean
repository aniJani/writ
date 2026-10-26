import WritProofs.Approvals
import WritProofs.Grants
import WritProofs.Origin

namespace Writ.Proofs

open Writ
open Basic Proofs.Consent Approvals

/-- Section 6, Grants: the call's declared cost fits what is left of the grant's `max_cost`. -/
def GrantFitsCost (g : GrantRec) (cost : Option Cost) : Prop :=
  ∀ mc, g.maxCost = some mc → ∃ x, cost = some x ∧ x.currency = mc.currency ∧
    g.costConsumed + g.costReserved + x.amount ≤ mc.amount

/-- Section 8, theorem 1(b) at propose: call `k`, read against its record `c`, was created by an
accepted `propose` answered `allowed_by_grant gid`, and grant `gid` covered it then: tool and
digest, validity at the propose time, a use left, the cost within `max_cost`, and an approver
eligible for every clause of the call's consent. -/
def GrantAtPropose (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec)
    (gid : String) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ s₀.calls[k]? = none ∧
    (∃ gs₀ esc₀, e₀.body = .propose k c.tool c.digest c.cost gs₀ esc₀) ∧
    (∃ sh₀, v₀ = .ok (.allowedByGrant gid) sh₀) ∧
    ∃ g₀, s₀.grants[gid]? = some g₀ ∧ g₀.tool = c.tool ∧ g₀.digest.all (· == c.digest) ∧
      g₀.revoked = false ∧ g₀.epoch = s₀.epoch ∧ (∀ nb, g₀.notBefore = some nb → nb ≤ e₀.time) ∧
      (∀ x, g₀.expiresAt = some x → e₀.time < x) ∧
      (g₀.scope = .turn → s₀.turnActive = true ∧ g₀.turn = s₀.turnIndex) ∧
      g₀.consumed + g₀.reserved < g₀.maxUses ∧ GrantFitsCost g₀ c.cost ∧
      ∀ cl ∈ c.consent.clauses, EligibleFor p s₀ cl (g₀.principal, g₀.approver)

namespace ConsentClaim

variable {p : Policy} {d : String} {s s' : State} {e : Event} {es : List Event} {k gid : String}
  {c c' : CallRec}

theorem atPropose_mono (h : GrantAtPropose p d es k c gid) :
    GrantAtPropose p d (es ++ [e]) k c gid := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem atPropose_same (h : GrantAtPropose p d es k c gid) (hs : RecSame c c') :
    GrantAtPropose p d es k c' gid := by
  unfold GrantAtPropose
  rw [hs.tool, hs.digest, hs.cost, hs.consent]
  exact h

theorem coversCost_fits {g : GrantRec} {cost : Option Cost} (h : g.coversCost cost = true) :
    GrantFitsCost g cost := by
  intro mc hmc
  unfold GrantRec.coversCost at h
  rw [hmc] at h
  cases cost with
  | none => cases h
  | some x =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨x, rfl, h.1, h.2⟩

theorem findGrant_fits {tool dg : String} {cs : Consent} {cost : Option Cost} {t : Nat}
    (h : s.findGrant p tool dg cs cost t = some gid) :
    ∃ g, s.grants[gid]? = some g ∧ g.validAt s t = true ∧ g.tool = tool ∧
      g.digest.all (· == dg) = true ∧ g.consumed + g.reserved < g.maxUses ∧
      g.coversCost cost = true ∧ (s.eligibleAll p cs g.approver).isNone = true := by
  unfold State.findGrant at h
  obtain ⟨⟨gid', g⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_of_find?_eq_some hf)
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨g, hm, hp.1.1.1.1.1, hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

/-- What an accepted `e` may leave in a call record: one from before the step up to `RecSame`, or
one whose grant, if any, has its `allowed_by_grant` propose in the trace ending with `e`. -/
def Born (p : Policy) (d : String) (es : List Event) (e : Event) (s' : State) : Prop :=
  ∀ (k : String) (c' : CallRec), s'.calls[k]? = some c' →
    (∃ c, (after p d es).calls[k]? = some c ∧ RecSame c c') ∨
      ∀ gid, c'.grant = some gid → GrantAtPropose p d (es ++ [e]) k c' gid

theorem Born.of_keeps (h : Keeps (after p d es) s') : Born p d es e s' :=
  fun k c' hc => .inl (h.calls k c' hc)

theorem Born.of_calls (h : s'.calls = (after p d es).calls) : Born p d es e s' :=
  fun _ c' hc => .inl ⟨c', h ▸ hc, .refl⟩

theorem born_approve {i a dg : String} {rid : RequestId} {cost : Option Cost}
    {ed : Option Edit} :
    Born p d es e (handleApprove p (after p d es) e.time i rid a dg cost ed).1 := by
  have hi := consentInv_reachable (reachable_after (p := p) (d := d) (es := es))
  unfold handleApprove
  split
  · exact .of_calls rfl
  · rename_i rc hck
    have hk := awaitingCheck_ok hck
    have haw := hi.awaiting i rc hk (awaitingCheck_facts hck).1
    dsimp only
    split
    · exact .of_calls rfl
    · rename_i r hr
      obtain ⟨x, hx, -, hgrant, -⟩ := applyApprove_ok hr
      rw [hx]
      intro k' c' hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · cases hc'
        exact .inr fun gid hg => absurd (hgrant.symm.trans hg) (by rw [haw]; nofun)
      · exact .inl ⟨c', hc', .refl⟩

theorem born_propose {i tool dg : String} {cs : Option Cost} {gs xs : List (String × Bool)}
    (ha : (step p (after p d es) e).2.accepted = true)
    (hb : e.body = .propose i tool dg cs gs xs) :
    Born p d es e (handlePropose p (after p d es) e.time i tool dg cs gs xs).1 := by
  have hi := consentInv_reachable (reachable_after (p := p) (d := d) (es := es))
  have hv : (step p (after p d es) e).2 =
      (handlePropose p (after p d es) e.time i tool dg cs gs xs).2 := by
    rw [accepted_step ha]
    simp only [Writ.stepHandle, hb]
  revert hv
  unfold handlePropose
  split
  · intro _; split <;> exact .of_calls rfl
  · rename_i hk
    split
    rename_i dd cn hd
    split
    · intro _; exact .of_calls rfl
    · rename_i r hr
      dsimp only
      intro hv k' c' hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        cases hc'
        refine .inr fun gid hg => ?_
        dsimp only at hg
        have hdd := Grants.shadowed_grant hg
        subst hdd
        rw [Origin.byGrant_shadowed] at hv
        obtain ⟨-, habg⟩ := enforceDecision_facts hd
        obtain ⟨-, -, hfind, hne⟩ := habg gid rfl
        obtain ⟨g, hsg, hval, hgt, hgd, huse, hcov, hel⟩ := findGrant_fits hfind
        obtain ⟨hrev, hep, hnb, hex, hsc⟩ := Dispatch.validAt_iff.mp hval
        obtain ⟨info, hinfo, hp⟩ := hi.grants gid g hsg
        refine ⟨_, _, _, trace_mem_last, by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hk,
          ⟨gs, xs, hb⟩, ⟨none, hv⟩, ?_⟩
        refine ⟨g, hsg, hgt, hgd, hrev, hep, hnb, hex, hsc, huse, coversCost_fits hcov,
          fun cl hcl => ?_⟩
        have hel' := eligibleFor_sound (eligibleAll_sound hne hel cl hcl) hinfo
        rw [hp] at hel'
        exact hel'
      · exact .inl ⟨c', hc', .refl⟩

theorem born_stepHandle (ha : (step p (after p d es) e).2.accepted = true) :
    Born p d es e (stepHandle p (after p d es) e).1 := by
  unfold Writ.stepHandle
  split <;> rename_i hb
  all_goals first
    | with_reducible exact .of_calls sessionStart_calls_eq
    | with_reducible exact .of_calls grantCreate_calls_eq
    | with_reducible exact born_approve
    | with_reducible exact born_propose ha hb
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

/-- Every call holding a grant has its `allowed_by_grant` propose in the trace, read against the
call's current record: a grant call is never Awaiting, so no edit changes what was proposed. -/
theorem origin (es : List Event) : ∀ (k : String) (c : CallRec) (gid : String),
    (after p d es).calls[k]? = some c → c.grant = some gid → GrantAtPropose p d es k c gid := by
  refine snoc_induction (P := fun es => ∀ k c gid, (after p d es).calls[k]? = some c →
    c.grant = some gid → GrantAtPropose p d es k c gid)
    (fun k c gid hc => by simp [after_nil, State.initial] at hc) ?_ es
  intro es e ih k c' gid hc' hg
  rw [after_snoc] at hc'
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at hc'
    exact atPropose_mono (ih k c' gid hc' hg)
  · rw [accepted_step ha] at hc'
    rcases born_stepHandle ha k c' hc' with ⟨c, hc, hs⟩ | hn
    · exact atPropose_mono (atPropose_same (ih k c gid hc (hs.grant ▸ hg)) hs)
    · exact hn gid hg

end ConsentClaim

open ConsentClaim

variable {p : Policy} {d : String} {e : Event} {es : List Event} {k dg key : String} {n : Nat}
  {cost : Option Cost} {g : List (String × Bool)} {c : CallRec}

/-- Section 8, theorem 1: a claimed dispatch of an enforced call whose recorded consent is not
`none` dispatches the approved digest and cost, and either (a) holds no grant, its tally meets the
consent with approvals of the dispatched generation and no reject of the call was accepted, or
(b) holds a grant that covered it at propose, including `max_cost`, still covers it at dispatch,
and holds a reserved use of it (first attempt) or consumed one (retry), which the grant's counters
count. -/
theorem consent_claim (h : (step p (after p d es) e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : (after p d es).calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hne : c.consent.clauses ≠ []) :
    dg = c.digest ∧ cost = c.cost ∧
      ((c.grant = none ∧ ConsentMet p (after p d es) c.consent c.tally ∧
          (∀ w ∈ c.tally, ApprovedBy p d es k c w) ∧
          ∀ x ∈ trace p (State.initial d) es,
            ¬ (x.2.2.accepted = true ∧ ∃ rid a, x.2.1.body = .reject k rid a)) ∨
        ∃ gid, c.grant = some gid ∧ GrantCovers p (after p d es) e.time c ∧
          GrantAtPropose p d es k c gid ∧
          (c.attempts = 0 → k ∈ reservedCalls (after p d es) gid) ∧
          (1 ≤ c.attempts → k ∈ consumedCalls (after p d es) gid) ∧
          ∃ g, (after p d es).grants[gid]? = some g ∧
            g.reserved = (reservedCalls (after p d es) gid).length ∧
            g.consumed = (consumedCalls (after p d es) gid).length) := by
  obtain ⟨hdg, hcost, happ⟩ := approvals h he hc
  refine ⟨hdg, hcost, ?_⟩
  rcases consent reachable_after h he hc hm hne with ⟨hg, hmet⟩ | hcov
  · exact .inl ⟨hg, hmet, happ, no_reject_before_claim h he⟩
  · obtain ⟨gid, gr, hg, hgr, -⟩ := hcov.2.2
    have hinv := grantInv_reachable (reachable_after (p := p) (d := d) (es := es))
    refine .inr ⟨gid, hg, hcov, origin es k c gid hc hg, fun h0 => ?_, fun h1 =>
      Grants.mem_consumedCalls.mpr ⟨c, hc, hg, h1⟩,
      gr, hgr, hinv.reserved gid gr hgr, hinv.consumed gid gr hgr⟩
    obtain ⟨-, c', hc', ⟨hst, -⟩, -⟩ := (dispatch_claimed_iff he).mp h
    rw [hc] at hc'
    cases hc'
    have hok := (Grants.inv_reachable (reachable_after (p := p) (d := d) (es := es))).recs k c hc
    refine Grants.mem_reservedCalls.mpr ⟨c, hc, hg, hst.resolve_right fun hu => ?_, h0⟩
    have := hok.2.1 (.inr hu)
    omega

/-- Section 8, theorem 1(b), read from the `propose` event: call `k`, read against its record `c`,
was created by an accepted `propose` answered `allowed_by_grant gid` that carried the call's tool,
digest and cost. The effective consent of that event's escalators is the call's consent, a single
approval, and every escalator of the action that fired in the event (missing or true in its
`escalators`) is grantable. -/
def FiredAtPropose (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec)
    (gid : String) : Prop :=
  ∃ s₀ e₀ v₀ r gs₀ esc₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ s₀.calls[k]? = none ∧
    p.action? c.tool = some r ∧ e₀.body = .propose k c.tool c.digest c.cost gs₀ esc₀ ∧
    (∃ sh₀, v₀ = .ok (.allowedByGrant gid) sh₀) ∧
    c.consent = r.effectiveConsent c.cost esc₀ ∧ c.consent.single = true ∧
    ∀ n esc, (n, esc) ∈ r.escalate → esc₀.lookup n ≠ some false → esc.grantable = true

/-- Section 8, theorem 1(b) over the `propose` event: a claimed dispatch of an enforced call whose
recorded consent is not `none` and that holds grant `gid` was proposed with escalators under which
the consent is a single approval and every escalator that fired is grantable, and the propose was
answered `allowed_by_grant gid`. -/
theorem consent_claim_fired {gid : String} (h : (step p (after p d es) e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : (after p d es).calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hne : c.consent.clauses ≠ []) (hg : c.grant = some gid) :
    FiredAtPropose p d es k c gid := by
  rcases (consent_claim h he hc hm hne).2.2 with ⟨hn, -⟩ | ⟨gid', hg', hcov, -⟩
  · rw [hg] at hn; cases hn
  rw [hg] at hg'
  cases hg'
  obtain ⟨⟨s₀, e₀, v₀, r, gs₀, esc₀, hm₀, -, hn₀, hr, hb, hesc, hgr⟩, -, h0, hcur, -⟩ :=
    call_origin hc
  obtain ⟨⟨sh, hv⟩, hcons, hgen⟩ := hgr gid hg
  rw [hgen, h0] at hcur
  obtain ⟨hd, hcs⟩ := Prod.mk.inj (Option.some.inj hcur)
  rw [hd, hcs] at hb
  obtain ⟨hsingle, hfired, -⟩ := hcov
  refine ⟨s₀, e₀, v₀, r, gs₀, esc₀, hm₀, hn₀, hr, hb, ⟨sh, hv⟩, hcons, hsingle, ?_⟩
  intro n esc hmem hl
  refine hfired r hr n esc hmem ?_
  rw [hesc, lookup_filter (fun _ => List.any_eq_true.mpr ⟨(n, esc), hmem, beq_self_eq_true n⟩)]
  exact hl

namespace ConsentClaim

variable {s : State} {t : Nat} {tool : String} {gs es' : List (String × Bool)} {dd : Disposition}
  {cs : Consent} {r : Requirements}

/-- Where a record that did not exist before step `e` comes from: a `propose` of a defined
action. -/
def Fresh (p : Policy) (s : State) (e : Event) (s' : State) : Prop :=
  ∀ (k : String) (c' : CallRec), s.calls[k]? = none → s'.calls[k]? = some c' →
    ∃ t dg cost gs esc r, e.body = .propose k t dg cost gs esc ∧ p.action? t = some r

theorem Fresh.of_keeps {s' : State} (h : Keeps s s') : Fresh p s e s' := fun k c' hk hc' => by
  obtain ⟨c₀, h₀, -⟩ := h.calls k c' hc'
  rw [hk] at h₀
  cases h₀

theorem Fresh.of_calls {s' : State} (h : s'.calls = s.calls) : Fresh p s e s' :=
  fun _ _ hk hc' => by rw [h, hk] at hc'; cases hc'

theorem fresh_propose {i : String} {cs' : Option Cost} {xs : List (String × Bool)}
    (hb : e.body = .propose i tool dg cs' gs xs) :
    Fresh p s e (handlePropose p s e.time i tool dg cs' gs xs).1 := by
  unfold handlePropose
  split
  · split <;> exact .of_calls rfl
  · split
    split
    · exact .of_calls rfl
    · rename_i r' hr'
      intro k' c' hk hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        exact ⟨tool, dg, cs', gs, xs, r', hb, hr'⟩
      · rw [hk] at hc'
        cases hc'

theorem fresh_approve {i a : String} {rid : RequestId} {cs' : Option Cost} {ed : Option Edit} :
    Fresh p s e (handleApprove p s e.time i rid a dg cs' ed).1 := by
  unfold handleApprove
  split
  · exact .of_calls rfl
  · rename_i rc hck
    have hk := awaitingCheck_ok hck
    dsimp only
    split
    · exact .of_calls rfl
    · rename_i r hr
      obtain ⟨x, hx, -⟩ := applyApprove_consent hr
      rw [hx]
      intro k' c' hn hc'
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        rw [hk] at hn
        cases hn
      · rw [hn] at hc'
        cases hc'

theorem fresh_stepHandle : Fresh p s e (stepHandle p s e).1 := by
  unfold Writ.stepHandle
  split <;> rename_i hb
  all_goals first
    | with_reducible exact .of_calls sessionStart_calls_eq
    | with_reducible exact .of_calls grantCreate_calls_eq
    | with_reducible exact fresh_approve
    | with_reducible exact fresh_propose hb
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

theorem edit_post {a : String} {rid : RequestId} {cs' : Option Cost} {x : Edit} {c c' : CallRec}
    (hc : s.calls[k]? = some c)
    (ha : (handleApprove p s t k rid a dg cs' (some x)).2.accepted = true)
    (hc' : (handleApprove p s t k rid a dg cs' (some x)).1.calls[k]? = some c') :
    c'.consent = edited p c x := by
  revert ha hc'
  unfold handleApprove
  split
  · intro h; cases h
  · rename_i rc hck
    rw [awaitingCheck_ok hck] at hc
    cases hc
    dsimp only
    split
    · intro h; cases h
    · rename_i r hr
      obtain ⟨y, hy, -, hed⟩ := applyApprove_consent hr
      rw [hy]
      intro _ hc'
      rw [Std.ExtTreeMap.getElem?_insert_self] at hc'
      cases hc'
      exact hed x rfl

end ConsentClaim

variable {s : State} {t : String} {esc : List (String × Bool)} {r : Requirements} {c' : CallRec}

/-- Section 8, theorem 1, the recorded consent at propose: an accepted `propose` of a new call of
a defined action records the call, with the effective consent at propose (the action's consent
after `consent_if_cost_over` and the fired escalators) whenever the call is Authorized or Awaiting
and is enforced or carries no would-deny shadow. A denied record holds that consent or the
action's base consent. -/
theorem consent_recorded_propose (ha : (step p s e).2.accepted = true)
    (hb : e.body = .propose k t dg cost g esc) (hk : s.calls[k]? = none)
    (hr : p.action? t = some r) :
    ∃ c, (step p s e).1.calls[k]? = some c ∧ c.tool = t ∧
      (c.consent = r.effectiveConsent cost esc ∨ c.consent = r.consent) ∧
      ((p.modeOf t = .enforce ∨ ∀ x, c.shadow ≠ some (.wouldDeny x)) →
        c.status = .authorized ∨ c.status = .awaiting →
          c.consent = r.effectiveConsent cost esc) := by
  rw [accepted_step ha]
  simp only [stepHandle, hb]
  unfold handlePropose
  rw [Std.ExtTreeMap.get?_eq_getElem?, hk]
  dsimp only
  generalize hd : enforceDecision p s e.time k t dg cost g esc = dc
  obtain ⟨dd, cs⟩ := dc
  obtain ⟨h1, h2⟩ := Origin.enforceDecision_consent hd hr
  rw [hr]
  dsimp only
  refine ⟨_, Std.ExtTreeMap.getElem?_insert_self, rfl, h1, fun hsh hst => h2 fun x hx => ?_⟩
  subst hx
  revert hsh hst
  cases hm : p.modeOf t <;> simp only [Disposition.shadowed] <;> (try split) <;>
    simp [Disposition.status]

/-- Section 8, theorem 1: a record that did not exist before an event was created by a `propose`
of that call id for an action the policy defines, so `consent_recorded_propose` gives its
consent. -/
theorem recorded_by_propose (hk : s.calls[k]? = none) (hc : (step p s e).1.calls[k]? = some c) :
    ∃ t dg cost g esc r, e.body = .propose k t dg cost g esc ∧ p.action? t = some r := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha, hk] at hc; cases hc
  · rw [accepted_step ha] at hc
    exact fresh_stepHandle k c hk hc

/-- Section 8, theorem 1, the recorded consent after propose: an accepted `approve` with an edit
records the call's consent joined with the effective consent of the edited arguments (the new
cost, else the current one, and the host-recomputed escalators); every other step leaves a
recorded call's consent as it was. -/
theorem consent_recorded (ha : (step p s e).2.accepted = true) (hc : s.calls[k]? = some c)
    (hc' : (step p s e).1.calls[k]? = some c') :
    (∀ rid a dg cost x, e.body = .approve k rid a dg cost (some x) →
      c'.consent = c.consent.join
        (((p.action? c.tool).getD {}).effectiveConsent (x.newCost <|> c.cost) x.escalators)) ∧
    ((∀ rid a dg cost x, e.body ≠ .approve k rid a dg cost (some x)) →
      c'.consent = c.consent) := by
  refine ⟨fun rid a dg cost x hb => ?_, fun hne => ?_⟩
  · have ha' : (stepHandle p s e).2.accepted = true := by
      have h' := ha; rw [accepted_step ha] at h'; exact h'
    rw [accepted_step ha] at hc'
    simp only [stepHandle, hb] at ha' hc'
    exact edit_post hc ha' hc'
  · rcases old_step k c c' hc hc' with hs | ⟨-, rid, a, dg, cost, ed, hb, hn, -⟩
    · exact hs.consent
    · cases ed with
      | none => exact hn rfl
      | some x => exact absurd hb (hne rid a dg cost x)

namespace ConsentClaim

/-- `GrantAtPropose` as a check, with the kernel's own validity and cost tests. -/
def proposedBy (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec)
    (gid : String) : Bool :=
  (trace p (State.initial d) es).any fun (s₀, e₀, v₀) =>
    s₀.calls[k]?.isNone &&
      (match e₀.body with
        | .propose k' tool dg cost _ _ =>
          k' == k && tool == c.tool && dg == c.digest && cost == c.cost
        | _ => false) &&
      v₀ == .ok (.allowedByGrant gid) none &&
      (s₀.grants[gid]?).any fun g₀ =>
        g₀.tool == c.tool && g₀.digest.all (· == c.digest) && g₀.validAt s₀ e₀.time &&
          g₀.consumed + g₀.reserved < g₀.maxUses && g₀.coversCost c.cost &&
          c.consent.clauses.all fun cl => s₀.eligibleFor p cl g₀.approver

def rejectedIn (p : Policy) (d : String) (es : List Event) (k : String) : Bool :=
  (trace p (State.initial d) es).any fun x =>
    x.2.2.accepted && match x.2.1.body with
      | .reject k' .. => k' == k
      | _ => false

open Grants (costPolicy costEvents usd retryGrantPolicy retryGrantOpen retryGrantEvent)

/-- The grant's `max_cost` is 10 and `c1` already holds 6 of it, so `c3`'s 4 fits exactly. -/
def costDispatch : Event := ⟨8, 8, 7, none, .dispatch "c3" 1 "d1" (usd 4) [] "k3"⟩

#guard (step consentPolicy (after consentPolicy "pd" consentEvents) consentDispatch).2.claimed &&
  ((after consentPolicy "pd" consentEvents).calls["c1"]?).any fun c =>
    consentPolicy.modeOf c.tool == .enforce && !c.consent.clauses.isEmpty && c.grant.isNone &&
      c.digest == "d1" && c.cost.isNone && c.tally == [("alice", "a1")] &&
      (after consentPolicy "pd" consentEvents).satisfied consentPolicy c.consent c.tally &&
      !rejectedIn consentPolicy "pd" consentEvents "c1"

#guard (step costPolicy (after costPolicy "pd" costEvents) costDispatch).2.claimed &&
  ((after costPolicy "pd" costEvents).calls["c3"]?).any fun c =>
    costPolicy.modeOf c.tool == .enforce && !c.consent.clauses.isEmpty &&
      c.grant == some "g1" && c.digest == "d1" && c.cost == usd 4 && c.attempts == 0 &&
      proposedBy costPolicy "pd" costEvents "c3" c "g1" &&
      (reservedCalls (after costPolicy "pd" costEvents) "g1").contains "c3" &&
      ((after costPolicy "pd" costEvents).grants["g1"]?).any (fun g =>
        g.reserved == (reservedCalls (after costPolicy "pd" costEvents) "g1").length &&
          g.consumed == (consumedCalls (after costPolicy "pd" costEvents) "g1").length) &&
      ((after costPolicy "pd" (costEvents.take 5)).grants["g1"]?).any fun g₀ =>
        g₀.maxCost == usd 10 && g₀.costReserved == 6

#guard (step retryGrantPolicy (after retryGrantPolicy "pd" retryGrantOpen)
    retryGrantEvent).2.claimed &&
  ((after retryGrantPolicy "pd" retryGrantOpen).calls["c1"]?).any fun c =>
    retryGrantPolicy.modeOf c.tool == .enforce && !c.consent.clauses.isEmpty &&
      c.grant == some "g1" && c.digest == "d1" && c.cost.isNone && c.attempts == 1 &&
      c.status == .unknown &&
      proposedBy retryGrantPolicy "pd" retryGrantOpen "c1" c "g1" &&
      (consumedCalls (after retryGrantPolicy "pd" retryGrantOpen) "g1").contains "c1" &&
      ((after retryGrantPolicy "pd" retryGrantOpen).grants["g1"]?).any fun g =>
        g.reserved == (reservedCalls (after retryGrantPolicy "pd" retryGrantOpen) "g1").length &&
          g.consumed == (consumedCalls (after retryGrantPolicy "pd" retryGrantOpen) "g1").length

/-- `FiredAtPropose` as a check. -/
def firedAt (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec) (gid : String) :
    Bool :=
  (trace p (State.initial d) es).any fun (s₀, e₀, v₀) =>
    s₀.calls[k]?.isNone && v₀ == .ok (.allowedByGrant gid) none &&
      (p.action? c.tool).any fun r =>
        match e₀.body with
        | .propose k' tool dg cost _ esc₀ =>
          k' == k && tool == c.tool && dg == c.digest && cost == c.cost &&
            c.consent == r.effectiveConsent c.cost esc₀ && c.consent.single &&
            r.escalate.all fun (n, esc) => esc₀.lookup n == some false || esc.grantable
        | _ => false

/-- Section 5's example: `not_allowlisted` is grantable and `dangerous` is not. -/
def shellPolicy : Policy :=
  { approverRoles := ["owner"]
    actions :=
      [("shell.run", { escalate := [("not_allowlisted", { consent := .perCall, grantable := true }),
                                    ("dangerous", { consent := .perCall })]
                       grantable := some { scope := .session, maxUses := 5, anyArgs := true
                                           maxDurationMs := some 1000 } })] }

/-- `c1` reports `dangerous` false and is covered by the any-arguments grant `g1`; `c2` leaves
`dangerous` out, so it fires and `c2` needs an approval although `g1` has uses left. -/
def shellEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [("a1", ⟨"alice", .human, ["owner"]⟩)] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .grantCreate "g1" "a1" "shell.run" none .session 5 none none (some 1000)
      "rs"⟩
  , ⟨4, 4, 3, none, .propose "c1" "shell.run" "ls" none []
      [("not_allowlisted", true), ("dangerous", false)]⟩
  , ⟨5, 5, 4, none, .propose "c2" "shell.run" "rm" none [] [("not_allowlisted", true)]⟩ ]

def shellDispatch : Event := ⟨6, 6, 5, none, .dispatch "c1" 1 "ls" none [] "k1"⟩

#guard decide shellPolicy.WF
#guard (trace shellPolicy (State.initial "pd") shellEvents).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .none none, .ok (.allowedByGrant "g1") none,
       .ok (.needsApproval ⟨"s1", "c2", 0⟩) none ]
#guard (step shellPolicy (after shellPolicy "pd" shellEvents) shellDispatch).2.claimed &&
  ((after shellPolicy "pd" shellEvents).calls["c1"]?).any fun c =>
    shellPolicy.modeOf c.tool == .enforce && !c.consent.clauses.isEmpty &&
      c.grant == some "g1" && firedAt shellPolicy "pd" shellEvents "c1" c "g1" &&
      c.proposedEscalators == [("not_allowlisted", true), ("dangerous", false)]
#guard ((after shellPolicy "pd" shellEvents).calls["c2"]?).any fun c =>
  c.grant.isNone && c.status == .awaiting
#guard (step costPolicy (after costPolicy "pd" costEvents) costDispatch).2.claimed &&
  ((after costPolicy "pd" costEvents).calls["c3"]?).any fun c =>
    c.grant == some "g1" && firedAt costPolicy "pd" costEvents "c3" c "g1"

/-- `free` needs consent only through its escalator `ext`; `pay`'s escalator `big` raises its
quorum to two. -/
def recPolicy : Policy :=
  { approverRoles := ["owner"]
    actions :=
      [ ("pay", { consent := .perCall
                  escalate := [("big", { consent := .quorum 2 none true false })] })
      , ("free", { escalate := [("ext", { consent := .perCall })], guards := ["ok"] }) ] }

def recEdit : Edit := { newDigest := "d4" }

/-- `c2` misses its guard; the edit of `c3` sends no escalators, so `big` fires. -/
def recEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] Consent.consentApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "free" "d1" none [("ok", true)] [("ext", true)]⟩
  , ⟨4, 4, 3, none, .propose "c2" "free" "d2" none [] [("ext", true)]⟩
  , ⟨5, 5, 4, none, .propose "c3" "pay" "d3" none [] [("big", false)]⟩
  , ⟨6, 6, 5, none, .approve "c3" ⟨"s1", "c3", 0⟩ "a1" "d3" none (some recEdit)⟩ ]

def recAt (n : Nat) : State := after recPolicy "pd" (recEvents.take n)

def freeReq : Requirements := (recPolicy.action? "free").getD {}

#guard (trace recPolicy (State.initial "pd") recEvents).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) none,
       .ok (.denied .guardFalse) none, .ok (.needsApproval ⟨"s1", "c3", 0⟩) none,
       .ok .pending none ]
#guard (recAt 2).calls["c1"]?.isNone && recPolicy.modeOf "free" == .enforce
#guard ((recAt 3).calls["c1"]?).any fun c =>
  c.tool == "free" && c.status == .awaiting &&
    c.consent == freeReq.effectiveConsent none [("ext", true)] && c.consent != freeReq.consent
#guard ((recAt 4).calls["c2"]?).any fun c =>
  c.status == .denied .guardFalse && c.consent == freeReq.consent &&
    c.consent != freeReq.effectiveConsent none [("ext", true)]
#guard ((recAt 5).calls["c3"]?).any fun c =>
  ((recAt 6).calls["c3"]?).any fun c' =>
    c'.consent == c.consent.join (((recPolicy.action? c.tool).getD {}).effectiveConsent
      (recEdit.newCost <|> c.cost) recEdit.escalators) && c'.consent != c.consent &&
      c'.generation == 1
#guard ((recAt 3).calls["c1"]?).any fun c => ((recAt 6).calls["c1"]?).any (·.consent == c.consent)

end ConsentClaim

end Writ.Proofs
