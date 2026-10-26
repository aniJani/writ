import WritProofs.Accept
import WritProofs.Lifecycle
import WritProofs.Accounting
import WritProofs.DefaultDeny

namespace Writ.Proofs

open Writ
open Basic Proofs.Consent Approvals

variable {p : Policy} {d : String} {s s' : State} {e : Event} {es : List Event}
  {k : String} {c : CallRec}

/-- Section 8, origin independence: verdicts and state do not depend on `origin`. -/
theorem origin_independent {o : Option String} : step p s { e with origin := o } = step p s e :=
  rfl

/-- Section 8, monotone time and seq: an accepted event has a later `seq` and no earlier `time`
than the state, and the state records both. -/
theorem accepted_seq_time (h : (step p s e).2.accepted = true) :
    s.lastSeq < e.seq ∧ s.lastTime ≤ e.time ∧ (step p s e).1.lastSeq = e.seq ∧
      (step p s e).1.lastTime = e.time := by
  have hn := envelope_iff.mp (accepted_open h)
  rw [accepted_step h]
  exact ⟨hn.2.2.2.1, hn.2.2.2.2.1, rfl, rfl⟩

namespace Support

theorem step_mono : s.lastSeq ≤ (step p s e).1.lastSeq ∧ s.lastTime ≤ (step p s e).1.lastTime := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := accepted_seq_time ha
    rw [h₃, h₄]
    exact ⟨Nat.le_of_lt h₁, h₂⟩

theorem trace_after : ∀ x ∈ trace p s es, x.2.2.accepted = true →
    s.lastSeq < x.2.1.seq ∧ s.lastTime ≤ x.2.1.time := by
  induction es generalizing s with
  | nil => intro x hx; cases hx
  | cons e es ih =>
    intro x hx hacc
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨h₁, h₂, -⟩ := accepted_seq_time hacc
      exact ⟨h₁, h₂⟩
    · obtain ⟨h₁, h₂⟩ := ih x hx hacc
      obtain ⟨m₁, m₂⟩ := step_mono (p := p) (s := s) (e := e)
      exact ⟨Nat.lt_of_le_of_lt m₁ h₁, Nat.le_trans m₂ h₂⟩

end Support

/-- Section 8, monotone time and seq: along any trace the accepted events have strictly
increasing `seq` and nondecreasing `time`. -/
theorem trace_seq_time : ((trace p s es).filter (·.2.2.accepted)).Pairwise
    fun x y => x.2.1.seq < y.2.1.seq ∧ x.2.1.time ≤ y.2.1.time := by
  induction es generalizing s with
  | nil => exact .nil
  | cons e es ih =>
    simp only [trace, List.filter_cons]
    split
    · rename_i hacc
      refine List.Pairwise.cons (fun y hy => ?_) ih
      obtain ⟨-, -, h₃, h₄⟩ := accepted_seq_time hacc
      obtain ⟨hy, hya⟩ := List.mem_filter.mp hy
      have := Support.trace_after y hy hya
      rw [h₃, h₄] at this
      exact this
    · exact ih

/-- Section 8's well-formedness invariant `Inv`: no calls before `session_start`, call epochs
bounded by the session's, duplicate-free tallies, each status consistent with the call's grant,
attempts and authorization time, and reservations and grant counters matching the calls. -/
structure WellFormed (p : Policy) (s : State) : Prop where
  fresh : s.started = false → ∀ k : String, s.calls[k]? = none
  epoch : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → c.epoch ≤ s.epoch
  tally : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → (c.tally.map (·.1)).Nodup
  awaiting : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → c.status = .awaiting →
    c.grant = none ∧ c.attempts = 0
  authorized : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → c.status = .authorized →
    c.attempts = 0 ∧ c.authorizedAt.isSome
  dispatched : ∀ (k : String) (c : CallRec), s.calls[k]? = some c →
    (c.status = .dispatched ∨ c.status = .unknown) →
    ∃ r, p.action? c.tool = some r ∧ 1 ≤ c.attempts ∧ c.attempts ≤ r.maxAttempts ∧
      c.authorizedAt.isSome
  accounting : Accounting p s
  grants : GrantInv s

namespace Support

def TallyNodup (m : CallMap) : Prop :=
  ∀ (k : String) (c : CallRec), m[k]? = some c → (c.tally.map (·.1)).Nodup

theorem TallyNodup.insert {m : CallMap} (h : TallyNodup m) (hc : (c.tally.map (·.1)).Nodup) :
    TallyNodup (m.insert k c) := by
  intro k' c' hk'
  rw [Std.ExtTreeMap.getElem?_insert] at hk'
  split at hk'
  · cases hk'; exact hc
  · exact h _ _ hk'

theorem TallyNodup.keeps (h : TallyNodup s.calls) (hk : Keeps s s') : TallyNodup s'.calls :=
  fun k c' hc' => by
    obtain ⟨c, hc, hr⟩ := hk.calls k c' hc'
    rw [hr.tally]
    exact h k c hc

theorem sessionStart_calls {i pd rq : String} {ps : List String}
    {as : List (String × ApproverInfo)} {l : Ledger} :
    (handleSessionStart s i pd rq ps as l).1.calls = s.calls := by
  unfold handleSessionStart; repeat' split
  all_goals rfl

theorem grantCreate_calls {t : Nat} {gid a tool : String} {dg : Option String} {sc : GrantScope}
    {n : Nat} {mc : Option Cost} {nb ex : Option Nat} {rsd : String} :
    (handleGrantCreate p s t gid a tool dg sc n mc nb ex rsd).1.calls = s.calls := by
  unfold handleGrantCreate; repeat' split
  all_goals rfl

theorem propose_tally {t : Nat} {tool dg : String} {cs : Option Cost}
    {g x : List (String × Bool)} (h : TallyNodup s.calls) :
    TallyNodup (handlePropose p s t k tool dg cs g x).1.calls := by
  unfold handlePropose
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact h
    | exact h.insert List.nodup_nil

theorem approve_tally {t : Nat} {a rd : String} {rid : RequestId} {rc : Option Cost}
    {ed : Option Edit} (h : TallyNodup s.calls) :
    TallyNodup (handleApprove p s t k rid a rd rc ed).1.calls := by
  unfold handleApprove
  split
  · exact h
  · rename_i c hc
    have hk := awaitingCheck_ok hc
    dsimp only
    split
    · exact h
    · rename_i v hv
      obtain ⟨x, hx, -, -, -, -, hor⟩ := applyApprove_spec hv
      obtain ⟨-, -, -, -, -, hne, -⟩ := Accept.apply_ok.mp ⟨v, hv⟩
      rw [hx]
      refine h.insert ?_
      rcases hor with ⟨he, ht, -⟩ | ⟨_, -, ht, -⟩
      · rw [ht, List.map_append, List.nodup_append]
        refine ⟨h k c hk, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro y hy z hz
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
        rw [hz]
        exact hne he w hw
      · rw [ht]
        exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem stepHandle_tally (h : TallyNodup s.calls) : TallyNodup (stepHandle p s e).1.calls := by
  unfold Writ.stepHandle
  split
  all_goals first
    | (rw [sessionStart_calls]; exact h)
    | (rw [grantCreate_calls]; exact h)
    | with_reducible exact propose_tally h
    | with_reducible exact approve_tally h
    | with_reducible exact h.keeps handleSessionEnd_kept
    | with_reducible exact h.keeps handleTurnStart_kept
    | with_reducible exact h.keeps handleTurnEnd_kept
    | with_reducible exact h.keeps handleStepStart_kept
    | with_reducible exact h.keeps handleApproverAttest_kept
    | with_reducible exact h.keeps handlePermissionRevoke_kept
    | with_reducible exact h.keeps handleReject_kept
    | with_reducible exact h.keeps handleApprovalExpire_kept
    | with_reducible exact h.keeps handleGrantRevoke_kept
    | with_reducible exact h.keeps handleDispatch_kept
    | with_reducible exact h.keeps handleResult_kept
    | with_reducible exact h.keeps handleOutcomeUnknown_kept
    | with_reducible exact h.keeps handleReconcile_kept
    | with_reducible exact h.keeps handleCancel_kept
    | with_reducible exact h.keeps handleReset_kept
    | with_reducible exact h.keeps handleKill_kept
    | with_reducible exact h.keeps handlePermissionAdd_kept
    | with_reducible exact h.keeps handleEscalationAck_kept
    | with_reducible exact h.keeps handleLedgerSync_kept

theorem tally_reachable (hr : Reachable p d s) : TallyNodup s.calls := by
  induction hr with
  | init => intro k c hk; simp [State.initial] at hk
  | @step s e _ ih =>
    cases ha : (step p s e).2.accepted
    · rw [frame ha]; exact ih
    · rw [accepted_step ha]
      exact stepHandle_tally ih

end Support

/-- Section 8's well-formedness invariant holds in every reachable state of a checked policy. -/
theorem wellFormed_reachable (hwf : p.WF) : Reachable p d s → WellFormed p s := by
  intro hr
  have hg := Grants.inv_reachable hr
  have hl := Lifecycle.Inv.reachable hr
  have hdeny := denyInv_reachable hr
  obtain ⟨es, rfl⟩ := reachable_iff.mp hr
  have hrec : ∀ k c, (after p d es).calls[k]? = some c →
      AtMostOnce.RecInv p k (after p d es) (trace p (State.initial d) es) c :=
    fun k c hc => (traceInv p d k es).present c hc
  refine
    { fresh := fun hs => ((consentInv_reachable hr).fresh hs).2.1
      epoch := fun k c hc => (hrec k c hc).epoch
      tally := Support.tally_reachable hr
      awaiting := fun k c hc hs => ⟨(hg.recs k c hc).2.2 hs, (hg.recs k c hc).1 (.inl hs)⟩
      authorized := fun k c hc hs =>
        ⟨(hg.recs k c hc).1 (.inr hs), hl.auth k c hc (.inl hs)⟩
      dispatched := fun k c hc hs => ?_
      accounting := accounting_reachable hwf hr
      grants := grantInv_reachable hr }
  obtain ⟨r, hr', -⟩ := hdeny.defined k c hc
  have hcap := (hrec k c hc).cap
  rw [AtMostOnce.rules, hr', Option.getD_some,
    Nat.max_eq_right (hwf.facts.maxAttempts_pos hr')] at hcap
  exact ⟨r, hr', (hg.recs k c hc).2.1 hs, hcap, hl.auth k c hc (.inr hs)⟩

namespace Support

open Accept

/-- From `Accept.base`: `c1` is approved, `c6` collects two principals' approvals and `c7` is
allowed by a grant, so every status `WellFormed` constrains is held by some call. -/
def wfEvents : List Event :=
  base ++
  [ ev 12 (.approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none none)
  , ev 13 (.approverAttest "a2" ⟨"bob", .human, ["owner"]⟩)
  , ev 14 (.propose "c6" "q" "d6" none [] [])
  , ev 15 (.approve "c6" ⟨"s1", "c6", 0⟩ "a1" "d6" none none)
  , ev 16 (.approve "c6" ⟨"s1", "c6", 0⟩ "a2" "d6" none none)
  , ev 17 (.grantCreate "g1" "a1" "t" (some "d7") .session 2 none none (some 60) "rs")
  , ev 18 (.propose "c7" "t" "d7" none [] []) ]

def sW : State := after aPolicy "pd" wfEvents

def callsOk (q : Policy) (s : State) : Bool :=
  s.calls.toList.all fun (_, c) =>
    c.epoch ≤ s.epoch && (c.tally.map (·.1)).eraseDups.length == c.tally.length &&
    (c.status != .awaiting || (c.grant.isNone && c.attempts == 0)) &&
    (c.status != .authorized || (c.attempts == 0 && c.authorizedAt.isSome)) &&
    (!(c.status == .dispatched || c.status == .unknown) ||
      (q.action? c.tool).any fun r =>
        1 ≤ c.attempts && c.attempts ≤ r.maxAttempts && c.authorizedAt.isSome)

#guard decide aPolicy.WF
#guard (trace aPolicy (State.initial "pd") wfEvents).all (·.2.2.accepted)
#guard callsOk aPolicy sW
#guard [CallStatus.awaiting, .authorized, .dispatched, .unknown].all fun st =>
  sW.calls.toList.any (·.2.status == st)
#guard (sW.calls["c6"]?).any fun c => c.status == .authorized && c.tally.length == 2
#guard (sW.calls["c7"]?).any fun c => c.status == .authorized && c.grant == some "g1"
#guard (sW.calls["c3"]?).any fun c => c.status == .unknown && c.attempts == 1
#guard !callsOk aPolicy { sW with
  calls := sW.calls.modify "c6" fun c => { c with tally := c.tally ++ c.tally } }
#guard !callsOk aPolicy { sW with
  calls := sW.calls.modify "c2" fun c => { c with attempts := 2 } }

def seqEvents : List Event :=
  witnessEvents ++
  [ staleEvent, ⟨6, 3, 4, none, .turnEnd⟩, ⟨7, 6, 4, none, .turnEnd⟩
  , ⟨8, 6, 5, none, .turnStart false⟩ ]

#guard (trace witnessPolicy (State.initial "pd") seqEvents).map (·.2.2.accepted) ==
  [true, true, true, true, false, false, true, true]
#guard decide (((trace witnessPolicy (State.initial "pd") seqEvents).filter
  (·.2.2.accepted)).Pairwise fun x y => x.2.1.seq < y.2.1.seq ∧ x.2.1.time ≤ y.2.1.time)
#guard (step witnessPolicy (after witnessPolicy "pd" (seqEvents.take 7)) ⟨8, 6, 5, none,
  .turnStart false⟩).1.lastSeq == 8

def proposeEvent : Event := ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩

#guard (step witnessPolicy (after witnessPolicy "pd" (witnessEvents.take 2))
  { proposeEvent with origin := some "tool_output" }) ==
  step witnessPolicy (after witnessPolicy "pd" (witnessEvents.take 2)) proposeEvent

end Support

end Writ.Proofs
