import WritProofs.Origin
import WritProofs.Permission

namespace Writ.Proofs

open Writ
open Basic

/-- Section 8, theorems 1, 3 and 11: approver `a` with principal, kind and roles `info` was
attested by an accepted event of the trace: a `session_start` whose approvers list holds
`(a, info)`, or an `approver_attest` of `a` carrying `info`. -/
def ApproverOrigin (p : Policy) (d : String) (es : List Event) (a : String)
    (info : ApproverInfo) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    ((∃ i pd req perms as l, e₀.body = .sessionStart i pd req perms as l ∧ (a, info) ∈ as) ∨
      e₀.body = .approverAttest a info)

/-- Section 8, theorem 1: `r` is the requester of an accepted `session_start` of the trace, and
every accepted `session_start` of the trace carries `r`. -/
def RequesterOrigin (p : Policy) (d : String) (es : List Event) (r : String) : Prop :=
  (∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    ∃ i pd perms as l, e₀.body = .sessionStart i pd r perms as l) ∧
  ∀ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es → v₀.accepted = true →
    ∀ i pd r' perms as l, e₀.body = .sessionStart i pd r' perms as l → r' = r

namespace Approvers

open Permission

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event} {a : String}
  {info : ApproverInfo}

theorem insertMany_src {m : Std.ExtTreeMap String ApproverInfo compare}
    {l : List (String × ApproverInfo)} (h : (m.insertMany l)[a]? = some info) :
    m[a]? = some info ∨ (a, info) ∈ l := by
  induction l generalizing m with
  | nil => exact .inl h
  | cons x l ih =>
    obtain ⟨b, v⟩ := x
    rw [Std.ExtTreeMap.insertMany_cons] at h
    rcases ih h with h' | h'
    · clear h
      rw [Std.ExtTreeMap.getElem?_insert] at h'
      split at h'
      · rename_i he
        cases Std.LawfulEqCmp.eq_of_compare he
        cases h'
        exact .inr (by simp)
      · exact .inl h'
    · exact .inr (List.mem_cons_of_mem _ h')

/-- What an accepted handler leaves in the approver map: the entries from before it, the entries
of its `session_start`, or the entry its `approver_attest` carried. -/
theorem stepHandle_approvers :
    (stepHandle p s e).2.accepted = true → (stepHandle p s e).1.approvers[a]? = some info →
      s.approvers[a]? = some info ∨
        (∃ i pd req perms as l, e.body = .sessionStart i pd req perms as l ∧ (a, info) ∈ as) ∨
        e.body = .approverAttest a info := by
  unfold stepHandle
  split <;> rename_i hb
  all_goals first
    | with_reducible exact fun _ h => .inl (handleSessionEnd_parties.src h)
    | with_reducible exact fun _ h => .inl (handleTurnStart_parties.src h)
    | with_reducible exact fun _ h => .inl (handleTurnEnd_parties.src h)
    | with_reducible exact fun _ h => .inl (handleStepStart_parties.src h)
    | with_reducible exact fun _ h => .inl (handlePropose_parties.src h)
    | with_reducible exact fun _ h => .inl (handleApprove_parties.src h)
    | with_reducible exact fun _ h => .inl (handleReject_parties.src h)
    | with_reducible exact fun _ h => .inl (handleApprovalExpire_parties.src h)
    | with_reducible exact fun _ h => .inl (handleGrantCreate_parties.src h)
    | with_reducible exact fun _ h => .inl (handleGrantRevoke_parties.src h)
    | with_reducible exact fun _ h => .inl (handleDispatch_parties.src h)
    | with_reducible exact fun _ h => .inl (handleResult_parties.src h)
    | with_reducible exact fun _ h => .inl (handleOutcomeUnknown_parties.src h)
    | with_reducible exact fun _ h => .inl (handleReconcile_parties.src h)
    | with_reducible exact fun _ h => .inl (handleCancel_parties.src h)
    | with_reducible exact fun _ h => .inl (handleReset_parties.src h)
    | with_reducible exact fun _ h => .inl (handleKill_parties.src h)
    | with_reducible exact fun _ h => .inl (handleEscalationAck_parties.src h)
    | with_reducible exact fun _ h => .inl (handleLedgerSync_parties.src h)
    | skip
  · unfold handleSessionStart
    split
    · intro ha; cases ha
    split
    · intro ha; cases ha
    intro _ h
    rcases insertMany_src h with h | h
    · exact .inl h
    · exact .inr (.inl ⟨_, _, _, _, _, _, hb, h⟩)
  · unfold handleApproverAttest
    split
    · intro ha; cases ha
    intro _ h
    dsimp only at h
    rw [Std.ExtTreeMap.getElem?_insert] at h
    split at h
    · rename_i he
      cases Std.LawfulEqCmp.eq_of_compare he
      cases h
      exact .inr (.inr hb)
    · exact .inl h
  · exact fun _ h => .inl h
  · unfold handlePermissionAdd
    repeat' split
    all_goals exact fun _ h => .inl h

/-- What an accepted handler does to the requester and `started`: a `session_start` sets the
requester it carries and starts the session; every other event leaves both. -/
theorem stepHandle_requester (ha : (stepHandle p s e).2.accepted = true) :
    (e.body.isStart = false ∧ (stepHandle p s e).1.requester = s.requester ∧
        (stepHandle p s e).1.started = s.started) ∨
      ∃ i pd perms as l, e.body = .sessionStart i pd (stepHandle p s e).1.requester perms as l ∧
        (stepHandle p s e).1.started = true := by
  revert ha
  unfold stepHandle
  split <;> rename_i hb
  all_goals first
    | ((with_reducible refine fun _ => .inl (handleSessionEnd_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleTurnStart_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleTurnEnd_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleStepStart_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handlePropose_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleApprove_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleReject_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleApprovalExpire_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleGrantCreate_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleGrantRevoke_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleDispatch_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleResult_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleOutcomeUnknown_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleReconcile_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleCancel_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleReset_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleKill_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleEscalationAck_parties.req ?_)); rw [hb]; rfl)
    | ((with_reducible refine fun _ => .inl (handleLedgerSync_parties.req ?_)); rw [hb]; rfl)
    | skip
  · unfold handleSessionStart
    split
    · intro ha; cases ha
    split
    · intro ha; cases ha
    intro _
    exact .inr ⟨_, _, _, _, _, hb, rfl⟩
  · intro _
    refine .inl ⟨by rw [hb]; rfl, ?_, ?_⟩ <;> (unfold handleApproverAttest; split <;> rfl)
  · exact fun _ => .inl ⟨by rw [hb]; rfl, rfl, rfl⟩
  · intro _
    refine .inl ⟨by rw [hb]; rfl, ?_, ?_⟩ <;> (unfold handlePermissionAdd; repeat' split) <;> rfl

theorem origin_mono (h : ApproverOrigin p d es a info) : ApproverOrigin p d (es ++ [e]) a info := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

end Approvers

open Approvers

variable {p : Policy} {d : String} {es : List Event} {a : String} {info : ApproverInfo}

/-- Section 8, theorems 1, 3 and 11: every attested approver came from the trace's events: its
principal, kind and roles are those an accepted `session_start` listed for it or an accepted
`approver_attest` of it carried. With `consentInv_reachable` (field `approvers`), no later step
removes or changes the entry. -/
theorem approver_origin (h : (after p d es).approvers[a]? = some info) :
    ApproverOrigin p d es a info := by
  refine snoc_induction (P := fun es => ∀ a info, (after p d es).approvers[a]? = some info →
    ApproverOrigin p d es a info) (fun a info h => by simp [after_nil, State.initial] at h) ?_ es
    a info h
  intro es e ih a info h
  rw [after_snoc] at h
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at h
    exact origin_mono (ih a info h)
  · have ha' : (stepHandle p (after p d es) e).2.accepted = true := by
      have h' := ha; rw [accepted_step ha] at h'; exact h'
    rw [accepted_step ha] at h
    rcases stepHandle_approvers ha' h with h | hs | hs
    · exact origin_mono (ih a info h)
    · exact ⟨_, _, _, trace_mem_last, ha, .inl hs⟩
    · exact ⟨_, _, _, trace_mem_last, ha, .inr hs⟩

/-- Section 8, theorem 1: once the session has started, its requester is the requester of the
trace's accepted `session_start`, the only one: every accepted `session_start` carries it. -/
theorem requester_origin (hs : (after p d es).started = true) :
    RequesterOrigin p d es (after p d es).requester := by
  suffices h : ∀ es : List Event,
      (∀ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es → v₀.accepted = true →
        ∀ i pd r' perms as l, e₀.body = .sessionStart i pd r' perms as l →
          r' = (after p d es).requester ∧ (after p d es).started = true) ∧
      ((after p d es).started = true → ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧
        v₀.accepted = true ∧ ∃ i pd perms as l,
          e₀.body = .sessionStart i pd (after p d es).requester perms as l) from
    ⟨(h es).2 hs, fun s₀ e₀ v₀ hm ha i pd r' perms as l hb => ((h es).1 s₀ e₀ v₀ hm ha i pd r' perms as l hb).1⟩
  intro es
  refine snoc_induction (P := fun es =>
      (∀ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es → v₀.accepted = true →
        ∀ i pd r' perms as l, e₀.body = .sessionStart i pd r' perms as l →
          r' = (after p d es).requester ∧ (after p d es).started = true) ∧
      ((after p d es).started = true → ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧
        v₀.accepted = true ∧ ∃ i pd perms as l,
          e₀.body = .sessionStart i pd (after p d es).requester perms as l))
    ⟨fun _ _ _ hm => by simp [trace] at hm, fun h => by simp [after_nil, State.initial] at h⟩ ?_ es
  intro es e ⟨ih₁, ih₂⟩
  cases ha : (step p (after p d es) e).2.accepted
  · have hst : after p d (es ++ [e]) = after p d es := by rw [after_snoc, frame ha]
    rw [hst]
    refine ⟨fun s₀ e₀ v₀ hm hv => ?_, fun h => ?_⟩
    · rcases trace_mem_snoc_iff.mp hm with hm | hm
      · exact ih₁ s₀ e₀ v₀ hm hv
      · cases hm
        rw [ha] at hv
        cases hv
    · obtain ⟨s₀, e₀, v₀, hm, rest⟩ := ih₂ h
      exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩
  · have ha' : (stepHandle p (after p d es) e).2.accepted = true := by
      have h' := ha; rw [accepted_step ha] at h'; exact h'
    have hst : after p d (es ++ [e]) = { (stepHandle p (after p d es) e).1 with
        lastSeq := e.seq, lastTime := e.time, version := (after p d es).version + 1 } := by
      rw [after_snoc, accepted_step ha]
    rw [hst]
    dsimp only
    rcases stepHandle_requester ha' with ⟨hns, hr, hs⟩ | ⟨i, pd, perms, as, l, hb, hs⟩
    · rw [hr, hs]
      refine ⟨fun s₀ e₀ v₀ hm hv => ?_, fun h => ?_⟩
      · rcases trace_mem_snoc_iff.mp hm with hm | hm
        · exact ih₁ s₀ e₀ v₀ hm hv
        · cases hm
          intro i pd r' perms as l hb
          rw [hb] at hns
          cases hns
      · obtain ⟨s₀, e₀, v₀, hm, rest⟩ := ih₂ h
        exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩
    · have hns : (after p d es).started = false := by
        have hn := (envelope_iff.mp (accepted_open ha)).2.2.1
        cases h : (after p d es).started
        · rfl
        · exact absurd ⟨h, by rw [hb]; rfl⟩ hn
      rw [hs]
      refine ⟨fun s₀ e₀ v₀ hm hv => ?_, fun _ => ⟨_, _, _, trace_mem_last, ha, i, pd, perms, as, l, hb⟩⟩
      rcases trace_mem_snoc_iff.mp hm with hm | hm
      · intro i' pd' r' perms' as' l' hb'
        rw [(ih₁ s₀ e₀ v₀ hm hv i' pd' r' perms' as' l' hb').2] at hns
        cases hns
      · cases hm
        intro i' pd' r' perms' as' l' hb'
        rw [hb] at hb'
        cases hb'
        exact ⟨rfl, rfl⟩

namespace Approvers

def attestPolicy : Policy := { approverRoles := ["owner"] }

def alice : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def bob : ApproverInfo := ⟨"bob", .human, ["owner"]⟩

def attested : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [("a1", alice)] {}⟩
  , ⟨2, 2, 1, none, .approverAttest "a2" bob⟩
  , ⟨3, 3, 2, none, .approverAttest "a2" ⟨"bob", .human, ["owner", "finance"]⟩⟩
  , ⟨4, 4, 2, none, .sessionStart "s2" "pd" "u2" [] [("a1", bob)] {}⟩
  , ⟨5, 5, 2, none, .approverAttest "a2" bob⟩ ]

/-- `ApproverOrigin` as a check, split by branch. -/
def startListed (es : List Event) (a : String) (info : ApproverInfo) : Bool :=
  (trace attestPolicy (State.initial "pd") es).any fun (_, e₀, v₀) =>
    v₀.accepted && match e₀.body with
      | .sessionStart _ _ _ _ as _ => as.contains (a, info)
      | _ => false

def attestCarried (es : List Event) (a : String) (info : ApproverInfo) : Bool :=
  (trace attestPolicy (State.initial "pd") es).any fun (_, e₀, v₀) =>
    v₀.accepted && e₀.body == .approverAttest a info

#guard (trace attestPolicy (State.initial "pd") attested).map (·.2.2)
  == [.ok .none none, .ok .none none, .rejected .approverChanged, .rejected .alreadyStarted,
    .ok .none none]
#guard (after attestPolicy "pd" attested).approvers["a1"]? == some alice
#guard (after attestPolicy "pd" attested).approvers["a2"]? == some bob
#guard (after attestPolicy "pd" attested).approvers.size == 2
#guard startListed attested "a1" alice && !attestCarried attested "a1" alice
#guard attestCarried attested "a2" bob && !startListed attested "a2" bob
#guard (after attestPolicy "pd" attested).started && (after attestPolicy "pd" attested).requester == "u1"

end Approvers

end Writ.Proofs
