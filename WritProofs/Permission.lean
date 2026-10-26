import WritProofs.Dispatch

namespace Writ.Proofs

open Writ

/-- Section 8, theorem 3: a disposition that lets the call go on. `existing` reports a call's past
and is not one. -/
def Decision.nonDenied : Decision → Bool
  | .allowed | .allowedByGrant _ | .needsApproval _ | .authorized => true
  | _ => false

end Writ.Proofs

namespace Writ.Decision
export Writ.Proofs.Decision (nonDenied)
end Writ.Decision

namespace Writ.Proofs

open Basic

/-- Section 8, theorem 3: held permission `perm` was attested by an accepted `session_start` of the
trace, or added by an accepted `permission_add` whose approver was attested at that point with a
principal other than `agent` and an approver role. -/
def PermissionOrigin (p : Policy) (d : String) (es : List Event) (perm : String) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧
    ((∃ i pd req perms as l, e₀.body = .sessionStart i pd req perms as l ∧ perm ∈ perms) ∨
      ∃ a info, e₀.body = .permissionAdd perm a ∧ s₀.approvers[a]? = some info ∧
        info.principal ≠ "agent" ∧ ∃ x ∈ info.roles, x ∈ p.approverRoles)

namespace Permission

variable {p : Policy} {d : String} {s s' s₁ s₂ : State} {e : Event} {es : List Event}
  {perm a : String} {info : ApproverInfo}

/-- The fields only `session_start`, `approver_attest`, `permission_add` and `permission_revoke`
write, unchanged. -/
structure Parties (s s' : State) : Prop where
  permissions : s'.permissions = s.permissions
  approvers : s'.approvers = s.approvers
  requester : s'.requester = s.requester
  started : s'.started = s.started

theorem Parties.refl : Parties s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Parties.trans (h : Parties s s₁) (h' : Parties s₁ s₂) : Parties s s₂ :=
  ⟨h'.permissions.trans h.permissions, h'.approvers.trans h.approvers,
    h'.requester.trans h.requester, h'.started.trans h.started⟩

/-- `h.with ..` extends `h` by a record update that leaves the four fields alone. -/
theorem Parties.with (h : Parties s s₁) (hp : s'.permissions = s₁.permissions)
    (ha : s'.approvers = s₁.approvers) (hr : s'.requester = s₁.requester)
    (hs : s'.started = s₁.started) : Parties s s' :=
  h.trans ⟨hp, ha, hr, hs⟩

theorem releaseGrant_parties : Parties s (s.releaseGrant k) := by
  unfold State.releaseGrant; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem consumeGrant_parties : Parties s (s.consumeGrant k) := by
  unfold State.consumeGrant; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem endCall_parties {st : CallStatus} : Parties s (s.endCall k st) := by
  unfold State.endCall
  exact releaseGrant_parties.with rfl rfl rfl rfl

theorem cancelPending_parties : Parties s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (Parties s) ?_ _ _ .refl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact ha.trans endCall_parties
  · exact ha.trans endCall_parties
  · exact ha

theorem interrupt_parties : Parties s s.interrupt := by
  unfold State.interrupt
  exact cancelPending_parties.with rfl rfl rfl rfl

theorem updateEntries_parties {m : String} {t : Nat} {f : List MeterEntry → List MeterEntry} :
    Parties s (s.updateEntries p m t f) := by
  unfold State.updateEntries; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem settle_parties {ms : List String} {o : Outcome} {x : Option Nat} {ne : Bool} {t : Nat} :
    Parties s (s.settle p ms k o x ne t).1 := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => Parties s b.1) ?_ ms _ .refl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact h.trans updateEntries_parties
  · split <;> exact h.trans updateEntries_parties

theorem recordFailure_parties {tool : String} : Parties s (s.recordFailure p tool) := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem claim_parties {t : Nat} {rc : CallRec} {r : Requirements} {retry : Bool} {key : String} :
    Parties s (claim p s t k rc r retry key) := by
  unfold claim
  dsimp only
  split
  · exact (foldl_invariant (Parties s) (fun _ _ hb => hb.trans updateEntries_parties) _ s
      .refl).with rfl rfl rfl rfl
  · exact (foldl_invariant (Parties s) (fun _ _ hb => hb.trans updateEntries_parties) _ _
      consumeGrant_parties).with rfl rfl rfl rfl

local macro "parties_keeps" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Parties.refl
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | exact cancelPending_parties.with rfl rfl rfl rfl
      | exact interrupt_parties.with rfl rfl rfl rfl
      | exact endCall_parties.with rfl rfl rfl rfl
      | exact claim_parties.with rfl rfl rfl rfl
      | exact (settle_parties.trans recordFailure_parties).with rfl rfl rfl rfl
      | exact settle_parties.with rfl rfl rfl rfl
      | exact recordFailure_parties.with rfl rfl rfl rfl)

theorem handleSessionEnd_parties : Parties s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; parties_keeps

theorem handleTurnStart_parties {u : Bool} : Parties s (handleTurnStart s u).1 := by
  unfold handleTurnStart; parties_keeps

theorem handleTurnEnd_parties : Parties s (handleTurnEnd s).1 := by
  unfold handleTurnEnd; parties_keeps

theorem handleStepStart_parties : Parties s (handleStepStart p s).1 := by
  unfold handleStepStart; parties_keeps

theorem handlePropose_parties {t : Nat} {tool dg : String} {cost : Option Cost}
    {gs xs : List (String × Bool)} : Parties s (handlePropose p s t k tool dg cost gs xs).1 := by
  unfold handlePropose; parties_keeps

theorem applyApprove_parties {t : Nat} {rc : CallRec} {w pr dg : String} {cost : Option Cost}
    {ed : Option Edit} {r : State × Verdict} (h : applyApprove p s t k rc w pr dg cost ed = .ok r) :
    Parties s r.1 := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> exact ⟨rfl, rfl, rfl, rfl⟩)

theorem handleApprove_parties {t : Nat} {rid : RequestId} {w dg : String} {cost : Option Cost}
    {ed : Option Edit} : Parties s (handleApprove p s t k rid w dg cost ed).1 := by
  unfold handleApprove
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact .refl
    | exact applyApprove_parties (by assumption)

theorem handleReject_parties {rid : RequestId} {w : String} :
    Parties s (handleReject p s k rid w).1 := by
  unfold handleReject
  split
  · exact .refl
  · exact (endCall_parties (st := .rejected)).with rfl rfl rfl rfl

theorem handleApprovalExpire_parties {rid : RequestId} :
    Parties s (handleApprovalExpire s k rid).1 := by
  unfold handleApprovalExpire; parties_keeps

theorem handleGrantCreate_parties {t : Nat} {gid w tool : String} {dg : Option String}
    {sc : GrantScope} {n : Nat} {mc : Option Cost} {nb ex : Option Nat} {rv : String} :
    Parties s (handleGrantCreate p s t gid w tool dg sc n mc nb ex rv).1 := by
  unfold handleGrantCreate; parties_keeps

theorem handleGrantRevoke_parties : Parties s (handleGrantRevoke s k).1 := by
  unfold handleGrantRevoke; parties_keeps

theorem handleDispatch_parties {t n : Nat} {dg key : String} {cost : Option Cost}
    {g : List (String × Bool)} : Parties s (handleDispatch p s t k n dg cost g key).1 := by
  rcases Dispatch.handle_cases with he | ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he]
  · exact .refl
  · exact endCall_parties
  · exact claim_parties

theorem handleResult_parties {t : Nat} {o : Outcome} {x : Option Nat} {ne : Bool} :
    Parties s (handleResult p s t k o x ne).1 := by
  unfold handleResult
  split
  · exact .refl
  next rc _ =>
    split
    · exact .refl
    · have h₁ : Parties s
          ((withStatus s k rc o.status).settle p (callMeters p rc) k o x ne t).1 :=
        (⟨rfl, rfl, rfl, rfl⟩ : Parties s (withStatus s k rc o.status)).trans settle_parties
      repeat' (first | (dsimp only) | split)
      all_goals first
        | exact h₁.trans recordFailure_parties
        | exact h₁.trans ⟨rfl, rfl, rfl, rfl⟩
        | exact h₁

theorem handleOutcomeUnknown_parties : Parties s (handleOutcomeUnknown p s k).1 := by
  unfold handleOutcomeUnknown
  split
  · exact .refl
  next rc _ =>
    split
    · exact .refl
    · exact (⟨rfl, rfl, rfl, rfl⟩ : Parties s (withStatus s k rc .unknown)).trans
        recordFailure_parties

theorem handleReconcile_parties {t : Nat} {o : Outcome} {x : Option Nat} {ne : Bool} :
    Parties s (handleReconcile p s t k o x ne).1 := by
  unfold handleReconcile
  split
  · exact .refl
  next rc _ =>
    split
    · exact .refl
    · split
      · exact .refl
      · have h₁ : Parties s
            ({ s with calls := s.calls.insert k { rc with reconciled := some o } }.settle p
              (callMeters p rc) k o x ne t).1 :=
          (⟨rfl, rfl, rfl, rfl⟩ : Parties s
            { s with calls := s.calls.insert k { rc with reconciled := some o } }).trans
            settle_parties
        repeat' (first | (dsimp only) | split)
        all_goals first
          | exact h₁.trans recordFailure_parties
          | exact h₁

theorem handleCancel_parties : Parties s (handleCancel s k).1 := by
  unfold handleCancel; parties_keeps

theorem handleReset_parties : Parties s (handleReset s).1 := by
  unfold handleReset; parties_keeps

theorem handleKill_parties : Parties s (handleKill p s).1 := by
  unfold handleKill; parties_keeps

theorem handleEscalationAck_parties {w : String} {n : Nat} :
    Parties s (handleEscalationAck p s w n).1 := by
  unfold handleEscalationAck; parties_keeps

theorem handleLedgerSync_parties {l : Ledger} : Parties s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; parties_keeps

theorem Parties.src (hp : Parties s s') (h : s'.approvers[a]? = some info) :
    s.approvers[a]? = some info := hp.approvers ▸ h

theorem Parties.req {b : EventBody} (hp : Parties s s') (hb : b.isStart = false) :
    b.isStart = false ∧ s'.requester = s.requester ∧ s'.started = s.started :=
  ⟨hb, hp.requester, hp.started⟩

def Source (p : Policy) (s : State) (e : Event) (perm : String) : Prop :=
  perm ∈ s.permissions ∨
    (∃ i pd req perms as l, e.body = .sessionStart i pd req perms as l ∧ perm ∈ perms) ∨
    ∃ a, e.body = .permissionAdd perm a ∧ s.eligibleAny p .none a = none

theorem Source.of_parties {v : Verdict} (h : Parties s s') :
    v.accepted = true → perm ∈ s'.permissions → Source p s e perm :=
  fun _ hm => .inl (h.permissions ▸ hm)

theorem stepHandle_source :
    (stepHandle p s e).2.accepted = true → perm ∈ (stepHandle p s e).1.permissions →
      Source p s e perm := by
  unfold stepHandle
  split <;> rename_i hb
  all_goals first
    | with_reducible exact Source.of_parties handleSessionEnd_parties
    | with_reducible exact Source.of_parties handleTurnStart_parties
    | with_reducible exact Source.of_parties handleTurnEnd_parties
    | with_reducible exact Source.of_parties handleStepStart_parties
    | with_reducible exact Source.of_parties handlePropose_parties
    | with_reducible exact Source.of_parties handleApprove_parties
    | with_reducible exact Source.of_parties handleReject_parties
    | with_reducible exact Source.of_parties handleApprovalExpire_parties
    | with_reducible exact Source.of_parties handleGrantCreate_parties
    | with_reducible exact Source.of_parties handleGrantRevoke_parties
    | with_reducible exact Source.of_parties handleDispatch_parties
    | with_reducible exact Source.of_parties handleResult_parties
    | with_reducible exact Source.of_parties handleOutcomeUnknown_parties
    | with_reducible exact Source.of_parties handleReconcile_parties
    | with_reducible exact Source.of_parties handleCancel_parties
    | with_reducible exact Source.of_parties handleReset_parties
    | with_reducible exact Source.of_parties handleKill_parties
    | with_reducible exact Source.of_parties handleEscalationAck_parties
    | with_reducible exact Source.of_parties handleLedgerSync_parties
    | skip
  · unfold handleSessionStart
    split
    · intro ha; cases ha
    split
    · intro ha; cases ha
    exact fun _ hm => .inr (.inl ⟨_, _, _, _, _, _, hb, hm⟩)
  · unfold handleApproverAttest
    split <;> exact fun _ hm => .inl hm
  · intro _ hm
    exact .inl (List.mem_filter.mp hm).1
  · unfold handlePermissionAdd
    split
    · intro ha; cases ha
    rename_i hel
    split
    · exact fun _ hm => .inl hm
    · intro _ hm
      rcases List.mem_append.mp hm with hm | hm
      · exact .inl hm
      · rw [List.mem_singleton.mp hm]
        exact .inr (.inr ⟨_, hb, hel⟩)

/-- `f` stands for the kernel's private `eligibilityClauses`, unfolded by `rfl` as in
`clauses_all`. -/
theorem clauses_none {q : Clause → Bool} (f : Consent → List Clause)
    (hf : ∀ c, f c = if c.clauses.isEmpty then [{ k := 1, humanOnly := false }] else c.clauses)
    (h : (f .none).any q = true) : q { k := 1, humanOnly := false } = true := by
  rw [hf] at h
  simpa [Consent.none, Consent.clauses] using h

theorem eligibleAny_none {a : String} (h : s.eligibleAny p .none a = none) :
    ∃ info, s.approvers[a]? = some info ∧ info.principal ≠ "agent" ∧
      ∃ x ∈ info.roles, x ∈ p.approverRoles := by
  unfold State.eligibleAny at h
  split at h
  · cases h
  split at h
  · rename_i hany
    have he := clauses_none _ (fun _ => rfl) hany
    unfold State.eligibleFor at he
    rw [Std.ExtTreeMap.get?_eq_getElem?] at he
    cases hi : s.approvers[a]? with
    | none => rw [hi] at he; cases he
    | some info =>
      rw [hi] at he
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, decide_eq_true_eq] at he
      exact ⟨info, rfl, he.1.1.1.1, he.1.1.1.2⟩
  · cases h

theorem origin_mono (h : PermissionOrigin p d es perm) :
    PermissionOrigin p d (es ++ [e]) perm := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem repeat_perm (h : (repeatDecision p s t k rc).1 = dc) (hnd : dc.nonDenied = true)
    (hm : p.modeOf rc.tool = .enforce) (hp : ((p.action? rc.tool).getD {}).permission = some perm) :
    perm ∈ s.permissions := by
  refine Classical.byContradiction fun hn => ?_
  have hany : ((p.action? rc.tool).getD {}).permission.any (· ∉ s.permissions) = true := by
    rw [hp]; simpa using hn
  unfold repeatDecision at h
  simp only [hany, hm] at h
  split at h
  · subst h; cases hnd
  cases hst : rc.status <;> cases hb : s.blocked rc.tool <;> simp [hst, hb] at h <;> subst h <;>
    simp [Decision.nonDenied] at hnd

theorem enforce_perm {tool dg : String} {gs es : List (String × Bool)}
    (h : (enforceDecision p s t k tool dg cost gs es).1 = dd) (hnd : dd.decision.nonDenied = true)
    (hp : ((p.action? tool).getD {}).permission = some perm) : perm ∈ s.permissions := by
  refine Classical.byContradiction fun hn => ?_
  have hany : ((p.action? tool).getD {}).permission.any (· ∉ s.permissions) = true := by
    rw [hp]; simpa using hn
  have hpre : preConsentDenial p s t ((p.action? tool).getD {}) tool dg cost gs ≠ none := by
    unfold preConsentDenial
    simp only [hany, ↓reduceIte]
    repeat' split
    all_goals simp
  unfold enforceDecision at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (subst h; simp [Disposition.decision, Decision.nonDenied] at hnd; done)
    | exact hpre (by assumption)

theorem handlePropose_perm {tool dg : String} {gs es : List (String × Bool)}
    (hv : (handlePropose p s t k tool dg cost gs es).2 = .ok dc sh) (hnd : dc.nonDenied = true)
    (hm : p.modeOf tool = .enforce) (hr : p.action? tool = some r)
    (hp : r.permission = some perm) : perm ∈ s.permissions := by
  unfold handlePropose at hv
  split at hv
  · rename_i rc _
    split at hv
    · rename_i hmatch
      obtain ⟨ht, -⟩ := hmatch
      subst ht
      exact repeat_perm (by injection hv) hnd hm (by rw [hr]; exact hp)
    · cases hv
  · split at hv
    rename_i dd cs hd
    split at hv
    · rename_i hn; rw [hr] at hn; cases hn
    · rename_i r' hr'
      rw [hr] at hr'
      cases hr'
      have hsh : dd.shadowed (p.modeOf tool) = (dd, none) := by rw [hm]; cases dd <;> rfl
      simp only [hsh] at hv
      injection hv with hdc
      subst hdc
      exact enforce_perm (by rw [hd]) hnd (by rw [hr]; exact hp)

end Permission

open Permission

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event} {perm : String}

/-- Section 8, theorem 3 at propose: a proposal of an enforced action answered with a disposition
that is not a denial, new or repeated, occurs only while the action's permission is held. -/
theorem permission_propose {k t dg : String} {cost : Option Cost} {gs esc : List (String × Bool)}
    {r : Requirements} {dc : Decision} {sh : Option Shadow}
    (he : e.body = .propose k t dg cost gs esc) (hm : p.modeOf t = .enforce)
    (hr : p.action? t = some r) (hp : r.permission = some perm) (hv : (step p s e).2 = .ok dc sh)
    (hnd : dc.nonDenied = true) : perm ∈ s.permissions := by
  have ha : (step p s e).2.accepted = true := by rw [hv]; rfl
  rw [accepted_step ha] at hv
  simp only [stepHandle, he] at hv
  exact handlePropose_perm hv hnd hm hr hp

/-- Section 8, theorem 3 at dispatch: a claimed dispatch of an enforced action occurs only while
the action's permission is held. -/
theorem permission_claim {k dg key : String} {n : Nat} {cost : Option Cost}
    {g : List (String × Bool)} {c : CallRec} {r : Requirements}
    (h : (step p s e).2.claimed = true) (he : e.body = .dispatch k n dg cost g key)
    (hc : s.calls[k]? = some c) (hm : p.modeOf c.tool = .enforce) (hr : p.action? c.tool = some r)
    (hp : r.permission = some perm) : perm ∈ s.permissions := by
  obtain ⟨-, c', hc', -, hok⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  exact (hok hm).1.2.1 perm (by rw [hr]; exact hp)

/-- Section 8, theorem 3: every held permission was attested at `session_start` or added by an
attested approver holding an approver role whose principal is not `agent`. -/
theorem permission_origin (hp : perm ∈ (after p d es).permissions) :
    PermissionOrigin p d es perm := by
  refine snoc_induction (P := fun es => ∀ perm, perm ∈ (after p d es).permissions →
    PermissionOrigin p d es perm) (fun perm h => by simp [after_nil, State.initial] at h) ?_ es
    perm hp
  intro es e ih perm h
  rw [after_snoc] at h
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at h
    exact origin_mono (ih perm h)
  · have ha' : (stepHandle p (after p d es) e).2.accepted = true := by
      have h' := ha; rw [accepted_step ha] at h'; exact h'
    rw [accepted_step ha] at h
    rcases stepHandle_source ha' h with h | hs | ⟨a, hb, hel⟩
    · exact origin_mono (ih perm h)
    · exact ⟨_, _, _, trace_mem_last, ha, .inl hs⟩
    · obtain ⟨info, hi, hag, hrole⟩ := eligibleAny_none hel
      exact ⟨_, _, _, trace_mem_last, ha, .inr ⟨a, info, hb, hi, hag, hrole⟩⟩

namespace Permission

/-- `PermissionOrigin` as a check, split by branch. -/
def startedWith (p : Policy) (d : String) (es : List Event) (perm : String) : Bool :=
  (trace p (State.initial d) es).any fun (_, e₀, v₀) =>
    v₀.accepted && match e₀.body with
      | .sessionStart _ _ _ perms _ _ => perms.contains perm
      | _ => false

def addedBy (p : Policy) (d : String) (es : List Event) (perm : String) : Bool :=
  (trace p (State.initial d) es).any fun (s₀, e₀, v₀) =>
    v₀.accepted && match e₀.body with
      | .permissionAdd perm' a =>
        perm' == perm && (s₀.approvers[a]?).any fun info =>
          info.principal != "agent" && info.roles.any (· ∈ p.approverRoles)
      | _ => false

def permPolicy : Policy :=
  { approverRoles := ["owner"]
    actions := [("t", { permission := some "p1" }),
      ("u", { permission := some "p1", consent := .perCall })] }

def permOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" ["p1"]
      [("a1", ⟨"alice", .human, ["owner"]⟩), ("bot", ⟨"agent", .automated, ["owner"]⟩)] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "u" "d2" none [] []⟩ ]

def repeatT : Event := ⟨5, 5, 4, none, .propose "c1" "t" "d1" none [] []⟩
def repeatU : Event := ⟨5, 5, 4, none, .propose "c2" "u" "d2" none [] []⟩
def dispatchT : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

#guard decide permPolicy.WF
#guard permPolicy.modeOf "t" == .enforce && permPolicy.modeOf "u" == .enforce
#guard (permPolicy.action? "t").any (·.permission == some "p1")
#guard (permPolicy.action? "u").any (·.permission == some "p1")
#guard (trace permPolicy (State.initial "pd") permOpen).map (·.2.2)
  == [.ok .none none, .ok .none none, .ok .allowed none,
    .ok (.needsApproval ⟨"s1", "c2", 0⟩) none]
#guard (after permPolicy "pd" permOpen).permissions == ["p1"]
#guard ((after permPolicy "pd" permOpen).calls["c1"]?).any (·.status == .authorized)
#guard ((after permPolicy "pd" permOpen).calls["c2"]?).any (·.status == .awaiting)
#guard (step permPolicy (after permPolicy "pd" permOpen) repeatT).2 == .ok .allowed none
#guard (step permPolicy (after permPolicy "pd" permOpen) repeatU).2
  == .ok (.needsApproval ⟨"s1", "c2", 0⟩) none
#guard (step permPolicy (after permPolicy "pd" permOpen) dispatchT).2.claimed

def revoked : List Event := permOpen ++ [⟨5, 5, 4, none, .permissionRevoke "p1"⟩]

def revokedRepeat : Event := ⟨6, 6, 5, none, .propose "c1" "t" "d1" none [] []⟩
def revokedDispatch : Event := ⟨6, 6, 5, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

#guard (after permPolicy "pd" revoked).permissions == []
#guard ((after permPolicy "pd" revoked).calls["c1"]?).any (·.status == .authorized)
#guard (step permPolicy (after permPolicy "pd" revoked) revokedRepeat).2
  == .ok (.denied .permissionMissing) none
#guard (step permPolicy (after permPolicy "pd" revoked) revokedDispatch).2
  == .ok (.dispatchDenied .permissionMissing) none
#guard ((step permPolicy (after permPolicy "pd" revoked) revokedDispatch).1.calls["c1"]?).any
  (·.status == .deniedAtDispatch .permissionMissing)

def added : List Event := revoked ++ [⟨6, 6, 5, none, .permissionAdd "p2" "a1"⟩]

def agentAdd : Event := ⟨7, 7, 6, none, .permissionAdd "p3" "bot"⟩

#guard (trace permPolicy (State.initial "pd") added).all (·.2.2.accepted)
#guard (after permPolicy "pd" added).permissions == ["p2"]
#guard addedBy permPolicy "pd" added "p2" && !startedWith permPolicy "pd" added "p2"
#guard startedWith permPolicy "pd" permOpen "p1"
#guard (step permPolicy (after permPolicy "pd" added) agentAdd).2
  == .rejected .approverNotEligible
#guard (step permPolicy (after permPolicy "pd" added) agentAdd).1.permissions == ["p2"]

end Permission

end Writ.Proofs
