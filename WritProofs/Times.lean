import WritProofs.Origin
import WritProofs.Support

namespace Writ.Proofs

open Writ
open Basic Calls Proofs.Consent Approvals

/-- Section 5 and section 8, theorems 1 and 6: `t` is the time of the event that requested
approval of generation `g` of call `k`. For generation 0 it is the accepted `propose` that created
the call, answered `needs_approval`; for generation `g + 1`, an accepted `approve` of the call
whose edit answered the request of generation `g`. -/
def RequestTime (p : Policy) (d : String) (es : List Event) (k : String) (g t : Nat) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧ e₀.time = t ∧
    ((g = 0 ∧ s₀.calls[k]? = none ∧ (∃ rid sh, v₀ = .ok (.needsApproval rid) sh) ∧
        ∃ tool dg cost gs esc, e₀.body = .propose k tool dg cost gs esc) ∨
      ∃ rid a rd rc x, e₀.body = .approve k rid a rd rc (some x) ∧ rid.generation + 1 = g)

/-- Section 8, theorems 1 and 6: `t` is the time of the event that authorized call `k`: the
accepted `propose` that created the call, answered `allowed` or `allowed_by_grant`, or an accepted
`approve` of the call answered `authorized`. -/
def AuthorizationTime (p : Policy) (d : String) (es : List Event) (k : String) (t : Nat) : Prop :=
  ∃ s₀ e₀ v₀, (s₀, e₀, v₀) ∈ trace p (State.initial d) es ∧ v₀.accepted = true ∧ e₀.time = t ∧
    ((s₀.calls[k]? = none ∧
        (∃ sh, v₀ = .ok .allowed sh ∨ ∃ gid, v₀ = .ok (.allowedByGrant gid) sh) ∧
        ∃ tool dg cost gs esc, e₀.body = .propose k tool dg cost gs esc) ∨
      (v₀ = .ok .authorized none ∧ ∃ rid a rd rc ed, e₀.body = .approve k rid a rd rc ed))

/-- Section 8, theorems 1 and 6: the times record `c` of call `k` measures its TTLs from. While the
call awaits approval, and once an approval has counted, `requestedAt` is the time of the request
of its current generation (`RequestTime`); `authorizedAt`, once set, is the time of the event that
authorized the call (`AuthorizationTime`). -/
def CallTimes (p : Policy) (d : String) (es : List Event) (k : String) (c : CallRec) : Prop :=
  ((c.status = .awaiting ∨ c.tally ≠ []) → RequestTime p d es k c.generation c.requestedAt) ∧
  ∀ t, c.authorizedAt = some t → AuthorizationTime p d es k t

namespace Times

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event} {k : String}
  {c c' : CallRec}

/-- What step `e`, with result `r`, leaves in a call record, for the fields `CallTimes` reads: one
from before it up to `RecSame`; one from before it that an accepted `approve` answered, with the
request time moved to the step's time by an edit and the authorization time set to it when the
approval authorized the call; or a new one from the step's `propose`. -/
def Moved (s : State) (e : Event) (r : State × Verdict) : Prop :=
  ∀ (k : String) (c' : CallRec), r.1.calls[k]? = some c' →
    (∃ c, s.calls[k]? = some c ∧ RecSame c c') ∨
    (∃ c rid a rd rc ed, s.calls[k]? = some c ∧ c.status = .awaiting ∧
      e.body = .approve k rid a rd rc ed ∧ rid.generation = c.generation ∧
      ((ed = none ∧ c'.generation = c.generation ∧ c'.requestedAt = c.requestedAt) ∨
        (∃ x, ed = some x ∧ c'.generation = c.generation + 1 ∧ c'.requestedAt = e.time)) ∧
      (c'.authorizedAt = c.authorizedAt ∨
        (c'.authorizedAt = some e.time ∧ r.2 = .ok .authorized none))) ∨
    (s.calls[k]? = none ∧ (∃ tool dg cost gs esc, e.body = .propose k tool dg cost gs esc) ∧
      c'.generation = 0 ∧ c'.tally = [] ∧
      (c'.status = .awaiting → c'.requestedAt = e.time ∧
        ∃ rid sh, r.2 = .ok (.needsApproval rid) sh) ∧
      ∀ t, c'.authorizedAt = some t → t = e.time ∧
        ∃ sh, r.2 = .ok .allowed sh ∨ ∃ gid, r.2 = .ok (.allowedByGrant gid) sh)

theorem Moved.of_keeps {r : State × Verdict} (h : Keeps s r.1) : Moved s e r :=
  fun k c' hc => .inl (h.calls k c' hc)

theorem Moved.of_calls {r : State × Verdict} (h : r.1.calls = s.calls) : Moved s e r :=
  fun _ c' hc => .inl ⟨c', h ▸ hc, .refl⟩

theorem moved_propose {i tool dg' : String} {cs : Option Cost} {gs xs : List (String × Bool)}
    (hb : e.body = .propose i tool dg' cs gs xs) :
    Moved s e (handlePropose p s e.time i tool dg' cs gs xs) := by
  unfold handlePropose
  split
  · split <;> exact .of_calls rfl
  · rename_i hk
    split
    rename_i dd cn hd
    split
    · exact .of_calls rfl
    · refine Origin.forall_insert (fun _ c' hc' => .inl ⟨c', hc', .refl⟩) (.inr (.inr
        ⟨by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hk, ⟨_, _, _, _, _, hb⟩, rfl, rfl, ?_⟩))
      dsimp only
      generalize dd.shadowed (p.modeOf tool) = x
      obtain ⟨d', sh⟩ := x
      cases d' <;> simp [Disposition.status, Disposition.decision]

theorem moved_approve {i a rd : String} {rid : RequestId} {cs : Option Cost} {ed : Option Edit}
    (hb : e.body = .approve i rid a rd cs ed) :
    Moved s e (handleApprove p s e.time i rid a rd cs ed) := by
  unfold handleApprove
  split
  · exact .of_calls rfl
  · rename_i rc hck
    have hk := awaitingCheck_ok hck
    have hst := (awaitingCheck_facts hck).1
    have hrid := awaitingCheck_rid hck
    dsimp only
    split
    · exact .of_calls rfl
    · rename_i r hr
      obtain ⟨x, hx, -, hcase, hauth⟩ := Origin.applyApprove_record hr
      rw [Moved, hx]
      refine Origin.forall_insert (fun _ c' hc' => .inl ⟨c', hc', .refl⟩)
        (.inr (.inl ⟨rc, rid, a, rd, cs, ed, hk, hst, hb, by rw [hrid], ?_, hauth⟩))
      rcases hcase with ⟨hed, hkept, hra⟩ | ⟨ed', hed, hg, -, -, hra⟩
      · exact .inl ⟨hed, hkept.generation, hra⟩
      · exact .inr ⟨ed', hed, hg, hra⟩

theorem moved_stepHandle : Moved s e (stepHandle p s e) :=
  Origin.stepHandle_of (fun _ h => .of_keeps h) (fun _ h => .of_calls h) moved_propose
    moved_approve

theorem request_mono {g t : Nat} (h : RequestTime p d es k g t) :
    RequestTime p d (es ++ [e]) k g t := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem auth_mono {t : Nat} (h : AuthorizationTime p d es k t) :
    AuthorizationTime p d (es ++ [e]) k t := by
  obtain ⟨s₀, e₀, v₀, hm, rest⟩ := h
  exact ⟨s₀, e₀, v₀, trace_mem_snoc hm, rest⟩

theorem times_mono (h : CallTimes p d es k c) : CallTimes p d (es ++ [e]) k c :=
  ⟨fun hg => request_mono (h.1 hg), fun t ht => auth_mono (h.2 t ht)⟩

theorem times_same (h : CallTimes p d es k c) (hs : RecSame c c') : CallTimes p d es k c' := by
  refine ⟨fun hg => ?_, fun t ht => h.2 t (hs.authorizedAt ▸ ht)⟩
  rw [hs.generation, hs.requestedAt]
  refine h.1 (hg.imp hs.awaiting fun hn => ?_)
  rw [← hs.tally]
  exact hn

theorem times_snoc (ih : ∀ k c, (after p d es).calls[k]? = some c → CallTimes p d es k c)
    (hc' : (after p d (es ++ [e])).calls[k]? = some c') : CallTimes p d (es ++ [e]) k c' := by
  rw [after_snoc] at hc'
  cases ha : (step p (after p d es) e).2.accepted
  · rw [frame ha] at hc'
    exact times_mono (ih k c' hc')
  have hst := accepted_step ha
  rw [hst] at hc'
  rcases moved_stepHandle (p := p) k c' hc' with ⟨c, hc, hs⟩ |
      ⟨c, rid, a, rd, rc, ed, hc, haw, hb, hrid, hreq, hauth⟩ |
      ⟨hn, ⟨tool, dg, cost, gs, esc, hb⟩, hg0, htally, hreq, hauth⟩
  · exact times_mono (times_same (ih k c hc) hs)
  · have hv : (step p (after p d es) e).2 = (stepHandle p (after p d es) e).2 := by rw [hst]
    refine ⟨fun _ => ?_, fun t ht => ?_⟩
    · rcases hreq with ⟨-, hg, hra⟩ | ⟨x, hed, hg, hra⟩
      · rw [hg, hra]
        exact request_mono ((ih k c hc).1 (.inl haw))
      · subst hed
        exact ⟨_, _, _, trace_mem_last, ha, hra.symm, .inr ⟨rid, a, rd, rc, x, hb, by rw [hrid, hg]⟩⟩
    · rcases hauth with he | ⟨he, hok⟩
      · exact auth_mono ((ih k c hc).2 t (he ▸ ht))
      · rw [he] at ht
        cases ht
        exact ⟨_, _, _, trace_mem_last, ha, rfl, .inr ⟨by rw [hv]; exact hok, rid, a, rd, rc, ed, hb⟩⟩
  · have hv : (step p (after p d es) e).2 = (stepHandle p (after p d es) e).2 := by rw [hst]
    refine ⟨fun hg => ?_, fun t ht => ?_⟩
    · have haw : c'.status = .awaiting := hg.resolve_right (fun h => h htally)
      obtain ⟨hra, rid, sh, hok⟩ := hreq haw
      rw [hg0]
      exact ⟨_, _, _, trace_mem_last, ha, hra.symm,
        .inl ⟨rfl, hn, ⟨rid, sh, by rw [hv]; exact hok⟩, tool, dg, cost, gs, esc, hb⟩⟩
    · obtain ⟨rfl, sh, hok⟩ := hauth t ht
      exact ⟨_, _, _, trace_mem_last, ha, rfl, .inl ⟨hn, ⟨sh, by rw [hv]; exact hok⟩, tool, dg,
        cost, gs, esc, hb⟩⟩

theorem time_le_last : ∀ x ∈ trace p (State.initial d) es, x.2.2.accepted = true →
    x.2.1.time ≤ (after p d es).lastTime := by
  refine snoc_induction (P := fun es => ∀ x ∈ trace p (State.initial d) es,
    x.2.2.accepted = true → x.2.1.time ≤ (after p d es).lastTime)
    (fun x hx => by simp [trace] at hx) ?_ es
  intro es e ih x hx hacc
  rw [after_snoc]
  rcases trace_mem_snoc_iff.mp hx with hx | rfl
  · exact Nat.le_trans (ih x hx hacc) (Support.step_mono (p := p) (e := e)).2
  · exact Nat.le_of_eq (accepted_seq_time hacc).2.2.2.symm

end Times

open Times

variable {p : Policy} {d : String} {e : Event} {es : List Event} {k : String} {c : CallRec}

/-- Section 8, theorems 1 and 6: the times every call record measures its TTLs from are event
times. While the call awaits approval, and once an approval has counted, `requestedAt` is the time
of the accepted `propose` answered `needs_approval` (generation 0) or of the accepted edit that
made the current generation; once set, `authorizedAt` is the time of the accepted `propose`
answered `allowed` or `allowed_by_grant`, or of the accepted `approve` answered `authorized`. -/
theorem call_times (hc : (after p d es).calls[k]? = some c) : CallTimes p d es k c :=
  snoc_induction (P := fun es => ∀ k c, (after p d es).calls[k]? = some c →
    CallTimes p d es k c) (fun k c h => by simp [after_nil, State.initial] at h)
    (fun _ _ ih _ _ hc' => times_snoc ih hc') es k c hc

/-- Section 8, theorem 6 over event times: an accepted `approve` answers the current request of an
Awaiting call, and comes at or after the time `t₀` of the event that made that request
(`RequestTime`) and before `t₀` plus the action's `approval_ttl`. -/
theorem approve_fresh_event {rid : RequestId} {a dg : String} {cost : Option Cost}
    {ed : Option Edit} (h : (step p (after p d es) e).2.accepted = true)
    (he : e.body = .approve k rid a dg cost ed) :
    ∃ c t₀, (after p d es).calls[k]? = some c ∧ c.status = .awaiting ∧
      rid = ⟨(after p d es).sessionId, k, c.generation⟩ ∧ RequestTime p d es k c.generation t₀ ∧
      t₀ ≤ e.time ∧
      ∀ ttl, p.approvalTtl ((p.action? c.tool).getD {}) = some ttl → e.time < t₀ + ttl := by
  obtain ⟨c, hc, hs, hrid, -, httl⟩ := approve_fresh h he
  exact ⟨c, c.requestedAt, hc, hs, hrid, (call_times hc).1 (.inl hs),
    Nat.le_trans ((approvalInv es).requestedAt k c hc) (envelope_time (accepted_open h)), httl⟩

/-- Section 8, theorem 6 over event times: a claimed dispatch of an enforced call, first attempt or
retry, comes at or after the time `t₀` of the event that authorized the call
(`AuthorizationTime`) and before `t₀` plus the action's `authorized_ttl`. -/
theorem claim_authorized_ttl_event {n ttl : Nat} {dg key : String} {cost : Option Cost}
    {g : List (String × Bool)} {r : Requirements}
    (h : (step p (after p d es) e).2.claimed = true) (he : e.body = .dispatch k n dg cost g key)
    (hc : (after p d es).calls[k]? = some c) (hm : p.modeOf c.tool = .enforce)
    (hra : p.action? c.tool = some r) (ht : p.authorizedTtl r = some ttl) :
    ∃ t₀, AuthorizationTime p d es k t₀ ∧ t₀ ≤ e.time ∧ e.time < t₀ + ttl := by
  obtain ⟨t₀, hat, hlt⟩ := claim_authorized_ttl reachable_after h he hc hm hra ht
  obtain ⟨s₀, e₀, v₀, hm₀, ha₀, ht₀, -⟩ := (call_times hc).2 t₀ hat
  refine ⟨t₀, (call_times hc).2 t₀ hat, ?_, hlt⟩
  rw [← ht₀]
  exact Nat.le_trans (time_le_last (s₀, e₀, v₀) hm₀ ha₀)
    (envelope_time (accepted_open (claimed_accepted h)))

namespace Times

def ttlPolicy : Policy :=
  { approverRoles := ["owner"]
    actions := [("pay",
      { consent := .quorum 2 none true false, approvalTtlMs := some 10, authorizedTtlMs := some 20 })] }

def ttlEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" []
      [("a1", ⟨"alice", .human, ["owner"]⟩), ("a2", ⟨"bob", .human, ["owner"]⟩)] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "pay" "d1" none [] []⟩
  , ⟨4, 9, 3, none, .approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none none⟩
  , ⟨5, 12, 4, none, .approve "c1" ⟨"s1", "c1", 0⟩ "a2" "d1" none none⟩ ]

def lateApprove : Event := ⟨5, 13, 4, none, .approve "c1" ⟨"s1", "c1", 0⟩ "a2" "d1" none none⟩
def inTtl : Event := ⟨6, 31, 5, none, .dispatch "c1" 1 "d1" none [] "k1"⟩
def pastTtl : Event := ⟨6, 32, 5, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

/-- `RequestTime` and `AuthorizationTime` as checks. -/
def requestedBy (es : List Event) (k : String) (g t : Nat) : Bool :=
  (trace ttlPolicy (State.initial "pd") es).any fun (s₀, e₀, v₀) =>
    v₀.accepted && e₀.time == t && match e₀.body, v₀ with
      | .propose k' .., .ok (.needsApproval _) _ => k' == k && g == 0 && (s₀.calls[k]?).isNone
      | .approve k' rid _ _ _ (some _), _ => k' == k && rid.generation + 1 == g
      | _, _ => false

def authorizedBy (es : List Event) (k : String) (t : Nat) : Bool :=
  (trace ttlPolicy (State.initial "pd") es).any fun (s₀, e₀, v₀) =>
    v₀.accepted && e₀.time == t && match e₀.body, v₀ with
      | .propose k' .., .ok .allowed _ | .propose k' .., .ok (.allowedByGrant _) _ =>
        k' == k && (s₀.calls[k]?).isNone
      | .approve k' .., .ok .authorized none => k' == k
      | _, _ => false

#guard decide ttlPolicy.WF
#guard (trace ttlPolicy (State.initial "pd") ttlEvents).map (·.2.2)
  == [.ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) none, .ok .pending none,
    .ok .authorized none]
#guard ((after ttlPolicy "pd" (ttlEvents.take 4)).calls["c1"]?).any fun c =>
  c.status == .awaiting && c.requestedAt == 3 && c.tally.length == 1 &&
    requestedBy (ttlEvents.take 4) "c1" c.generation c.requestedAt
#guard (step ttlPolicy (after ttlPolicy "pd" (ttlEvents.take 4)) lateApprove).2
  == .rejected .approvalExpired
#guard ((after ttlPolicy "pd" ttlEvents).calls["c1"]?).any fun c =>
  c.status == .authorized && c.requestedAt == 3 && c.authorizedAt == some 12 &&
    requestedBy ttlEvents "c1" c.generation c.requestedAt && authorizedBy ttlEvents "c1" 12
#guard (step ttlPolicy (after ttlPolicy "pd" ttlEvents) inTtl).2.claimed
#guard (step ttlPolicy (after ttlPolicy "pd" ttlEvents) pastTtl).2
  == .ok (.dispatchDenied .authorizationExpired) none
#guard ttlPolicy.modeOf "pay" == .enforce
#guard (ttlPolicy.action? "pay").any (ttlPolicy.authorizedTtl · == some 20)

def editTimes : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [("a1", ⟨"alice", .human, ["owner"]⟩)] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "pay" "d1" none [] []⟩
  , ⟨4, 7, 3, none, .approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none (some { newDigest := "d2" })⟩ ]

#guard ((after { ttlPolicy with bindingMutable := true } "pd" editTimes).calls["c1"]?).any
  fun c => c.status == .awaiting && c.generation == 1 && c.requestedAt == 7

end Times

end Writ.Proofs
