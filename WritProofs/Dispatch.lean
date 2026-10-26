import WritProofs.Envelope
import WritProofs.Usage
import WritProofs.WF

namespace Writ.Proofs

open Writ
open Basic

/-- Section 6, Dispatch and Protocol errors: what the event and the stored record must agree on
before re-evaluation. -/
def ProtocolOk (s : State) (r : Requirements) (c : CallRec) (n : Nat) (dg : String)
    (cost : Option Cost) (key : String) : Prop :=
  (c.status = .authorized ∨ c.status = .unknown) ∧
  (c.status = .unknown → c.reconciled = none ∧ r.retryAfterUnknown = true ∧ c.epoch = s.epoch ∧
    c.attempts < r.maxAttempts) ∧
  n = c.attempts + 1 ∧ dg = c.digest ∧ cost = c.cost ∧
  ∀ k', c.idempotencyKey = some k' → k' = key

/-- Section 6, Dispatch: the re-evaluation whose failure ends a first attempt `DeniedAtDispatch`
or `Expired`. The authorized TTL runs from the authorization time, retries included. -/
def AuthOk (p : Policy) (s : State) (t : Nat) (r : Requirements) (c : CallRec) (retry : Prop) :
    Prop :=
  (∀ ttl, p.authorizedTtl r = some ttl → t < c.authorizedAt.getD 0 + ttl) ∧
  (∀ perm, r.permission = some perm → perm ∈ s.permissions) ∧
  (¬retry → (c.tool, c.digest) ∉ s.rejectedMemory) ∧
  ∀ gid, c.grant = some gid → ∃ gr, s.grants[gid]? = some gr ∧ gr.revoked = false ∧
    gr.epoch = s.epoch ∧ (∀ nb, gr.notBefore = some nb → nb ≤ t) ∧
    (∀ x, gr.expiresAt = some x → t < x) ∧
    (gr.scope = .turn → s.turnActive = true ∧ gr.turn = s.turnIndex)

/-- Section 6, Meters: the meter is defined, a money meter gets a cost in its currency within
`max_per_call`, and the call's draw fits the cap on the usage at `t`. -/
def MeterFits (p : Policy) (s : State) (t : Nat) (m : String) (cost : Option Cost) : Prop :=
  ∃ spec, p.meter? m = some spec ∧
    (∀ cur, spec.unit = .money cur → ∃ cc, cost = some cc ∧ cc.currency = cur ∧
      ∀ mx, spec.maxPerCall = some mx → cc.amount ≤ mx) ∧
    ∀ cap, spec.cap = some cap → usageAt spec (entriesOf p s m) m t + draw spec cost ≤ cap

/-- Section 6, Meters: a retry must fit meter `m` again when the session's first entry for call
`k` on `m` is missing or has left the window at `t`. -/
def Stale (p : Policy) (s : State) (t : Nat) (m k : String) : Prop :=
  ∀ en, (entriesOf p s m).find? (fun en => en.meter == m && en.session == s.sessionId &&
      en.call == k) = some en →
    ∀ spec, p.meter? m = some spec → spec.windowMs.all (en.time + · > t) = false

/-- Section 6, Dispatch: the transient checks, whose failure rejects the dispatch and leaves the
call as it is. -/
def ReadyOk (p : Policy) (s : State) (t : Nat) (r : Requirements) (c : CallRec) (k : String)
    (retry : Prop) (g : List (String × Bool)) : Prop :=
  s.escalated = false ∧ c.tool ∉ s.blockedTools ∧
  (∀ x ∈ r.guards, lookupFlag g x = some true) ∧
  ∀ m ∈ r.meters, (retry → Stale p s t m k) → MeterFits p s t m c.cost

variable {p : Policy} {s : State} {e : Event} {k dg key : String} {n t : Nat}
  {cost : Option Cost} {g : List (String × Bool)} {c : CallRec} {r : Requirements} {b : Bool}

namespace Dispatch

theorem step_accepted_iff : (step p s e).2.accepted = true ↔
    stepEnvelope s e = none ∧ (stepHandle p s e).2.accepted = true := by
  unfold step
  split
  · simp_all [Verdict.accepted]
  · split <;> simp_all [Verdict.accepted]

theorem step_claimed_iff : (step p s e).2.claimed = true ↔
    stepEnvelope s e = none ∧ (stepHandle p s e).2.claimed = true := by
  unfold step
  split
  · simp_all [Verdict.claimed]
  · split <;> simp_all [Verdict.claimed]

theorem stepHandle_dispatch (he : e.body = .dispatch k n dg cost g key) :
    stepHandle p s e = handleDispatch p s e.time k n dg cost g key := by
  simp only [stepHandle, he]

theorem stage_authorized (hs : ¬(c.status ≠ .authorized ∧ (!(c.status == .unknown)) = true))
    (hu : c.status ≠ .unknown) : c.status = .authorized :=
  Classical.byContradiction fun ha => hs ⟨ha, by rw [beq_false_of_ne hu]; rfl⟩

theorem stage_active (hs : ¬(c.status ≠ .authorized ∧ (!(c.status == .unknown)) = true)) :
    c.status = .authorized ∨ c.status = .unknown :=
  (Classical.em (c.status = .unknown)).symm.imp (stage_authorized hs) id

/-- `handle_accepted` and `handle_claimed` in one: `f` reads the verdict and refuses every
rejection. -/
theorem handle_iff {f : Verdict → Bool} (hf : ∀ x, f (.rejected x) = false) :
    f (handleDispatch p s t k n dg cost g key).2 = true ↔
      ∃ c, s.calls[k]? = some c ∧ ¬(c.status ≠ .authorized ∧ (!(c.status == .unknown)) = true) ∧
        dispatchProtocol s ((p.action? c.tool).getD {}) c (c.status == .unknown) n dg cost key =
          none ∧
        match p.modeOf c.tool,
            dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g with
        | .enforce, some (x, some _) =>
          c.status = .authorized ∧ f (.ok (.dispatchDenied x) none) = true
        | .enforce, some (_, none) => False
        | _, d => f (.ok .dispatchClaimed (d.map fun (x, _) => .wouldDeny x)) = true := by
  unfold handleDispatch
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hk : s.calls[k]? with
  | none => simp only [hf, Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
  | some c =>
    simp only [Option.some.injEq, exists_eq_left']
    split
    next hs =>
      exact iff_of_false (by simp only [hf, Bool.false_eq_true, not_false_eq_true]) fun h => h.1 hs
    next hs =>
      simp only [hs, not_false_eq_true, true_and]
      split
      next hp => simp only [hf, hp, Bool.false_eq_true, reduceCtorEq, false_and]
      next hp =>
        simp only [hp, true_and]
        cases p.modeOf c.tool with
        | logOnly =>
          rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
            with _ | ⟨x, _ | st⟩ <;> exact Iff.rfl
        | enforce =>
          rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
            with _ | ⟨x, _ | st⟩
          · exact Iff.rfl
          · simp only [hf, Bool.false_eq_true]
          · by_cases hu : c.status = .unknown
            · simp only [hu, beq_self_eq_true, ite_true, hf, Bool.false_eq_true, reduceCtorEq,
                false_and]
            · simp only [stage_authorized hs hu, true_and]
              exact Iff.rfl

theorem handle_accepted : (handleDispatch p s t k n dg cost g key).2.accepted = true ↔
    ∃ c, s.calls[k]? = some c ∧ ¬(c.status ≠ .authorized ∧ (!(c.status == .unknown)) = true) ∧
      dispatchProtocol s ((p.action? c.tool).getD {}) c (c.status == .unknown) n dg cost key =
        none ∧
      (p.modeOf c.tool = .enforce →
        dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g = none ∨
        (c.status = .authorized ∧ ∃ x st, dispatchDenial p s t k ((p.action? c.tool).getD {}) c
          (c.status == .unknown) g = some (x, some st))) := by
  rw [handle_iff (f := Verdict.accepted) fun _ => rfl]
  refine exists_congr fun c => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  cases p.modeOf c.tool with
  | logOnly =>
    rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
      with _ | ⟨x, _ | st⟩ <;> exact iff_of_true rfl nofun
  | enforce =>
    rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
      with _ | ⟨x, _ | st⟩
    · exact iff_of_true rfl fun _ => .inl rfl
    · exact iff_of_false id fun h => by obtain h | ⟨-, _, _, h⟩ := h rfl <;> cases h
    · exact ⟨fun ⟨ha, _⟩ _ => .inr ⟨ha, x, st, rfl⟩,
        fun h => (h rfl).elim nofun fun ⟨ha, _⟩ => ⟨ha, rfl⟩⟩

theorem handle_claimed : (handleDispatch p s t k n dg cost g key).2.claimed = true ↔
    ∃ c, s.calls[k]? = some c ∧ ¬(c.status ≠ .authorized ∧ (!(c.status == .unknown)) = true) ∧
      dispatchProtocol s ((p.action? c.tool).getD {}) c (c.status == .unknown) n dg cost key =
        none ∧
      (p.modeOf c.tool = .enforce →
        dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g = none) := by
  rw [handle_iff (f := Verdict.claimed) fun _ => rfl]
  refine exists_congr fun c => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  cases p.modeOf c.tool with
  | logOnly =>
    rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
      with _ | ⟨x, _ | st⟩ <;> exact iff_of_true rfl nofun
  | enforce =>
    rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
      with _ | ⟨x, _ | st⟩
    · exact iff_of_true rfl fun _ => rfl
    · exact iff_of_false id fun h => nomatch h rfl
    · exact iff_of_false (fun h => nomatch h.2) fun h => nomatch h rfl

theorem handle_post (h : (handleDispatch p s t k n dg cost g key).2.claimed = true)
    (hc : s.calls[k]? = some c) :
    (handleDispatch p s t k n dg cost g key).1 =
      claim p s t k c ((p.action? c.tool).getD {}) (c.status == .unknown) key := by
  obtain ⟨c', hc', hs, hp, hd⟩ := handle_claimed.mp h
  rw [hc, Option.some.injEq] at hc'
  subst hc'
  unfold handleDispatch
  rw [Std.ExtTreeMap.get?_eq_getElem?, hc]
  dsimp only
  simp only [hs, ↓reduceIte, hp]
  cases hm : p.modeOf c.tool with
  | logOnly =>
    rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
      with _ | ⟨x, _ | st⟩ <;> rfl
  | enforce => rw [hd hm]

theorem denial_status (h : dispatchDenial p s t k r c b g = some (x, some st)) :
    st = .expired ∨ ∃ y, st = .deniedAtDispatch y := by
  unfold dispatchDenial at h
  split at h
  next hd =>
    cases h
    unfold authorizedDenial at hd
    repeat' split at hd
    all_goals (cases hd; try first | exact .inl rfl | exact .inr ⟨_, rfl⟩)
  · repeat' split at h
    all_goals first | cases h | (dsimp only at h; simp at h)

theorem handle_unclaimed (h : (handleDispatch p s t k n dg cost g key).2.claimed = false) :
    (handleDispatch p s t k n dg cost g key).1 = s ∨
      ∃ c st, s.calls[k]? = some c ∧ c.status = .authorized ∧
        (st = .expired ∨ ∃ x, st = .deniedAtDispatch x) ∧
        (handleDispatch p s t k n dg cost g key).1 = s.endCall k st := by
  revert h
  unfold handleDispatch
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hk : s.calls[k]? with
  | none => exact fun _ => .inl rfl
  | some c =>
    dsimp only
    split
    · exact fun _ => .inl rfl
    next hs =>
      split
      · exact fun _ => .inl rfl
      · cases p.modeOf c.tool with
        | logOnly =>
          rcases dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
            with _ | ⟨x, _ | st⟩ <;> exact nofun
        | enforce =>
          rcases hd : dispatchDenial p s t k ((p.action? c.tool).getD {}) c (c.status == .unknown) g
            with _ | ⟨x, _ | st⟩
          · exact nofun
          · exact fun _ => .inl rfl
          · by_cases hu : c.status = .unknown
            · exact fun _ => .inl (by simp only [hu, beq_self_eq_true, ↓reduceIte])
            · simp only [beq_false_of_ne hu, Bool.false_eq_true, ite_false]
              exact fun _ => .inr ⟨c, st, rfl, stage_authorized hs hu, denial_status hd, rfl⟩

theorem handle_cases :
    (handleDispatch p s t k n dg cost g key).1 = s ∨
      (∃ c st, s.calls[k]? = some c ∧ c.status = .authorized ∧
        (st = .expired ∨ ∃ x, st = .deniedAtDispatch x) ∧
        (handleDispatch p s t k n dg cost g key).1 = s.endCall k st) ∨
      ∃ c, s.calls[k]? = some c ∧ (c.status = .authorized ∨ c.status = .unknown) ∧
        (handleDispatch p s t k n dg cost g key).1 =
          claim p s t k c ((p.action? c.tool).getD {}) (c.status == .unknown) key := by
  cases hc : (handleDispatch p s t k n dg cost g key).2.claimed
  · exact (handle_unclaimed hc).imp_right .inl
  · obtain ⟨c, hk, hs, -⟩ := handle_claimed.mp hc
    exact .inr (.inr ⟨c, hk, stage_active hs, handle_post hc hk⟩)

theorem any_ne {α : Type _} {o : Option α} {f : α → Bool} :
    ¬ o.any f = true ↔ ∀ a, o = some a → f a = false := by
  cases o <;> simp

theorem protocol_iff :
    (¬(c.status ≠ .authorized ∧ (!(c.status == .unknown)) = true) ∧
      dispatchProtocol s r c (c.status == .unknown) n dg cost key = none) ↔
    ProtocolOk s r c n dg cost key := by
  unfold dispatchProtocol ProtocolOk
  simp only [Envelope.ite_none, any_ne]
  by_cases hu : c.status = .unknown
  · simp [hu, and_assoc]
  · simp [hu]

theorem validAt_iff {gr : GrantRec} :
    gr.validAt s t = true ↔ gr.revoked = false ∧ gr.epoch = s.epoch ∧
      (∀ nb, gr.notBefore = some nb → nb ≤ t) ∧ (∀ x, gr.expiresAt = some x → t < x) ∧
      (gr.scope = .turn → s.turnActive = true ∧ gr.turn = s.turnIndex) := by
  unfold GrantRec.validAt
  cases hn : gr.notBefore <;> cases hx : gr.expiresAt <;> cases hs : gr.scope <;>
    simp [and_assoc]

theorem auth_iff : authorizedDenial p s t r c b = none ↔ AuthOk p s t r c (b = true) := by
  unfold authorizedDenial AuthOk
  simp only [Envelope.ite_none, any_ne, and_true, Std.ExtTreeMap.get?_eq_getElem?]
  refine and_congr (forall_congr' fun _ => imp_congr_right fun _ => by simp)
    (and_congr (forall_congr' fun _ => imp_congr_right fun _ => by simp)
      (and_congr (by cases b <;> simp) (forall_congr' fun gid => imp_congr_right fun _ => ?_)))
  cases s.grants[gid]? <;> simp [validAt_iff]

theorem stale_iff {ms : List String} {m : String} :
    m ∈ s.staleMeters p t ms k ↔ m ∈ ms ∧ Stale p s t m k := by
  unfold State.staleMeters Stale State.entry?
  rw [List.mem_filter, Usage.meterEntries_eq]
  refine and_congr_right fun _ => ?_
  show _ ↔ ∀ en, (entriesOf p s m).find? (·.isFor m s.sessionId k) = some en → _
  generalize (entriesOf p s m).find? (·.isFor m s.sessionId k) = o
  cases p.meter? m <;> cases o <;> simp [MeterSpec.inWindow, Usage.inWindowAt_eq]

theorem shape_iff {spec : MeterSpec} :
    costShapeDenial spec cost = none ↔ ∀ cur, spec.unit = .money cur → ∃ cc, cost = some cc ∧
      cc.currency = cur ∧ ∀ mx, spec.maxPerCall = some mx → cc.amount ≤ mx := by
  unfold costShapeDenial
  cases spec.unit with
  | calls => simp
  | money cur =>
    cases cost with
    | none => simp
    | some cc =>
      by_cases h1 : cc.currency = cur
      · cases spec.maxPerCall <;> simp [h1]
      · simp [h1]

theorem fits_iff {m : String} :
    meterShapeDenial p m cost = none ∧ s.hasRoom p t m cost = true ↔ MeterFits p s t m cost := by
  unfold meterShapeDenial State.hasRoom MeterFits
  cases p.meter? m with
  | none => simp
  | some spec =>
    simp only [Option.some.injEq, exists_eq_left']
    refine and_congr shape_iff ?_
    rw [← usageAt_eq, Usage.meterEntries_eq, Usage.amount_eq]
    cases spec.cap <;> simp

theorem meters_iff {ms : List String} :
    metersDenial p s t ms cost = none ↔ ∀ m ∈ ms, MeterFits p s t m cost := by
  have h : metersDenial p s t ms cost = none ↔
      (∀ m ∈ ms, meterShapeDenial p m cost = none) ∧ ∀ m ∈ ms, s.hasRoom p t m cost = true := by
    unfold metersDenial
    rw [← List.findSome?_eq_none_iff]
    split <;> simp_all
  rw [h]
  exact ⟨fun ⟨h1, h2⟩ m hm => fits_iff.mp ⟨h1 m hm, h2 m hm⟩,
    fun h => ⟨fun m hm => (fits_iff.mpr (h m hm)).1, fun m hm => (fits_iff.mpr (h m hm)).2⟩⟩

theorem denial_none : dispatchDenial p s t k r c b g = none ↔
    AuthOk p s t r c (b = true) ∧ ReadyOk p s t r c k (b = true) g := by
  unfold dispatchDenial
  rw [← auth_iff]
  cases authorizedDenial p s t r c b with
  | some v => simp
  | none =>
    simp only [true_and]
    unfold ReadyOk State.blocked
    simp only [Envelope.ite_none, Option.map_eq_none_iff, meters_iff, Bool.or_eq_true,
      decide_eq_true_eq, not_or, List.any_eq_true, not_exists, not_and, Classical.not_not,
      and_assoc]
    refine and_congr (by simp) (and_congr Iff.rfl (and_congr Iff.rfl ?_))
    cases b <;> simp [stale_iff]

theorem denial_terminal : (∃ x st, dispatchDenial p s t k r c b g = some (x, some st)) ↔
    ¬ AuthOk p s t r c (b = true) := by
  unfold dispatchDenial
  rw [← auth_iff]
  cases authorizedDenial p s t r c b with
  | some v => simp
  | none =>
    simp only [not_true_eq_false, iff_false, not_exists]
    intro x st
    repeat' split
    all_goals simp

end Dispatch

theorem dispatch_accepted_iff (he : e.body = .dispatch k n dg cost g key) :
    (step p s e).2.accepted = true ↔ EnvelopeOk s e ∧ ∃ c, s.calls[k]? = some c ∧
      ProtocolOk s ((p.action? c.tool).getD {}) c n dg cost key ∧
      (p.modeOf c.tool = .enforce →
        (AuthOk p s e.time ((p.action? c.tool).getD {}) c (c.status = .unknown) ∧
          ReadyOk p s e.time ((p.action? c.tool).getD {}) c k (c.status = .unknown) g) ∨
        (c.status = .authorized ∧
          ¬ AuthOk p s e.time ((p.action? c.tool).getD {}) c (c.status = .unknown))) := by
  rw [Dispatch.step_accepted_iff, envelope_iff, Dispatch.stepHandle_dispatch he,
    Dispatch.handle_accepted]
  refine and_congr_right fun _ => exists_congr fun c => and_congr_right fun _ => ?_
  rw [← and_assoc, Dispatch.protocol_iff]
  refine and_congr_right fun _ => imp_congr_right fun _ => ?_
  rw [Dispatch.denial_none, Dispatch.denial_terminal, beq_iff_eq]

theorem dispatch_claimed_iff (he : e.body = .dispatch k n dg cost g key) :
    (step p s e).2.claimed = true ↔ EnvelopeOk s e ∧ ∃ c, s.calls[k]? = some c ∧
      ProtocolOk s ((p.action? c.tool).getD {}) c n dg cost key ∧
      (p.modeOf c.tool = .enforce →
        AuthOk p s e.time ((p.action? c.tool).getD {}) c (c.status = .unknown) ∧
          ReadyOk p s e.time ((p.action? c.tool).getD {}) c k (c.status = .unknown) g) := by
  rw [Dispatch.step_claimed_iff, envelope_iff, Dispatch.stepHandle_dispatch he,
    Dispatch.handle_claimed]
  refine and_congr_right fun _ => exists_congr fun c => and_congr_right fun _ => ?_
  rw [← and_assoc, Dispatch.protocol_iff]
  refine and_congr_right fun _ => imp_congr_right fun _ => ?_
  rw [Dispatch.denial_none, beq_iff_eq]

theorem claim_post (h : (step p s e).2.claimed = true) (he : e.body = .dispatch k n dg cost g key)
    (hc : s.calls[k]? = some c) :
    (step p s e).1 = { claim p s e.time k c ((p.action? c.tool).getD {}) (c.status == .unknown) key
      with lastSeq := e.seq, lastTime := e.time, version := s.version + 1 } := by
  have hh := (Dispatch.step_claimed_iff.mp h).2
  rw [accepted_step (claimed_accepted h)]
  rw [Dispatch.stepHandle_dispatch he] at hh ⊢
  rw [Dispatch.handle_post hh hc]

namespace Dispatch

def guardAction : Requirements := { guards := ["ok"] }

def guardPolicy (mode : Mode) : Policy :=
  { actions := [("t", { guardAction with mode := some mode })] }

def guardOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [("ok", true)] []⟩ ]

def guardDispatch (ok : Bool) : Event :=
  ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" none [("ok", ok)] "k1"⟩

#guard decide (guardPolicy .enforce).WF
#guard decide (guardPolicy .logOnly).WF
#guard (guardPolicy .enforce).modeOf "t" == .enforce
#guard (guardPolicy .logOnly).modeOf "t" == .logOnly
#guard ((after (guardPolicy .enforce) "pd" guardOpen).calls["c1"]?.map (·.status))
  == some .authorized
#guard ((after (guardPolicy .logOnly) "pd" guardOpen).calls["c1"]?.map (·.status))
  == some .authorized
#guard lookupFlag (match (guardDispatch false).body with | .dispatch _ _ _ _ g _ => g | _ => [])
  "ok" == some false
#guard (step (guardPolicy .enforce) (after (guardPolicy .enforce) "pd" guardOpen)
  (guardDispatch true)).2 == .ok .dispatchClaimed none
#guard (step (guardPolicy .enforce) (after (guardPolicy .enforce) "pd" guardOpen)
  (guardDispatch false)).2 == .rejected .guardFalse
#guard (step (guardPolicy .logOnly) (after (guardPolicy .logOnly) "pd" guardOpen)
  (guardDispatch false)).2 == .ok .dispatchClaimed (some (.wouldDeny .guardFalse))

def ttlPolicy : Policy := { limits := { authorizedTtlMs := some 10 }, actions := [("t", {})] }

def ttlOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩ ]

/-- Time 13 is the authorization time 3 plus the TTL 10, the first instant outside it. -/
def lateDispatch : Event := ⟨4, 13, 3, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

#guard decide ttlPolicy.WF
#guard ttlPolicy.authorizedTtl {} == some 10
#guard ((after ttlPolicy "pd" ttlOpen).calls["c1"]?).any fun c =>
  c.status == .authorized && c.attempts == 0 && c.authorizedAt == some 3
#guard (step ttlPolicy (after ttlPolicy "pd" ttlOpen) lateDispatch).2
  == .ok (.dispatchDenied .authorizationExpired) none
#guard ((step ttlPolicy (after ttlPolicy "pd" ttlOpen) lateDispatch).1.calls["c1"]?.map (·.status))
  == some .expired
#guard (step ttlPolicy (after ttlPolicy "pd" ttlOpen) { lateDispatch with time := 12 }).2.claimed

def retryTtlPolicy : Policy :=
  { limits := { authorizedTtlMs := some 10 }
    actions := [("t", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 })] }

def retryTtlOpen : List Event :=
  ttlOpen ++
    [⟨4, 4, 3, none, .dispatch "c1" 1 "d1" none [] "k1"⟩, ⟨5, 5, 4, none, .outcomeUnknown "c1"⟩]

/-- Time 13 is the authorization time 3 plus the TTL 10: a retry is held to the same TTL. -/
def lateRetry : Event := ⟨6, 13, 5, none, .dispatch "c1" 2 "d1" none [] "k1"⟩

#guard decide retryTtlPolicy.WF
#guard (trace retryTtlPolicy (State.initial "pd") retryTtlOpen).all (·.2.2.accepted)
#guard ((after retryTtlPolicy "pd" retryTtlOpen).calls["c1"]?).any fun c =>
  c.status == .unknown && c.attempts == 1 && c.authorizedAt == some 3
#guard (step retryTtlPolicy (after retryTtlPolicy "pd" retryTtlOpen)
  { lateRetry with time := 12 }).2 == .ok .dispatchClaimed none
#guard (step retryTtlPolicy (after retryTtlPolicy "pd" retryTtlOpen) lateRetry).2
  == .rejected .authorizationExpired
#guard ((step retryTtlPolicy (after retryTtlPolicy "pd" retryTtlOpen) lateRetry).1.calls["c1"]?.map
  (·.status)) == some .unknown

end Dispatch

end Writ.Proofs
