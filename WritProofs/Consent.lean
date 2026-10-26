import WritProofs.Calls
import WritProofs.ConsentMeaning
import WritProofs.Dispatch

namespace Writ.Proofs

open Writ
open Basic Calls ConsentMeaning

variable {p : Policy} {d : String} {s s' s₁ s₂ : State} {e : Event} {k : String} {c c' : CallRec}
  {tally : List (String × String)} {cs : Consent}

/-- Section 8, theorem 1(b) at dispatch: a single-approval consent, every fired escalator
grantable, and a grant for this call and digest, created by an approver eligible for every clause,
that is valid at `time`. -/
def GrantCovers (p : Policy) (s : State) (time : Nat) (c : CallRec) : Prop :=
  c.consent.single = true ∧
  (∀ r, p.action? c.tool = some r → ∀ n esc, (n, esc) ∈ r.escalate →
    c.proposedEscalators.lookup n ≠ some false → esc.grantable = true) ∧
  ∃ gid g, c.grant = some gid ∧ s.grants[gid]? = some g ∧ g.tool = c.tool ∧
    g.digest.all (· == c.digest) ∧
    (∀ cl ∈ c.consent.clauses, EligibleFor p s cl (g.principal, g.approver)) ∧
    g.revoked = false ∧ g.epoch = s.epoch ∧ (∀ nb, g.notBefore = some nb → nb ≤ time) ∧
    (∀ x, g.expiresAt = some x → time < x) ∧
    (g.scope = .turn → s.turnActive = true ∧ g.turn = s.turnIndex)

namespace Consent

theorem any_congr_mem {α : Type _} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr_mem fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem eligibleFor_congr {a : String} {cl : Clause} (ha : s'.approvers[a]? = s.approvers[a]?)
    (hr : s'.requester = s.requester) : s'.eligibleFor p cl a = s.eligibleFor p cl a := by
  unfold State.eligibleFor
  rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.get?_eq_getElem?, ha, hr]

/-- As in `assign_sound`, `f` and `f'` stand for the private `State.assign` at `s` and `s'`. -/
theorem assign_congr
    (hag : ∀ cl w, w ∈ tally → s'.eligibleFor p cl w.2 = s.eligibleFor p cl w.2)
    (f f' : List Clause → List (String × String) → Bool)
    (hnil : ∀ a, f [] a = true) (hnil' : ∀ a, f' [] a = true)
    (hstep : ∀ cl rest avail, f (cl :: rest) avail =
      (let principals := (avail.map (·.1)).eraseDups
       let room (c : Clause) :=
         ((avail.filter (s.eligibleFor p c ·.2)).map (·.1)).eraseDups.length ≥ (cl :: rest).count c
       (cl :: rest).length ≤ principals.length && (cl :: rest).all room &&
         principals.any fun who =>
           avail.any (fun (w, a) => w == who && s.eligibleFor p cl a) &&
             f rest (avail.filter (·.1 != who))))
    (hstep' : ∀ cl rest avail, f' (cl :: rest) avail =
      (let principals := (avail.map (·.1)).eraseDups
       let room (c : Clause) :=
         ((avail.filter (s'.eligibleFor p c ·.2)).map (·.1)).eraseDups.length ≥ (cl :: rest).count c
       (cl :: rest).length ≤ principals.length && (cl :: rest).all room &&
         principals.any fun who =>
           avail.any (fun (w, a) => w == who && s'.eligibleFor p cl a) &&
             f' rest (avail.filter (·.1 != who)))) :
    ∀ (slots : List Clause) (avail : List (String × String)), (∀ w ∈ avail, w ∈ tally) →
      f' slots avail = f slots avail := by
  intro slots
  induction slots with
  | nil => intro avail _; rw [hnil, hnil']
  | cons cl rest ih =>
    intro avail hsub
    rw [hstep, hstep']
    have hfilt : ∀ c : Clause, avail.filter (fun x => s'.eligibleFor p c x.2)
        = avail.filter (fun x => s.eligibleFor p c x.2) :=
      fun c => List.filter_congr fun w hw => hag c w (hsub w hw)
    have hany : ∀ who, avail.any (fun (w, a) => w == who && s'.eligibleFor p cl a)
        = avail.any (fun (w, a) => w == who && s.eligibleFor p cl a) := by
      intro who
      refine any_congr_mem fun ⟨w, a⟩ hw => ?_
      dsimp only
      rw [hag cl (w, a) (hsub _ hw)]
    have hrec : ∀ who, f' rest (avail.filter (·.1 != who)) = f rest (avail.filter (·.1 != who)) :=
      fun who => ih _ fun w hw => hsub w (List.mem_filter.mp hw).1
    simp only [hfilt, hany, hrec]

theorem satisfied_congr
    (hag : ∀ cl w, w ∈ tally → s'.eligibleFor p cl w.2 = s.eligibleFor p cl w.2) :
    s'.satisfied p cs tally = s.satisfied p cs tally := by
  unfold State.satisfied
  refine List.all_congr rfl fun g => ?_
  split
  · exact assign_congr hag _ _ (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      _ _ fun w hw => hw
  · refine List.all_congr rfl fun cl => ?_
    rw [List.filter_congr fun w hw => hag cl w hw]

end Consent

open Proofs.Consent

/-- A status from which a call may still be claimed, or has been. -/
def Active (st : CallStatus) : Prop := st = .authorized ∨ st = .dispatched ∨ st = .unknown

def GrantAttested (s : State) (g : GrantRec) : Prop :=
  ∃ info, s.approvers[g.approver]? = some info ∧ info.principal = g.principal

/-- `GrantCovers` without the validity at dispatch time, which a revoke, reset or turn end can
take away from a call that stays Authorized. -/
def GrantFacts (p : Policy) (s : State) (c : CallRec) : Prop :=
  c.consent.single = true ∧
  (∀ r, p.action? c.tool = some r → ∀ n esc, (n, esc) ∈ r.escalate →
    c.proposedEscalators.lookup n ≠ some false → esc.grantable = true) ∧
  ∃ gid g, c.grant = some gid ∧ s.grants[gid]? = some g ∧ g.tool = c.tool ∧
    g.digest.all (· == c.digest) ∧
    ∀ cl ∈ c.consent.clauses, EligibleFor p s cl (g.principal, g.approver)

namespace Consent

def RecOk (p : Policy) (s : State) (c : CallRec) : Prop :=
  TallyAttested s c.tally ∧ (c.status = .awaiting → c.grant = none) ∧
  (p.modeOf c.tool = .enforce → Active c.status → c.consent.clauses ≠ [] →
    (c.grant = none → s.satisfied p c.consent c.tally = true) ∧
    (c.grant ≠ none → GrantFacts p s c))

/-- What a step may do to a call record without new consent: change its status, attempts, key or
reconciliation, but never move it into Awaiting or into a claimable status. -/
structure RecSame (c c' : CallRec) : Prop where
  tool : c'.tool = c.tool
  consent : c'.consent = c.consent
  tally : c'.tally = c.tally
  grant : c'.grant = c.grant
  digest : c'.digest = c.digest
  escalators : c'.proposedEscalators = c.proposedEscalators
  active : Active c'.status → Active c.status
  awaiting : c'.status = .awaiting → c.status = .awaiting
  generation : c'.generation = c.generation
  cost : c'.cost = c.cost
  requestedAt : c'.requestedAt = c.requestedAt
  authorizedAt : c'.authorizedAt = c.authorizedAt
  proposedDigest : c'.proposedDigest = c.proposedDigest
  proposedCost : c'.proposedCost = c.proposedCost
  generations : c'.generations = c.generations

def GrantSame (g g' : GrantRec) : Prop :=
  g'.approver = g.approver ∧ g'.principal = g.principal ∧ g'.tool = g.tool ∧ g'.digest = g.digest

/-- `s'` keeps what the consent invariant reads from `s`: attested approvers, the requester,
grant identities and call records up to `RecSame`. -/
structure Keeps (s s' : State) : Prop where
  approvers : ∀ (a : String) (i : ApproverInfo),
    s.approvers[a]? = some i → s'.approvers[a]? = some i
  requester : s'.requester = s.requester
  started : s'.started = s.started
  grantsFwd : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g →
    ∃ g', s'.grants[gid]? = some g' ∧ GrantSame g g'
  grantsBack : ∀ (gid : String) (g' : GrantRec), s'.grants[gid]? = some g' →
    ∃ g, s.grants[gid]? = some g ∧ GrantSame g g'
  calls : ∀ (k : String) (c' : CallRec), s'.calls[k]? = some c' →
    ∃ c, s.calls[k]? = some c ∧ RecSame c c'

theorem RecSame.refl : RecSame c c :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, id, id, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RecSame.trans {c'' : CallRec} (h : RecSame c c') (h' : RecSame c' c'') :
    RecSame c c'' where
  tool := h'.tool.trans h.tool
  consent := h'.consent.trans h.consent
  tally := h'.tally.trans h.tally
  grant := h'.grant.trans h.grant
  digest := h'.digest.trans h.digest
  escalators := h'.escalators.trans h.escalators
  active a := h.active (h'.active a)
  awaiting a := h.awaiting (h'.awaiting a)
  generation := h'.generation.trans h.generation
  cost := h'.cost.trans h.cost
  requestedAt := h'.requestedAt.trans h.requestedAt
  authorizedAt := h'.authorizedAt.trans h.authorizedAt
  proposedDigest := h'.proposedDigest.trans h.proposedDigest
  proposedCost := h'.proposedCost.trans h.proposedCost
  generations := h'.generations.trans h.generations

theorem RecSame.status {st : CallStatus} (h : Active st → Active c.status)
    (h' : st = .awaiting → c.status = .awaiting) : RecSame c { c with status := st } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, h, h', rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def Closed (st : CallStatus) : Prop := ¬Active st ∧ st ≠ .awaiting

theorem RecSame.closed {st : CallStatus} (h : Closed st) : RecSame c { c with status := st } :=
  .status (fun a => absurd a h.1) (fun a => absurd a h.2)

theorem GrantSame.refl {g : GrantRec} : GrantSame g g := ⟨rfl, rfl, rfl, rfl⟩

theorem GrantSame.trans {g g' g'' : GrantRec} (h : GrantSame g g') (h' : GrantSame g' g'') :
    GrantSame g g'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

theorem Keeps.refl : Keeps s s :=
  ⟨fun _ _ h => h, rfl, rfl, fun _ g h => ⟨g, h, .refl⟩, fun _ g h => ⟨g, h, .refl⟩,
   fun _ c h => ⟨c, h, .refl⟩⟩

theorem Keeps.trans (h : Keeps s s₁) (h' : Keeps s₁ s₂) : Keeps s s₂ where
  approvers a i hi := h'.approvers a i (h.approvers a i hi)
  requester := h'.requester.trans h.requester
  started := h'.started.trans h.started
  grantsFwd gid g hg := by
    obtain ⟨g₁, h₁, hs₁⟩ := h.grantsFwd gid g hg
    obtain ⟨g₂, h₂, hs₂⟩ := h'.grantsFwd gid g₁ h₁
    exact ⟨g₂, h₂, hs₁.trans hs₂⟩
  grantsBack gid g hg := by
    obtain ⟨g₁, h₁, hs₁⟩ := h'.grantsBack gid g hg
    obtain ⟨g₂, h₂, hs₂⟩ := h.grantsBack gid g₁ h₁
    exact ⟨g₂, h₂, hs₂.trans hs₁⟩
  calls k c hc := by
    obtain ⟨c₁, h₁, hs₁⟩ := h'.calls k c hc
    obtain ⟨c₂, h₂, hs₂⟩ := h.calls k c₁ h₁
    exact ⟨c₂, h₂, hs₂.trans hs₁⟩

theorem Keeps.of_eq (ha : s'.approvers = s.approvers) (hr : s'.requester = s.requester)
    (hs : s'.started = s.started) (hg : s'.grants = s.grants) (hc : s'.calls = s.calls) :
    Keeps s s' := by
  refine ⟨fun a i h => ?_, hr, hs, fun gid g h => ⟨g, ?_, .refl⟩,
    fun gid g h => ⟨g, ?_, .refl⟩, fun k c h => ⟨c, ?_, .refl⟩⟩
  · rw [ha]; exact h
  · rw [hg]; exact h
  · rw [← hg]; exact h
  · rw [← hc]; exact h

/-- `h.with ..` extends `h` by a record update that leaves the consent fields alone. -/
theorem Keeps.with (h : Keeps s s₁) (ha : s'.approvers = s₁.approvers)
    (hr : s'.requester = s₁.requester) (hs : s'.started = s₁.started)
    (hg : s'.grants = s₁.grants) (hc : s'.calls = s₁.calls) : Keeps s s' :=
  h.trans (.of_eq ha hr hs hg hc)

theorem Keeps.grants_insert {gid : String} {g g' : GrantRec} (hg : s.grants[gid]? = some g)
    (hs : GrantSame g g') : Keeps s { s with grants := s.grants.insert gid g' } := by
  refine ⟨fun _ _ h => h, rfl, rfl, fun x gx hx => ?_, fun x gx hx => ?_,
    fun k c h => ⟨c, h, .refl⟩⟩
  · simp only [Std.ExtTreeMap.getElem?_insert]
    split
    next he =>
      cases Std.LawfulEqCmp.eq_of_compare he
      rw [hg] at hx; cases hx
      exact ⟨g', rfl, hs⟩
    · exact ⟨gx, hx, .refl⟩
  · simp only [Std.ExtTreeMap.getElem?_insert] at hx
    split at hx
    next he =>
      cases Std.LawfulEqCmp.eq_of_compare he
      cases hx
      exact ⟨g, hg, hs⟩
    · exact ⟨gx, hx, .refl⟩

theorem Keeps.grants_map {f : String → GrantRec → GrantRec}
    (hf : ∀ k g, GrantSame g (f k g)) :
    Keeps s { s with grants := s.grants.map f } := by
  refine ⟨fun _ _ h => h, rfl, rfl, fun x gx hx => ?_, fun x gx hx => ?_,
    fun k c h => ⟨c, h, .refl⟩⟩
  · simp only [Std.ExtTreeMap.getElem?_map, hx, Option.map_some]
    exact ⟨_, rfl, hf x gx⟩
  · simp only [Std.ExtTreeMap.getElem?_map] at hx
    cases hk : s.grants[x]? with
    | none => simp [hk] at hx
    | some g =>
      simp only [hk, Option.map_some, Option.some.injEq] at hx; subst hx; exact ⟨g, rfl, hf x g⟩

theorem Keeps.grants_modify {gid : String} {f : GrantRec → GrantRec}
    (hf : ∀ g, GrantSame g (f g)) :
    Keeps s { s with grants := s.grants.modify gid f } := by
  refine ⟨fun _ _ h => h, rfl, rfl, fun x gx hx => ?_, fun x gx hx => ?_,
    fun k c h => ⟨c, h, .refl⟩⟩
  · simp only [Std.ExtTreeMap.getElem?_modify]
    split
    next he =>
      cases Std.LawfulEqCmp.eq_of_compare he
      rw [hx]; exact ⟨_, rfl, hf gx⟩
    · exact ⟨gx, hx, .refl⟩
  · simp only [Std.ExtTreeMap.getElem?_modify] at hx
    split at hx
    next he =>
      cases Std.LawfulEqCmp.eq_of_compare he
      cases hk : s.grants[gid]? with
      | none => simp [hk] at hx
      | some g =>
        simp only [hk, Option.map_some, Option.some.injEq] at hx; subst hx; exact ⟨g, rfl, hf g⟩
    · exact ⟨gx, hx, .refl⟩

theorem Keeps.calls_insert (hk : s.calls[k]? = some c) (hr : RecSame c c') :
    Keeps s { s with calls := s.calls.insert k c' } := by
  refine ⟨fun _ _ h => h, rfl, rfl, fun _ g h => ⟨g, h, .refl⟩, fun _ g h => ⟨g, h, .refl⟩,
    fun x cx hx => ?_⟩
  simp only [Std.ExtTreeMap.getElem?_insert] at hx
  split at hx
  next he =>
    cases Std.LawfulEqCmp.eq_of_compare he
    cases hx
    exact ⟨c, hk, hr⟩
  · exact ⟨cx, hx, .refl⟩

theorem Keeps.calls_modify {f : CallRec → CallRec} (hf : ∀ c, RecSame c (f c)) :
    Keeps s { s with calls := s.calls.modify k f } := by
  refine ⟨fun _ _ h => h, rfl, rfl, fun _ g h => ⟨g, h, .refl⟩, fun _ g h => ⟨g, h, .refl⟩,
    fun x cx hx => ?_⟩
  simp only [Std.ExtTreeMap.getElem?_modify] at hx
  split at hx
  next he =>
    cases Std.LawfulEqCmp.eq_of_compare he
    cases hk : s.calls[k]? with
    | none => simp [hk] at hx
    | some c =>
      simp only [hk, Option.map_some, Option.some.injEq] at hx; subst hx; exact ⟨c, rfl, hf c⟩
  · exact ⟨cx, hx, .refl⟩

theorem Keeps.calls_map {f : String → CallRec → CallRec} (hf : ∀ k c, RecSame c (f k c)) :
    Keeps s { s with calls := s.calls.map f } := by
  refine ⟨fun _ _ h => h, rfl, rfl, fun _ g h => ⟨g, h, .refl⟩, fun _ g h => ⟨g, h, .refl⟩,
    fun x cx hx => ?_⟩
  simp only [Std.ExtTreeMap.getElem?_map] at hx
  cases hk : s.calls[x]? with
  | none => simp [hk] at hx
  | some c =>
    simp only [hk, Option.map_some, Option.some.injEq] at hx; subst hx; exact ⟨c, rfl, hf x c⟩

theorem Keeps.grants_insert' {gid : String} {g g' : GrantRec} (hg : s.grants.get? gid = some g)
    (hs : GrantSame g g') : Keeps s { s with grants := s.grants.insert gid g' } :=
  Keeps.grants_insert (by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hg) hs

theorem releaseGrant_keeps : Keeps s (s.releaseGrant k) := by
  unfold State.releaseGrant
  repeat' split
  all_goals first
    | exact Keeps.refl
    | (rename_i hg; exact Keeps.grants_insert' hg ⟨rfl, rfl, rfl, rfl⟩)

theorem consumeGrant_keeps : Keeps s (s.consumeGrant k) := by
  unfold State.consumeGrant
  repeat' split
  all_goals first
    | exact Keeps.refl
    | (rename_i hg; exact Keeps.grants_insert' hg ⟨rfl, rfl, rfl, rfl⟩)

theorem endCall_keeps {st : CallStatus} (h : Closed st) : Keeps s (s.endCall k st) := by
  unfold State.endCall
  exact releaseGrant_keeps.trans (Keeps.calls_modify fun _ => .closed h)

theorem closed_cancelled : Closed .cancelled := ⟨by simp [Active], by simp⟩

theorem cancelPending_keeps : Keeps s (cancelPending s) := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (Keeps s) ?_ _ _ Keeps.refl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact ha.trans (endCall_keeps closed_cancelled)
  · exact ha.trans (endCall_keeps closed_cancelled)
  · exact ha

theorem interrupt_keeps : Keeps s s.interrupt := by
  unfold State.interrupt
  refine (cancelPending_keeps.trans (Keeps.calls_map fun _ c => ?_)).trans
    (Keeps.grants_map fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
  split
  next hd =>
    exact .status (fun _ => by rw [hd]; simp [Active]) (by simp)
  · exact .refl

theorem updateEntries_keeps : Keeps s (s.updateEntries p m t f) := by
  unfold State.updateEntries; split <;> exact Keeps.of_eq rfl rfl rfl rfl rfl

theorem retime_keeps : Keeps s (s.retime p m k t) := updateEntries_keeps
theorem reserve_keeps : Keeps s (s.reserve p m k a t) := updateEntries_keeps

theorem settle_keeps : Keeps s (s.settle p ms k o a ne t).1 := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => Keeps s b.1) ?_ ms _ Keeps.refl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact h.trans updateEntries_keeps
  · split <;> exact h.trans updateEntries_keeps

theorem recordFailure_keeps : Keeps s (s.recordFailure p t) := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals exact Keeps.of_eq rfl rfl rfl rfl rfl

theorem recordSuccess_keeps : Keeps s (s.recordSuccess t) := Keeps.of_eq rfl rfl rfl rfl rfl

theorem claim_keeps {rc : CallRec} (hk : s.calls[k]? = some rc) (ha : Active rc.status) :
    Keeps s (Writ.claim p s t k rc r retry key) := by
  unfold Writ.claim
  have hr : RecSame rc
      { rc with status := .dispatched, attempts := rc.attempts + 1, idempotencyKey := some key } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ha, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  dsimp only
  split
  · have h₁ := foldl_invariant (Keeps s) (f := fun s m => s.retime p m k t)
      (fun b _ hb => hb.trans retime_keeps) (s.staleMeters p t r.meters k) s Keeps.refl
    have hc := foldl_calls (f := fun s m => s.retime p m k t) (fun _ _ => retime_calls)
      (s.staleMeters p t r.meters k) s
    exact h₁.trans ((Keeps.calls_insert (by rw [hc]; exact hk) hr).with rfl rfl rfl rfl rfl)
  · have h₁ := foldl_invariant (Keeps s)
      (f := fun s m => s.reserve p m k (p.callAmount m rc.cost) t)
      (fun b _ hb => hb.trans reserve_keeps) r.meters (s.consumeGrant k) consumeGrant_keeps
    have hc := foldl_calls (f := fun s m => s.reserve p m k (p.callAmount m rc.cost) t)
      (fun _ _ => reserve_calls) r.meters (s.consumeGrant k)
    exact h₁.trans ((Keeps.calls_insert (by rw [hc, consumeGrant_calls]; exact hk) hr).with
      rfl rfl rfl rfl rfl)

theorem closed_of {st : CallStatus} (h : st.terminal = true) (hu : st ≠ .unknown) : Closed st := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · rcases ha with ha | ha | ha <;> subst ha <;> first | exact hu rfl | cases h
  · subst ha; cases h

local macro "closed" : tactic => `(tactic| exact closed_of (by rfl) (by simp))

theorem closed_of_denial {st : CallStatus} (h : st = .expired ∨ ∃ x, st = .deniedAtDispatch x) :
    Closed st := by
  rcases h with rfl | ⟨_, rfl⟩ <;> closed

local macro "consent_keeps" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact Keeps.refl
      | exact Keeps.of_eq rfl rfl rfl rfl rfl
      | exact cancelPending_keeps.with rfl rfl rfl rfl rfl
      | exact interrupt_keeps.with rfl rfl rfl rfl rfl
      | exact (endCall_keeps (by closed)).with rfl rfl rfl rfl rfl)

theorem handleSessionEnd_kept : Keeps s (handleSessionEnd s).1 := by
  unfold handleSessionEnd; consent_keeps

theorem handleTurnStart_kept : Keeps s (handleTurnStart s u).1 := by
  unfold handleTurnStart; consent_keeps

theorem handleTurnEnd_kept : Keeps s (handleTurnEnd s).1 := by
  unfold handleTurnEnd
  split
  · exact Keeps.refl
  · exact (Keeps.grants_map fun _ g => by split <;> exact ⟨rfl, rfl, rfl, rfl⟩).with
      rfl rfl rfl rfl rfl

theorem handleStepStart_kept : Keeps s (handleStepStart p s).1 := by
  unfold handleStepStart; consent_keeps

theorem handleApproverAttest_kept : Keeps s (handleApproverAttest s a i).1 := by
  unfold handleApproverAttest
  split
  · exact Keeps.refl
  next hn =>
    refine ⟨fun a' i' h => ?_, rfl, rfl, fun _ g h => ⟨g, h, .refl⟩, fun _ g h => ⟨g, h, .refl⟩,
      fun _ c h => ⟨c, h, .refl⟩⟩
    dsimp only
    rw [Std.ExtTreeMap.getElem?_insert]
    split
    next he =>
      cases Std.LawfulEqCmp.eq_of_compare he
      rw [Std.ExtTreeMap.get?_eq_getElem?, h] at hn
      simp only [Option.any_some, bne_iff_ne, ne_eq, Classical.not_not] at hn
      rw [hn]
    · exact h

theorem handlePermissionRevoke_kept : Keeps s (handlePermissionRevoke s a).1 := by
  unfold handlePermissionRevoke; consent_keeps

theorem handleReject_kept : Keeps s (handleReject p s i r w).1 := by
  unfold handleReject; consent_keeps

theorem handleApprovalExpire_kept : Keeps s (handleApprovalExpire s i r).1 := by
  unfold handleApprovalExpire; consent_keeps

theorem handleGrantRevoke_kept : Keeps s (handleGrantRevoke s i).1 := by
  unfold handleGrantRevoke
  split
  · exact Keeps.refl
  next hg => exact Keeps.grants_insert' hg ⟨rfl, rfl, rfl, rfl⟩

theorem handleCancel_kept : Keeps s (handleCancel s i).1 := by
  unfold handleCancel; consent_keeps

theorem handleReset_kept : Keeps s (handleReset s).1 := by
  unfold handleReset; consent_keeps

theorem handleKill_kept : Keeps s (handleKill p s).1 := by
  unfold handleKill; consent_keeps

theorem handlePermissionAdd_kept : Keeps s (handlePermissionAdd p s a b).1 := by
  unfold handlePermissionAdd; consent_keeps

theorem handleEscalationAck_kept : Keeps s (handleEscalationAck p s a b).1 := by
  unfold handleEscalationAck; consent_keeps

theorem handleLedgerSync_kept : Keeps s (handleLedgerSync s l).1 := by
  unfold handleLedgerSync; consent_keeps

theorem withStatus_kept {rc : CallRec} {st : CallStatus} (hk : s.calls[k]? = some rc)
    (ha : rc.status = .dispatched) (hs : st ≠ .awaiting) : Keeps s (withStatus s k rc st) :=
  Keeps.calls_insert hk (.status (fun _ => by rw [ha]; simp [Active]) (fun h => absurd h hs))

theorem handleDispatch_kept : Keeps s (handleDispatch p s t i n dg cost g key).1 := by
  rcases Dispatch.handle_cases with he | ⟨-, st, -, -, hst, he⟩ | ⟨rc, hk, hs, he⟩ <;> rw [he]
  · exact Keeps.refl
  · exact endCall_keeps (closed_of_denial hst)
  · exact claim_keeps hk (by rcases hs with h | h <;> simp only [Active, h, true_or, or_true])

theorem handleResult_kept : Keeps s (handleResult p s t i o a ne).1 := by
  unfold handleResult
  split
  · exact Keeps.refl
  next rc hrc =>
    have hk : s.calls[i]? = some rc := by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hrc
    split
    · exact Keeps.refl
    next hd =>
      have hd : rc.status = .dispatched := Classical.not_not.mp hd
      have h₁ : Keeps s ((withStatus s i rc o.status).settle p (callMeters p rc) i o a ne t).1 :=
        (withStatus_kept hk hd (by cases o <;> simp [Outcome.status])).trans settle_keeps
      repeat' (first | (dsimp only) | split)
      all_goals first
        | exact h₁.trans recordFailure_keeps
        | exact h₁.trans recordSuccess_keeps
        | exact h₁

theorem handleOutcomeUnknown_kept : Keeps s (handleOutcomeUnknown p s i).1 := by
  unfold handleOutcomeUnknown
  split
  · exact Keeps.refl
  next rc hrc =>
    have hk : s.calls[i]? = some rc := by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hrc
    split
    · exact Keeps.refl
    next hd =>
      exact (withStatus_kept hk (Classical.not_not.mp hd) (by simp)).trans recordFailure_keeps

theorem handleReconcile_kept : Keeps s (handleReconcile p s t i o a ne).1 := by
  unfold handleReconcile
  split
  · exact Keeps.refl
  next rc hrc =>
    have hk : s.calls[i]? = some rc := by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hrc
    split
    · exact Keeps.refl
    · split
      · exact Keeps.refl
      · have h₁ : Keeps s { s with calls := s.calls.insert i { rc with reconciled := some o } } :=
          Keeps.calls_insert hk
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, id, id, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        repeat' (first | (dsimp only) | split)
        all_goals first
          | exact (h₁.trans settle_keeps).trans recordFailure_keeps
          | exact h₁.trans settle_keeps

structure PartiesKept (s s' : State) : Prop where
  approvers : ∀ (a : String) (i : ApproverInfo),
    s.approvers[a]? = some i → s'.approvers[a]? = some i
  requester : s'.requester = s.requester
  started : s'.started = s.started

theorem Keeps.parties (h : Keeps s s') : PartiesKept s s' := ⟨h.approvers, h.requester, h.started⟩

/-- The part of `ConsentInv` proved by induction; the rest holds of every state that has it. -/
structure ConsentCore (p : Policy) (s : State) : Prop where
  calls : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → RecOk p s c
  grants : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g → GrantAttested s g
  fresh : s.started = false →
    (∀ a : String, s.approvers[a]? = none) ∧ (∀ k : String, s.calls[k]? = none) ∧
      ∀ gid : String, s.grants[gid]? = none

end Consent

theorem EligibleFor.mono {cl : Clause} {w : String × String} (h : EligibleFor p s cl w)
    (ha : ∀ (a : String) (i : ApproverInfo), s.approvers[a]? = some i → s'.approvers[a]? = some i)
    (hr : s'.requester = s.requester) : EligibleFor p s' cl w := by
  obtain ⟨info, hi, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨info, ha _ _ hi, h₁, h₂, h₃, h₄, h₅, hr ▸ h₆⟩

theorem TallyAttested.mono (h : TallyAttested s tally)
    (ha : ∀ (a : String) (i : ApproverInfo), s.approvers[a]? = some i → s'.approvers[a]? = some i) :
    TallyAttested s' tally := fun w hw => by
  obtain ⟨info, hi, hp⟩ := h w hw
  exact ⟨info, ha _ _ hi, hp⟩

namespace Consent

theorem satisfied_mono (h : TallyAttested s tally)
    (ha : ∀ (a : String) (i : ApproverInfo), s.approvers[a]? = some i → s'.approvers[a]? = some i)
    (hr : s'.requester = s.requester) : s'.satisfied p cs tally = s.satisfied p cs tally :=
  satisfied_congr fun _ w hw => by
    obtain ⟨info, hi, _⟩ := h w hw
    exact eligibleFor_congr (by rw [hi, ha _ _ hi]) hr

theorem RecOk.transport (h : RecOk p s c) (hc : RecSame c c')
    (ha : ∀ (a : String) (i : ApproverInfo), s.approvers[a]? = some i → s'.approvers[a]? = some i)
    (hr : s'.requester = s.requester)
    (hg : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g →
      ∃ g', s'.grants[gid]? = some g' ∧ GrantSame g g') : RecOk p s' c' := by
  obtain ⟨htool, hcons, htally, hgrant, hdig, hesc, hact, hawait, -, -, -⟩ := hc
  obtain ⟨hatt, haw, hmain⟩ := h
  refine ⟨htally ▸ hatt.mono ha, fun hs => hgrant ▸ haw (hawait hs), fun hm hA hne => ?_⟩
  rw [htool] at hm
  rw [hcons] at hne
  obtain ⟨hq, hgf⟩ := hmain hm (hact hA) hne
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · rw [hcons, htally, satisfied_mono hatt ha hr]
    exact hq (hgrant ▸ hn)
  · obtain ⟨hsingle, hfired, gid, g, hgid, hsg, hgt, hgd, hel⟩ := hgf (hgrant ▸ hn)
    obtain ⟨g', hsg', hga, hgp, hgt', hgd'⟩ := hg gid g hsg
    refine ⟨hcons ▸ hsingle, htool ▸ hesc ▸ hfired, gid, g', hgrant ▸ hgid, hsg', ?_, ?_, ?_⟩
    · rw [hgt', hgt, htool]
    · rw [hgd', hdig]; exact hgd
    · intro cl hcl
      rw [hga, hgp]
      exact (hel cl (hcons ▸ hcl)).mono ha hr

theorem ConsentCore.update (h : ConsentCore p s) (hst : s'.started = true)
    (ha : ∀ (a : String) (i : ApproverInfo), s.approvers[a]? = some i → s'.approvers[a]? = some i)
    (hr : s'.requester = s.requester)
    (hgf : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g →
      ∃ g', s'.grants[gid]? = some g' ∧ GrantSame g g')
    (hgb : ∀ (gid : String) (g' : GrantRec), s'.grants[gid]? = some g' →
      (∃ g, s.grants[gid]? = some g ∧ GrantSame g g') ∨ GrantAttested s' g')
    (hc : ∀ (k : String) (c' : CallRec), s'.calls[k]? = some c' →
      (∃ c, s.calls[k]? = some c ∧ RecSame c c') ∨ RecOk p s' c') :
    ConsentCore p s' := by
  refine ⟨fun k c' hk => ?_, fun gid g' hg' => ?_, fun hf => absurd hst (by rw [hf]; nofun)⟩
  · rcases hc k c' hk with ⟨c, hk₀, hs⟩ | hok
    · exact (h.calls k c hk₀).transport hs ha hr hgf
    · exact hok
  · rcases hgb gid g' hg' with ⟨g, hg, hga, hgp, _, _⟩ | hatt
    · obtain ⟨info, hi, hp⟩ := h.grants gid g hg
      exact ⟨info, by rw [hga]; exact ha _ _ hi, by rw [hgp]; exact hp⟩
    · exact hatt

theorem ConsentCore.keeps (h : ConsentCore p s) (hs : s.started = true) (hk : Keeps s s') :
    ConsentCore p s' :=
  h.update (hk.started.trans hs) hk.approvers hk.requester hk.grantsFwd
    (fun gid g' hg => .inl (hk.grantsBack gid g' hg)) (fun k c' hc => .inl (hk.calls k c' hc))

theorem ConsentCore.of_empty (ha : s.started = false → ∀ a : String, s.approvers[a]? = none)
    (hc : ∀ k : String, s.calls[k]? = none) (hg : ∀ gid : String, s.grants[gid]? = none) :
    ConsentCore p s :=
  ⟨fun k c h => (by rw [hc k] at h; cases h), fun gid g h => (by rw [hg gid] at h; cases h),
   fun hf => ⟨ha hf, hc, hg⟩⟩

theorem PartiesKept.refl : PartiesKept s s := ⟨fun _ _ h => h, rfl, rfl⟩

theorem eligibleAll_contains (h : s.eligibleAll p cs a = none) : s.approvers.contains a = true := by
  unfold State.eligibleAll at h
  split at h
  · cases h
  next hc => simpa using hc

theorem eligibleAny_contains (h : s.eligibleAny p cs a = none) : s.approvers.contains a = true := by
  unfold State.eligibleAny at h
  split at h
  · cases h
  next hc => simpa using hc

theorem attested_of_contains (h : s.approvers.contains a = true) :
    ∃ info, s.approvers[a]? = some info ∧
      ((s.approvers.get? a).map (·.principal)).getD a = info.principal := by
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?] at h
  cases hi : s.approvers[a]? with
  | none => rw [hi] at h; cases h
  | some info => exact ⟨info, rfl, by rw [Std.ExtTreeMap.get?_eq_getElem?, hi]; rfl⟩

theorem grantDenial_none (h : grantDenial p s t gid a tool dg sc n mc ex = none) :
    s.grants[gid]? = none ∧ s.approvers.contains a = true := by
  unfold grantDenial at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals refine ⟨?_, eligibleAll_contains (by assumption)⟩
  all_goals
    have hc : ¬s.grants.contains gid = true := by assumption
    rw [Std.ExtTreeMap.contains_eq_isSome_getElem?] at hc
    cases hg : s.grants[gid]? with
    | none => rfl
    | some _ => rw [hg] at hc; exact absurd rfl hc

theorem ConsentCore.grantCreate (h : ConsentCore p s) (hs : s.started = true) :
    ConsentCore p (handleGrantCreate p s t gid a tool dg sc n mc nb ex rv).1 ∧
      PartiesKept s (handleGrantCreate p s t gid a tool dg sc n mc nb ex rv).1 := by
  unfold handleGrantCreate
  split
  · exact ⟨h, .refl⟩
  next hd =>
    obtain ⟨hgn, hac⟩ := grantDenial_none hd
    obtain ⟨info, hi, hp⟩ := attested_of_contains hac
    refine ⟨h.update hs (fun _ _ h => h) rfl (fun gid' g hg => ?_) (fun gid' g' hg => ?_)
      (fun k c hc => .inl ⟨c, hc, .refl⟩), fun _ _ h => h, rfl, rfl⟩
    · dsimp only
      rw [Std.ExtTreeMap.getElem?_insert]
      split
      next he =>
        cases Std.LawfulEqCmp.eq_of_compare he
        rw [hgn] at hg; cases hg
      · exact ⟨g, hg, .refl⟩
    · dsimp only at hg
      rw [Std.ExtTreeMap.getElem?_insert] at hg
      split at hg
      · cases hg
        exact .inr ⟨info, hi, hp.symm⟩
      · exact .inl ⟨g', hg, .refl⟩

theorem awaitingCheck_facts (h : awaitingCheck p s k rid w = .ok rc) :
    rc.status = .awaiting ∧ s.approvers.contains w = true := by
  unfold awaitingCheck at h
  cases hc : callCheck s k rid with
  | error => simp [hc, bind, Except.bind] at h
  | ok rc' =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    next he =>
      cases h
      refine ⟨?_, eligibleAny_contains he⟩
      unfold callCheck at hc
      repeat' split at hc
      all_goals first
        | (cases hc; done)
        | (cases hc
           have hst : ¬rc.status ≠ .awaiting := by assumption
           exact Classical.not_not.mp hst)

theorem applyApprove_ok (h : applyApprove p s t k rc w pr dg cost ed = .ok r) :
    ∃ x : CallRec, r.1 = { s with calls := s.calls.insert k x } ∧ x.tool = rc.tool ∧
      x.grant = rc.grant ∧ (x.tally = rc.tally ++ [(pr, w)] ∨ x.tally = [(pr, w)]) ∧
      (x.status = rc.status ∨
        (x.status = .authorized ∧ s.satisfied p x.consent x.tally = true)) := by
  unfold applyApprove at h
  dsimp only at h
  iterate 6 (split at h; · cases h)
  next rc' hn =>
    have hf : rc'.tool = rc.tool ∧ rc'.grant = rc.grant ∧
        (rc'.tally = rc.tally ++ [(pr, w)] ∨ rc'.tally = [(pr, w)]) ∧ rc'.status = rc.status := by
      revert hn
      repeat' split
      all_goals (intro hn; cases hn)
      all_goals simp
    split at h
    next hsat =>
      cases h
      exact ⟨_, rfl, hf.1, hf.2.1, hf.2.2.1, .inr ⟨rfl, hsat⟩⟩
    · cases h
      exact ⟨_, rfl, hf.1, hf.2.1, hf.2.2.1, .inl hf.2.2.2⟩

theorem ConsentCore.approve (h : ConsentCore p s) (hs : s.started = true) :
    ConsentCore p (handleApprove p s t i rid w dg cost ed).1 ∧
      PartiesKept s (handleApprove p s t i rid w dg cost ed).1 := by
  unfold handleApprove
  split
  · exact ⟨h, .refl⟩
  next rc hck =>
    have hk := awaitingCheck_ok hck
    obtain ⟨hst, hac⟩ := awaitingCheck_facts hck
    obtain ⟨hatt, haw, _⟩ := h.calls i rc hk
    obtain ⟨info, hi, hp⟩ := attested_of_contains hac
    dsimp only
    split
    · exact ⟨h, .refl⟩
    next r hr =>
      obtain ⟨x, hx, -, hgrant, htally, hstat⟩ := applyApprove_ok hr
      rw [hx]
      have hxg : x.grant = none := hgrant.trans (haw hst)
      have hxt : TallyAttested s x.tally := by
        intro v hv
        rcases htally with htally | htally <;> rw [htally] at hv
        · rcases List.mem_append.mp hv with hv | hv
          · exact hatt v hv
          · rw [List.mem_singleton.mp hv]; exact ⟨info, hi, hp.symm⟩
        · rw [List.mem_singleton.mp hv]; exact ⟨info, hi, hp.symm⟩
      refine ⟨h.update hs (fun _ _ h => h) rfl (fun _ g hg => ⟨g, hg, .refl⟩)
        (fun _ g hg => .inl ⟨g, hg, .refl⟩) (fun k' c' hc' => ?_), fun _ _ h => h, rfl, rfl⟩
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · cases hc'
        refine .inr ⟨hxt, fun _ => hxg, fun _ hA _ => ⟨fun _ => ?_, fun hn => absurd hxg hn⟩⟩
        rcases hstat with hstat | ⟨_, hsat⟩
        · rw [hstat, hst] at hA
          rcases hA with hA | hA | hA <;> cases hA
        · exact (satisfied_mono (s' := { s with calls := s.calls.insert i x }) hxt
            (fun _ _ h => h) rfl).trans hsat
      · exact .inl ⟨c', hc', .refl⟩

/-- `f` stands for the kernel's private `eligibilityClauses`, unfolded by `rfl` as in
`assign_sound`. -/
theorem clauses_all {q : Clause → Bool} (f : Consent → List Clause)
    (hf : ∀ c, f c = if c.clauses.isEmpty then [{ k := 1, humanOnly := false }] else c.clauses)
    (hne : cs.clauses ≠ []) (h : (f cs).all q = true) : ∀ cl ∈ cs.clauses, q cl = true := by
  rw [hf] at h
  have he : cs.clauses.isEmpty = false := by
    cases hc : cs.clauses with
    | nil => exact absurd hc hne
    | cons _ _ => rfl
  rw [he] at h
  simpa using h

theorem eligibleAll_sound (hne : cs.clauses ≠ []) (h : (s.eligibleAll p cs a).isNone = true) :
    ∀ cl ∈ cs.clauses, s.eligibleFor p cl a = true := by
  unfold State.eligibleAll at h
  split at h
  · cases h
  · split at h
    next hall =>
      exact clauses_all _ (fun _ => rfl) hne hall
    · cases h

theorem findGrant_some {tool dg : String} {gid : String}
    (h : s.findGrant p tool dg cs cost t = some gid) :
    ∃ g, s.grants[gid]? = some g ∧ g.tool = tool ∧ g.digest.all (· == dg) = true ∧
      (s.eligibleAll p cs g.approver).isNone = true := by
  unfold State.findGrant at h
  obtain ⟨⟨gid', g⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_of_find?_eq_some hf)
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨g, hm, hp.1.1.1.1.2, hp.1.1.1.2, hp.2⟩

theorem lookup_filter {α : Type} {P : String × α → Bool} {n : String} (hP : ∀ b, P (n, b) = true) :
    ∀ l : List (String × α), (l.filter P).lookup n = l.lookup n
  | [] => rfl
  | (m, b) :: l => by
    rw [List.filter_cons]
    by_cases hm : n = m
    · subst hm
      simp [hP b, List.lookup]
    · have hb : (n == m) = false := by simpa using hm
      split
      · simp only [List.lookup, hb]; exact lookup_filter hP l
      · simp only [List.lookup, hb]; exact lookup_filter hP l

theorem enforceDecision_facts {tool dg : String} {gs es : List (String × Bool)} {dd : Disposition}
    (h : enforceDecision p s t k tool dg cost gs es = (dd, cs)) :
    (dd = .allowed → cs.clauses = []) ∧ ∀ gid, dd = .allowedByGrant gid →
      cs.single = true ∧ ((p.action? tool).getD {}).firedGrantable es = true ∧
      s.findGrant p tool dg cs cost t = some gid ∧ cs.clauses ≠ [] := by
  unfold enforceDecision at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals cases h
  all_goals refine ⟨fun hd => ?_, fun gid hd => ?_⟩
  all_goals try (cases hd; done)
  next he =>
    exact List.isEmpty_iff.mp he
  next hne _ _ hg =>
    cases hd
    split at hg
    next hc =>
      simp only [Bool.and_eq_true] at hc
      exact ⟨hc.1, hc.2, hg, fun h => hne (by rw [h]; rfl)⟩
    · cases hg

theorem Disposition.grant_of_awaiting {D : Disposition} (h : D.status = .awaiting) :
    D.grant = none := by
  cases D <;> first | rfl | cases h

theorem fired_grantable {r : Requirements} {es : List (String × Bool)}
    (hf : r.firedGrantable es = true) {n : String} {esc : Escalator} (hm : (n, esc) ∈ r.escalate)
    (hl : (es.filter fun x => r.escalate.any fun y => y.1 == x.1).lookup n ≠ some false) :
    esc.grantable = true := by
  rw [lookup_filter (fun _ => List.any_eq_true.mpr ⟨(n, esc), hm, beq_self_eq_true n⟩)] at hl
  unfold Requirements.firedGrantable Requirements.fired at hf
  refine List.all_eq_true.mp hf esc (List.mem_map.mpr ⟨(n, esc), List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩)
  simpa using hl

theorem Keeps.reserveGrant (o : Option String) :
    Keeps s { s with grants := match o with
      | some gid => s.grants.modify gid fun g =>
        { g with reserved := g.reserved + 1, costReserved := g.costReserved + g.costHeld cost }
      | none => s.grants } := by
  cases o with
  | none => exact Keeps.of_eq rfl rfl rfl rfl rfl
  | some gid => exact Keeps.grants_modify (by intro; exact ⟨rfl, rfl, rfl, rfl⟩)

theorem ConsentCore.propose {tool dg : String} {gs es : List (String × Bool)}
    (h : ConsentCore p s) (hs : s.started = true) :
    ConsentCore p (handlePropose p s t k tool dg cost gs es).1 ∧
      PartiesKept s (handlePropose p s t k tool dg cost gs es).1 := by
  unfold handlePropose
  split
  · split <;> exact ⟨h, .refl⟩
  · generalize hd : enforceDecision p s t k tool dg cost gs es = dc
    obtain ⟨dd, cs⟩ := dc
    dsimp only
    split
    · exact ⟨h.keeps hs (Keeps.of_eq rfl rfl rfl rfl rfl), fun _ _ h => h, rfl, rfl⟩
    next r hr =>
      dsimp only
      generalize hD : (Disposition.shadowed (p.modeOf tool) dd).fst = D
      refine ⟨?_, fun _ _ h => h, rfl, rfl⟩
      have hG := Keeps.reserveGrant (s := s) (cost := cost) D.grant
      refine h.update hs (fun _ _ h => h) rfl hG.grantsFwd
        (fun gid g' hg => .inl (hG.grantsBack gid g' hg)) (fun k' c' hc' => ?_)
      dsimp only at hc'
      rw [Std.ExtTreeMap.getElem?_insert] at hc'
      split at hc'
      · cases hc'
        refine .inr ⟨fun _ hw => (nomatch hw), Disposition.grant_of_awaiting, fun hm hA hne => ?_⟩
        have hm' : p.modeOf tool = .enforce := hm
        rw [hm', shadowed_enforce] at hD
        simp only at hD
        subst hD
        obtain ⟨hal, habg⟩ := enforceDecision_facts hd
        cases dd with
        | allowed => exact absurd (hal rfl) hne
        | allowedByGrant gid =>
          obtain ⟨hsingle, hfg, hfind, -⟩ := habg gid rfl
          rw [hr, Option.getD_some] at hfg
          obtain ⟨g, hsg, hgt, hgd, hel⟩ := findGrant_some hfind
          obtain ⟨g', hsg', hga, hgp, hgt', hgd'⟩ := hG.grantsFwd gid g hsg
          obtain ⟨info, hi, hp⟩ := h.grants gid g hsg
          refine ⟨fun hn => (nomatch hn), fun _ => ⟨hsingle, fun r' hr' n esc hm hl => ?_, gid, g',
            rfl, hsg', hgt'.trans hgt, by rw [hgd']; exact hgd, fun cl hcl => ?_⟩⟩
          · rw [hr] at hr'
            cases hr'
            exact fired_grantable hfg hm hl
          · rw [hga, hgp]
            have he := eligibleFor_sound (eligibleAll_sound hne hel cl hcl) hi
            rw [hp] at he
            exact he.mono (fun _ _ h => h) rfl
        | needsApproval _ => rcases hA with hA | hA | hA <;> cases hA
        | denied _ => rcases hA with hA | hA | hA <;> cases hA
      · exact .inl ⟨c', hc', .refl⟩

theorem ConsentCore.kept (h : ConsentCore p s) (hs : s.started = true) (hk : Keeps s s') :
    ConsentCore p s' ∧ PartiesKept s s' :=
  ⟨h.keeps hs hk, hk.parties⟩

theorem ConsentCore.sessionStart (h : ConsentCore p s) (hs : s.started = false) :
    ConsentCore p (handleSessionStart s i pd r ps as l).1 := by
  obtain ⟨_, hc, hg⟩ := h.fresh hs
  unfold handleSessionStart
  split
  · exact h
  · split
    · exact h
    · exact .of_empty (fun hf => by cases hf) hc hg

theorem ConsentCore.stepHandle (h : ConsentCore p s) (hs : s.started = true)
    (hn : stepEnvelope s e = none) :
    ConsentCore p (stepHandle p s e).1 ∧ PartiesKept s (stepHandle p s e).1 := by
  unfold Writ.stepHandle
  split
  next hb =>
    exact ((envelope_iff.mp hn).2.2.1 ⟨hs, by rw [hb]; rfl⟩).elim
  all_goals first
    | with_reducible exact h.kept hs handleSessionEnd_kept
    | with_reducible exact h.kept hs handleTurnStart_kept
    | with_reducible exact h.kept hs handleTurnEnd_kept
    | with_reducible exact h.kept hs handleStepStart_kept
    | with_reducible exact h.kept hs handleApproverAttest_kept
    | with_reducible exact h.kept hs handlePermissionRevoke_kept
    | with_reducible exact h.propose hs
    | with_reducible exact h.approve hs
    | with_reducible exact h.kept hs handleReject_kept
    | with_reducible exact h.kept hs handleApprovalExpire_kept
    | with_reducible exact h.grantCreate hs
    | with_reducible exact h.kept hs handleGrantRevoke_kept
    | with_reducible exact h.kept hs handleDispatch_kept
    | with_reducible exact h.kept hs handleResult_kept
    | with_reducible exact h.kept hs handleOutcomeUnknown_kept
    | with_reducible exact h.kept hs handleReconcile_kept
    | with_reducible exact h.kept hs handleCancel_kept
    | with_reducible exact h.kept hs handleReset_kept
    | with_reducible exact h.kept hs handleKill_kept
    | with_reducible exact h.kept hs handlePermissionAdd_kept
    | with_reducible exact h.kept hs handleEscalationAck_kept
    | with_reducible exact h.kept hs handleLedgerSync_kept

theorem ConsentCore.bump (h : ConsentCore p s) :
    ConsentCore p { s with lastSeq := a, lastTime := b, version := v } := by
  by_cases hs : s.started = true
  · exact h.keeps hs (Keeps.of_eq rfl rfl rfl rfl rfl)
  · obtain ⟨ha, hc, hg⟩ := h.fresh (by simpa using hs)
    exact .of_empty (fun _ => ha) hc hg

theorem ConsentCore.step (h : ConsentCore p s) : ConsentCore p (Writ.step p s e).1 := by
  cases ha : (Writ.step p s e).2.accepted
  · rw [frame ha]; exact h
  · rw [accepted_step ha]
    have hn := accepted_open ha
    refine ConsentCore.bump ?_
    cases hs : s.started
    · cases hb : e.body
      all_goals try (exfalso; unfold stepEnvelope at hn; simp [hb, hs] at hn; done)
      unfold Writ.stepHandle
      rw [hb]
      exact h.sessionStart hs
    · exact (h.stepHandle hs hn).1

theorem ConsentCore.initial : ConsentCore p (State.initial d) :=
  .of_empty (fun _ _ => by simp [State.initial]) (fun _ => by simp [State.initial])
    (fun _ => by simp [State.initial])

theorem consentCore_reachable (hr : Reachable p d s) : ConsentCore p s := by
  induction hr with
  | init => exact ConsentCore.initial
  | step _ ih => exact ih.step

theorem approvers_step (h : ConsentCore p s) {a : String} {i : ApproverInfo}
    (hi : s.approvers[a]? = some i) : (Writ.step p s e).1.approvers[a]? = some i := by
  cases ha : (Writ.step p s e).2.accepted
  · rw [frame ha]; exact hi
  · rw [accepted_step ha]
    by_cases hs : s.started = true
    · exact (h.stepHandle hs (accepted_open ha)).2.approvers a i hi
    · rw [(h.fresh (by simpa using hs)).1 a] at hi; cases hi

theorem requester_step (h : ConsentCore p s) (hs : s.started = true) :
    (Writ.step p s e).1.requester = s.requester := by
  cases ha : (Writ.step p s e).2.accepted
  · rw [frame ha]
  · rw [accepted_step ha]
    exact (h.stepHandle hs (accepted_open ha)).2.requester

end Consent

/-- `approvers` and `requester` say that eligibility read at dispatch agrees with eligibility
read at approval or grant creation. -/
structure ConsentInv (p : Policy) (s : State) : Prop where
  tally : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → TallyAttested s c.tally
  approvers : ∀ (e : Event) (a : String) (i : ApproverInfo),
    s.approvers[a]? = some i → (Writ.step p s e).1.approvers[a]? = some i
  requester : s.started = true → ∀ e : Event, (Writ.step p s e).1.requester = s.requester
  quorum : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → p.modeOf c.tool = .enforce →
    Active c.status → c.consent.clauses ≠ [] → c.grant = none →
      s.satisfied p c.consent c.tally = true
  grant : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → p.modeOf c.tool = .enforce →
    Active c.status → c.consent.clauses ≠ [] → c.grant ≠ none → GrantFacts p s c
  awaiting : ∀ (k : String) (c : CallRec), s.calls[k]? = some c → c.status = .awaiting →
    c.grant = none
  grants : ∀ (gid : String) (g : GrantRec), s.grants[gid]? = some g → GrantAttested s g
  fresh : s.started = false →
    (∀ a : String, s.approvers[a]? = none) ∧ (∀ k : String, s.calls[k]? = none) ∧
      ∀ gid : String, s.grants[gid]? = none

namespace Consent

theorem ConsentCore.inv (h : ConsentCore p s) : ConsentInv p s where
  tally k c hc := (h.calls k c hc).1
  approvers _ _ _ hi := approvers_step h hi
  requester hs _ := requester_step h hs
  quorum k c hc hm ha hne := ((h.calls k c hc).2.2 hm ha hne).1
  grant k c hc hm ha hne := ((h.calls k c hc).2.2 hm ha hne).2
  awaiting k c hc := (h.calls k c hc).2.1
  grants := h.grants
  fresh := h.fresh

end Consent

theorem consentInv_reachable : Reachable p d s → ConsentInv p s :=
  fun hr => (consentCore_reachable hr).inv

theorem consent (hr : Reachable p d s) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hne : c.consent.clauses ≠ []) :
    (c.grant = none ∧ ConsentMet p s c.consent c.tally) ∨ GrantCovers p s e.time c := by
  have hi := consentInv_reachable hr
  obtain ⟨-, c', hc', ⟨hst, -⟩, hok⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  obtain ⟨⟨-, -, -, hv⟩, -⟩ := hok hm
  have ha : Active c.status := hst.elim .inl (.inr ∘ .inr)
  cases hg : c.grant with
  | none => exact .inl ⟨rfl, satisfied_sound (hi.tally k c hc) (hi.quorum k c hc hm ha hne hg)⟩
  | some gid =>
    obtain ⟨hsingle, hfired, gid', gr, hgid, hsg, hgt, hgd, hel⟩ :=
      hi.grant k c hc hm ha hne (by rw [hg]; nofun)
    rw [hg] at hgid
    cases hgid
    obtain ⟨gr', hsg', hval⟩ := hv gid hg
    rw [hsg] at hsg'
    cases hsg'
    exact .inr ⟨hsingle, hfired, gid, gr, hg, hsg, hgt, hgd, hel, hval⟩

namespace Consent

def consentApprovers : List (String × ApproverInfo) := [("a1", ⟨"alice", .human, ["owner"]⟩)]

def consentPolicy : Policy :=
  { approverRoles := ["owner"], actions := [("pay", { consent := .perCall })] }

def consentEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] consentApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "pay" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .approve "c1" ⟨"s1", "c1", 0⟩ "a1" "d1" none none⟩ ]

def consentDispatch : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

def grantPolicy : Policy :=
  { approverRoles := ["owner"]
    actions :=
      [("pay", { consent := .perCall, grantable := some { scope := .session, maxUses := 2 } })] }

def grantEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] consentApprovers {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .grantCreate "g1" "a1" "pay" (some "d1") .session 1 none none none "r1"⟩
  , ⟨4, 4, 3, none, .propose "c1" "pay" "d1" none [] []⟩ ]

end Consent

#guard (trace consentPolicy (State.initial "pd") (consentEvents ++ [consentDispatch])).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) none,
       .ok .authorized none, .ok .dispatchClaimed none ]
#guard (step consentPolicy (after consentPolicy "pd" consentEvents) consentDispatch).2.claimed
#guard ((after consentPolicy "pd" consentEvents).calls["c1"]?).any fun c =>
  consentPolicy.modeOf c.tool == .enforce && !c.consent.clauses.isEmpty && c.grant.isNone &&
    c.tally == [("alice", "a1")] &&
    (after consentPolicy "pd" consentEvents).satisfied consentPolicy c.consent c.tally

#guard (trace grantPolicy (State.initial "pd") (grantEvents ++ [consentDispatch])).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok .none none, .ok (.allowedByGrant "g1") none,
       .ok .dispatchClaimed none ]
#guard (step grantPolicy (after grantPolicy "pd" grantEvents) consentDispatch).2.claimed
#guard ((after grantPolicy "pd" grantEvents).calls["c1"]?).any fun c =>
  grantPolicy.modeOf c.tool == .enforce && !c.consent.clauses.isEmpty && c.consent.single &&
    c.tally.isEmpty && c.grant == some "g1" &&
    ((after grantPolicy "pd" grantEvents).grants["g1"]?).any fun g =>
      g.validAt (after grantPolicy "pd" grantEvents) consentDispatch.time && g.tool == "pay" &&
        c.consent.clauses.all fun cl =>
          (after grantPolicy "pd" grantEvents).eligibleFor grantPolicy cl g.approver

end Writ.Proofs

