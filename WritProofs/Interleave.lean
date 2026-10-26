import WritProofs.Accounting
import WritProofs.Kill

namespace Writ.Proofs

open Writ
open Basic

/-- Section 8, theorem 9: one step of one session in an interleaving, with the stored ledger
before and after it. -/
structure Commit where
  session : Nat
  pre : State
  event : Event
  verdict : Verdict
  storedBefore : Ledger
  storedAfter : Ledger

/-- Section 8, theorem 9: `ledger_sync` and `session_start` bring a session up to the stored
ledger and never write it. -/
def writesLedger : EventBody → Bool
  | .ledgerSync _ | .sessionStart .. => false
  | _ => true

/-- Section 8, theorem 9: session `i` takes event `e`, and a step other than `ledger_sync` and
`session_start` that changes the ledger version writes its ledger to the store. -/
def interleave (p : Policy) (d : String) (stored : Ledger) (sessions : Nat → State) :
    List (Nat × Event) → List Commit
  | [] => []
  | (i, e) :: rest =>
    let pre := sessions i
    let r := step p pre e
    let stored' :=
      if writesLedger e.body = true ∧ r.1.ledger.version ≠ pre.ledger.version then r.1.ledger
      else stored
    ⟨i, pre, e, r.2, stored, stored'⟩ ::
      interleave p d stored' (fun j => if j = i then r.1 else sessions j) rest

/-- Section 8, theorem 9's commit discipline: each committed step that changed the stored ledger
read the last committed ledger. -/
def Disciplined (p : Policy) (log : List Commit) : Prop :=
  ∀ x ∈ log, writesLedger x.event.body = true →
    (step p x.pre x.event).1.ledger.version ≠ x.pre.ledger.version →
      x.pre.ledger = x.storedBefore

/-- Section 8, theorem 9 over several policies: a step of session `i`, or an out-of-band write of
the stored ledger's tombstone (the gate's `killPrincipal` and `clearPrincipalKill`). -/
inductive Op where
  | step (i : Nat) (e : Event)
  | store (tombstone : Bool)

/-- Section 7: the out-of-band tombstone write, which bumps the version only when it changes the
tombstone. -/
def storeLedger (l : Ledger) (b : Bool) : Ledger :=
  if l.tombstone = b then l else { l with tombstone := b, version := l.version + 1 }

theorem storeLedger_eq (l : Ledger) (b : Bool) : storeLedger l b = l.setTombstone b := rfl

/-- Section 8, theorem 9 over several policies: `interleave` where session `i` steps under
`pol i` and an `Op.store` rewrites the stored ledger without a commit. -/
def interleaveP (pol : Nat → Policy) (stored : Ledger) (sessions : Nat → State) :
    List Op → List Commit
  | [] => []
  | .step i e :: rest =>
    let pre := sessions i
    let r := step (pol i) pre e
    let stored' :=
      if writesLedger e.body = true ∧ r.1.ledger.version ≠ pre.ledger.version then r.1.ledger
      else stored
    ⟨i, pre, e, r.2, stored, stored'⟩ ::
      interleaveP pol stored' (fun j => if j = i then r.1 else sessions j) rest
  | .store b :: rest => interleaveP pol (storeLedger stored b) sessions rest

/-- Section 8, theorem 9's commit discipline over several policies: `Disciplined` with each
commit stepped under its session's policy. -/
def DisciplinedP (pol : Nat → Policy) (log : List Commit) : Prop :=
  ∀ x ∈ log, writesLedger x.event.body = true →
    (step (pol x.session) x.pre x.event).1.ledger.version ≠ x.pre.ledger.version →
      x.pre.ledger = x.storedBefore

/-- The event of a step op; an out-of-band write has none. -/
def Op.event? : Op → Option Event
  | .step _ e => some e
  | .store _ => none

/-- Section 10's trusted monotone server clock, shared by every session of the schedule: the event
times of its step ops never decrease along it, so commit order matches time order. -/
def TimeOrdered (ops : List Op) : Prop :=
  (ops.filterMap Op.event?).Pairwise fun a b => a.time ≤ b.time

/-- Section 8, theorem 9 over several policies: every two policies that define `m` as a principal
meter give it the same unit and window, as `createGate` checks. -/
def MeterAgree (pol : Nat → Policy) (m : String) : Prop :=
  ∀ i j si sj, (pol i).meter? m = some si → (pol j).meter? m = some sj →
    si.scope = .principal → sj.scope = .principal → si.unit = sj.unit ∧ si.windowMs = sj.windowMs

variable {p : Policy} {d : String} {s : State} {e : Event} {L : Ledger} {S : Nat → State}
  {sched : List (Nat × Event)} {x : Commit} {pre post log : List Commit}
  {k m dg key : String} {n t cap : Nat} {cost : Option Cost} {g : List (String × Bool)}
  {c : CallRec} {r : Requirements} {spec : MeterSpec} {f : List MeterEntry → List MeterEntry}
  {st : CallStatus} {ms : List String} {o : Outcome} {a : Option Nat} {ne : Bool}
  {pol : Nat → Policy} {dig : Nat → String} {ops : List Op} {en : MeterEntry} {i : Nat}

namespace Interleave

instance instDecidableDisciplined {p : Policy} {log : List Commit} :
    Decidable (Disciplined p log) := by
  unfold Disciplined; infer_instance

instance instDecidableDisciplinedP {pol : Nat → Policy} {log : List Commit} :
    Decidable (DisciplinedP pol log) := by
  unfold DisciplinedP; infer_instance

instance instDecidableTimeOrdered {ops : List Op} : Decidable (TimeOrdered ops) := by
  unfold TimeOrdered; infer_instance

theorem updateEntries_version :
    s.ledger.version ≤ (s.updateEntries p m t f).ledger.version := by
  unfold State.updateEntries; split <;> dsimp only <;> omega

theorem updateEntries_tomb : (s.updateEntries p m t f).ledger.tombstone = s.ledger.tombstone := by
  unfold State.updateEntries; split <;> rfl

theorem consumeGrant_ledger : (s.consumeGrant k).ledger = s.ledger := by
  unfold State.consumeGrant; repeat' split
  all_goals rfl

theorem releaseGrant_ledger : (s.releaseGrant k).ledger = s.ledger := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem recordFailure_ledger {tool : String} : (s.recordFailure p tool).ledger = s.ledger := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem endCall_ledger : (s.endCall k st).ledger = s.ledger := by
  unfold State.endCall; dsimp only; rw [releaseGrant_ledger]

theorem cancelPending_ledger : (cancelPending s).ledger = s.ledger := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b : State => b.ledger = s.ledger) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split <;> first | exact ha | rw [endCall_ledger, ha]

theorem interrupt_ledger : s.interrupt.ledger = s.ledger := by
  unfold State.interrupt; dsimp only; rw [cancelPending_ledger]

theorem settle_tomb : (s.settle p ms k o a ne t).1.ledger.tombstone = s.ledger.tombstone := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.ledger.tombstone = s.ledger.tombstone)
    ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · rw [State.release, updateEntries_tomb, h]
  · split <;> rw [State.commit, updateEntries_tomb, h]

theorem claim_version {r : Requirements} {retry : Bool} {key : String} :
    s.ledger.version < (claim p s t k c r retry key).ledger.version := by
  unfold claim
  dsimp only
  refine Nat.lt_succ_of_le ?_
  split
  · exact foldl_invariant (fun b : State => s.ledger.version ≤ b.ledger.version)
      (fun _ _ h => Nat.le_trans h updateEntries_version) _ _ (Nat.le_refl _)
  · refine foldl_invariant (fun b : State => s.ledger.version ≤ b.ledger.version)
      (fun _ _ h => Nat.le_trans h updateEntries_version) _ _ ?_
    rw [consumeGrant_ledger]; exact Nat.le_refl _

/-- Section 6, Ledger: every claim changes the ledger version. -/
theorem claimed_version (hr : Reachable p d s) (h : (step p s e).2.claimed = true) :
    (step p s e).1.ledger.version ≠ s.ledger.version := by
  obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hr h
  obtain ⟨-, c, hc, -⟩ := (dispatch_claimed_iff he).mp h
  rw [claim_post h he hc]
  exact Nat.ne_of_gt (claim_version (key := key))

theorem stepHandle_tomb (hw : writesLedger e.body = true) (ht : s.ledger.tombstone = true)
    (hn : stepEnvelope s e = none) : (stepHandle p s e).1.ledger.tombstone = true := by
  unfold stepHandle
  split <;> rename_i hb
  all_goals try (rw [hb] at hw; cases hw; done)
  -- The envelope admits a tombstoned session only the events that stay open after a kill, so
  -- only those handlers are left to keep the tombstone.
  all_goals try
    (exfalso; unfold stepEnvelope at hn; simp [hb, ht] at hn
     repeat' split at hn
     all_goals simp_all
     done)
  all_goals
    first
      | unfold handlePropose
      | unfold handleKill
      | unfold handleSessionEnd
      | unfold handleResult
      | unfold handleOutcomeUnknown
      | unfold handleReconcile
    repeat' (first | (dsimp only) | split)
  all_goals simp only [withStatus, settle_tomb, recordFailure_ledger, State.recordSuccess,
    interrupt_ledger, cancelPending_ledger, ht]

/-- A step that writes the stored ledger never clears its tombstone. -/
theorem tomb_stays (hw : writesLedger e.body = true) (ht : s.ledger.tombstone = true) :
    (step p s e).1.ledger.tombstone = true := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact ht
  · rw [accepted_step ha]
    exact stepHandle_tomb hw ht (accepted_open ha)

theorem kill_ledger (hk : e.body = .kill) (ha : (step p s e).2.accepted = true)
    (hp : p.killSetsTombstone = true) :
    (step p s e).1.ledger =
      { s.ledger with tombstone := true, version := s.ledger.version + 1 } := by
  rw [accepted_step ha]
  show (stepHandle p s e).1.ledger = _
  unfold stepHandle
  rw [hk]
  simp only [handleKill, hp, ↓reduceIte, cancelPending_ledger]

theorem update_reach (hS : ∀ i, Reachable (pol i) (dig i) (S i)) {i : Nat} :
    ∀ j, Reachable (pol j) (dig j)
      ((fun j => if j = i then (step (pol i) (S i) e).1 else S j) j) := fun j => by
  dsimp only
  split
  · rename_i h; subst h; exact .step (hS _)
  · exact hS j

theorem memP (hS : ∀ i, Reachable (pol i) (dig i) (S i)) (hx : x ∈ interleaveP pol L S ops) :
    Reachable (pol x.session) (dig x.session) x.pre ∧
      x.verdict = (step (pol x.session) x.pre x.event).2 ∧
      x.storedAfter =
        if writesLedger x.event.body = true ∧
          (step (pol x.session) x.pre x.event).1.ledger.version ≠ x.pre.ledger.version
        then (step (pol x.session) x.pre x.event).1.ledger else x.storedBefore := by
  induction ops generalizing L S with
  | nil => cases hx
  | cons o rest ih =>
    cases o with
    | step i e =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hS i, rfl, rfl⟩
      · exact ih (update_reach hS) hx
    | store b => exact ih hS hx

theorem suffixP (hS : ∀ i, Reachable (pol i) (dig i) (S i))
    (h : interleaveP pol L S ops = pre ++ x :: post) :
    ∃ S' rest, (∀ i, Reachable (pol i) (dig i) (S' i)) ∧ (∀ o ∈ rest, o ∈ ops) ∧
      S' x.session = (step (pol x.session) x.pre x.event).1 ∧
      post = interleaveP pol x.storedAfter S' rest := by
  induction ops generalizing L S pre with
  | nil => cases pre <;> cases h
  | cons o rest ih =>
    cases o with
    | step i e =>
      cases pre with
      | nil =>
        injection h with hx hp
        subst hx
        exact ⟨_, rest, update_reach hS, fun _ ho => List.mem_cons_of_mem _ ho, ite_eq_left rfl,
          hp.symm⟩
      | cons a pre =>
        injection h with _ hp
        obtain ⟨S', r, hS', hr, hx, hpost⟩ := ih (update_reach hS) hp
        exact ⟨S', r, hS', fun _ ho => List.mem_cons_of_mem _ (hr _ ho), hx, hpost⟩
    | store b =>
      obtain ⟨S', r, hS', hr, hx, hpost⟩ := ih hS h
      exact ⟨S', r, hS', fun _ ho => List.mem_cons_of_mem _ (hr _ ho), hx, hpost⟩

/-- Without an out-of-band clear, a tombstone in the store stays there: a committed step wrote a
ledger read from the store, and `tomb_stays` keeps its tombstone. -/
theorem tombP (hL : L.tombstone = true) (hno : Op.store false ∉ ops)
    (hdis : DisciplinedP pol (interleaveP pol L S ops)) :
    ∀ y ∈ interleaveP pol L S ops, y.storedBefore.tombstone = true := by
  induction ops generalizing L S with
  | nil => intro y hy; cases hy
  | cons o rest ih =>
    have hno' : Op.store false ∉ rest := fun h => hno (List.mem_cons_of_mem _ h)
    cases o with
    | step i e =>
      have hhead := hdis _ List.mem_cons_self
      dsimp only at hhead
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hL
      · refine ih ?_ hno' (fun z hz => hdis z (List.mem_cons_of_mem _ hz)) y hy
        split
        · rename_i hw
          exact tomb_stays hw.1 (by rw [hhead hw.1 hw.2]; exact hL)
        · exact hL
    | store b =>
      cases b with
      | false => exact absurd List.mem_cons_self hno
      | true =>
        refine ih ?_ hno' hdis
        unfold storeLedger
        rw [ite_eq_left hL]
        exact hL

theorem tomb_afterP (hS : ∀ i, Reachable (pol i) (dig i) (S i))
    (hdis : DisciplinedP pol (interleaveP pol L S ops))
    (hsplit : interleaveP pol L S ops = pre ++ x :: post) (hno : Op.store false ∉ ops)
    (ht : x.storedAfter.tombstone = true) : ∀ y ∈ post, y.storedBefore.tombstone = true := by
  obtain ⟨S', rest, -, hrest, -, hpost⟩ := suffixP hS hsplit
  have hmem : ∀ y ∈ post, y ∈ interleaveP pol L S ops := fun y hy => by rw [hsplit]; simp [hy]
  subst hpost
  exact tombP ht (fun h => hno (hrest _ h)) (fun z hz => hdis z (hmem z hz))

/-- A claim writes the ledger, so under the discipline it read the stored ledger and stored the
ledger it produced. -/
theorem claim_commit (hS : ∀ i, Reachable (pol i) (dig i) (S i))
    (hdis : DisciplinedP pol (interleaveP pol L S ops)) (hx : x ∈ interleaveP pol L S ops)
    (h : x.verdict.claimed = true) :
    Reachable (pol x.session) (dig x.session) x.pre ∧
      (step (pol x.session) x.pre x.event).2.claimed = true ∧ x.pre.ledger = x.storedBefore ∧
      x.storedAfter = (step (pol x.session) x.pre x.event).1.ledger := by
  obtain ⟨hR, hv, hst⟩ := memP hS hx
  rw [hv] at h
  obtain ⟨_, _, _, _, _, _, he⟩ := claimed_dispatch hR h
  have hw : writesLedger x.event.body = true := by rw [he]; rfl
  have hver := claimed_version hR h
  exact ⟨hR, h, hdis x hx hw hver, by rw [hst, ite_eq_left ⟨hw, hver⟩]⟩

theorem no_claim_storedP (hS : ∀ i, Reachable (pol i) (dig i) (S i))
    (hdis : DisciplinedP pol (interleaveP pol L S ops)) (hx : x ∈ interleaveP pol L S ops)
    (ht : x.storedBefore.tombstone = true) : x.verdict.claimed = false := by
  cases hc : x.verdict.claimed
  · rfl
  · obtain ⟨-, h, hpre, -⟩ := claim_commit hS hdis hx hc
    rw [no_claim_tombstone (by rw [hpre]; exact ht)] at h
    cases h

theorem kill_commit (hS : ∀ i, Reachable (pol i) (dig i) (S i))
    (hx : x ∈ interleaveP pol L S ops) (hk : x.event.body = .kill)
    (ha : x.verdict.accepted = true) (hp : (pol x.session).killSetsTombstone = true) :
    x.storedAfter.tombstone = true := by
  obtain ⟨-, hv, hst⟩ := memP hS hx
  rw [hv] at ha
  have hkl := kill_ledger hk ha hp
  have hw : writesLedger x.event.body = true := by rw [hk]; rfl
  have hver : (step (pol x.session) x.pre x.event).1.ledger.version ≠ x.pre.ledger.version := by
    rw [hkl]; exact Nat.succ_ne_self _
  rw [hst, ite_eq_left ⟨hw, hver⟩, hkl]

/-- An entry that section 6's pruning at `t` under `p` drops from the principal ledger. -/
def PrunedAt (p : Policy) (t : Nat) (en : MeterEntry) : Prop :=
  (p.meter? en.meter).any (fun spec => spec.scope == .principal && spec.expired en t) = true

/-- `s'` keeps every entry of another session that `s` holds, unless pruning at `t` drops it. -/
def Others (p : Policy) (t : Nat) (s s' : State) : Prop :=
  s'.sessionId = s.sessionId ∧ ∀ en ∈ s.ledger.entries, en.session ≠ s.sessionId →
    en ∈ s'.ledger.entries ∨ PrunedAt p t en

theorem Others.of (hsid : s'.sessionId = s.sessionId)
    (hled : s'.ledger.entries = s.ledger.entries) : Others p t s s' :=
  ⟨hsid, fun _ hen _ => .inl (hled ▸ hen)⟩

theorem Others.trans (h₁ : Others p t s s₁) (h₂ : Others p t s₁ s₂) : Others p t s s₂ :=
  ⟨h₂.1.trans h₁.1, fun en hen hne => (h₁.2 en hen hne).elim
    (fun h => h₂.2 en h (h₁.1 ▸ hne)) .inr⟩

theorem updateEntries_others
    (hf : ∀ l, ∀ en ∈ l, en.session ≠ s.sessionId → en ∈ f l) :
    Others p t s (s.updateEntries p m t f) := by
  refine ⟨Meters.updateEntries_sessionId, fun en hen hne => ?_⟩
  unfold State.updateEntries
  split
  · dsimp only
    split
    · exact .inl hen
    · unfold Policy.prune
      by_cases hp : PrunedAt p t en
      · exact .inr hp
      · refine .inl (List.mem_filter.mpr ⟨hf _ en hen hne, ?_⟩)
        unfold PrunedAt at hp
        simpa using hp
  · exact .inl hen

theorem isFor_other {sid k : String} (hne : en.session ≠ sid) : en.isFor m sid k = false := by
  simp [MeterEntry.isFor, hne]

theorem reserve_others {k : String} : Others p t s (s.reserve p m k n t) :=
  updateEntries_others fun _ _ h _ => List.mem_append_left _ h

theorem retime_others {k : String} : Others p t s (s.retime p m k t) :=
  updateEntries_others fun _ en h hne => List.mem_map.mpr ⟨en, h, by simp [isFor_other hne]⟩

theorem commit_others {k : String} : Others p t s (s.commit p m k n t) :=
  updateEntries_others fun _ en h hne => List.mem_map.mpr ⟨en, h, by simp [isFor_other hne]⟩

theorem release_others {k : String} : Others p t s (s.release p m k t) :=
  updateEntries_others fun _ en h hne => List.mem_filter.mpr ⟨h, by simp [isFor_other hne]⟩

theorem claim_others {retry : Bool} : Others p t s (claim p s t k c r retry key) := by
  unfold claim
  dsimp only
  refine Others.trans ?_ (Others.of rfl rfl)
  split
  · exact foldl_invariant (Others p t s) (fun _ _ h => h.trans retime_others) _ s
      (Others.of rfl rfl)
  · exact foldl_invariant (Others p t s) (fun _ _ h => h.trans reserve_others) _ _
      (Others.of Accounting.consumeGrant_same.sid Accounting.consumeGrant_same.led)

theorem settle_others : Others p t s (s.settle p ms k o a ne t).1 := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => Others p t s b.1) ?_ ms _
    (Others.of rfl rfl)
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact h.trans release_others
  · split <;> exact h.trans commit_others

/-- A step that writes the stored ledger keeps every entry of another session, unless pruning at
the event's time under the stepping policy drops it. -/
theorem step_others (hr : Reachable p d s) (hw : writesLedger e.body = true) :
    Others p e.time s (step p s e).1 := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact Others.of rfl rfl
  · cases hcl : (step p s e).2.claimed
    · have hcl' : (stepHandle p s e).2.claimed = false := by
        rw [accepted_step ha] at hcl; exact hcl
      rw [accepted_step ha]
      refine Others.trans (s₁ := (stepHandle p s e).1) ?_ (Others.of rfl rfl)
      rcases Accounting.stepHandle_kind hcl' with
        hp | ⟨k, _, c', _, _, _, -, -, -, -, -, -, hs⟩ | ⟨_, hb, -⟩ | ⟨_, _, _, _, _, _, hb, -⟩
      · exact Others.of hp.sid hp.led
      · exact (Others.of (s' := { s with calls := s.calls.insert k c' }) rfl rfl).trans
          (settle_others.trans (Others.of hs.sid hs.led))
      · rw [hb] at hw; cases hw
      · rw [hb] at hw; cases hw
    · obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hr hcl
      obtain ⟨-, c, hc, -⟩ := (dispatch_claimed_iff he).mp hcl
      rw [claim_post hcl he hc]
      exact (claim_others (key := key)).trans (Others.of rfl rfl)

theorem releaseGrant_ended : (s.releaseGrant k).ended = s.ended := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem recordFailure_ended {tool : String} : (s.recordFailure p tool).ended = s.ended := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem updateEntries_ended : (s.updateEntries p m t f).ended = s.ended := by
  unfold State.updateEntries; split <;> rfl

theorem settle_ended : (s.settle p ms k o a ne t).1.ended = s.ended := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.ended = s.ended) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · rw [State.release, updateEntries_ended, h]
  · split <;> rw [State.commit, updateEntries_ended, h]

theorem endCall_ended : (s.endCall k st).ended = s.ended := by
  unfold State.endCall; dsimp only; rw [releaseGrant_ended]

theorem cancelPending_ended : (cancelPending s).ended = s.ended := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b : State => b.ended = s.ended) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split <;> first | exact ha | rw [endCall_ended, ha]

theorem stepHandle_ended (hd : s.ended = true) (hn : stepEnvelope s e = none) :
    (stepHandle p s e).1.ended = true := by
  unfold stepHandle
  split <;> rename_i hb
  -- The envelope admits an ended session only `reconcile` and `ledger_sync`.
  all_goals try
    (exfalso; unfold stepEnvelope at hn; simp [hb, hd] at hn
     repeat' split at hn
     all_goals simp_all
     done)
  all_goals
    first
      | unfold handleReconcile
      | unfold handleLedgerSync
    repeat' (first | (dsimp only) | split)
  all_goals simp only [settle_ended, recordFailure_ended, cancelPending_ended, hd]

theorem ended_stays (hd : s.ended = true) : (step p s e).1.ended = true := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact hd
  · rw [accepted_step ha]
    exact stepHandle_ended hd (accepted_open ha)

theorem no_claim_ended (hd : s.ended = true) : (step p s e).2.claimed = false := by
  cases hc : (step p s e).2.claimed
  · rfl
  · have hs := (envelope_iff.mp (accepted_open (claimed_accepted hc))).2.1 hd
    rcases stepHandle_claimed (step_claimed hc) with
      ⟨_, _, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, _, _, hb, _, _⟩
    all_goals (rw [hb] at hs; cases hs)

theorem sync_started {l : Ledger} : (handleLedgerSync s l).1.started = s.started := by
  unfold handleLedgerSync
  dsimp only
  repeat' split
  all_goals first | rfl | exact Accounting.cancelPending_plain.started

theorem started_stays (hr : Reachable p d s) (hs : s.started = true) :
    (step p s e).1.started = true := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact hs
  · cases hcl : (step p s e).2.claimed
    · have hcl' : (stepHandle p s e).2.claimed = false := by
        rw [accepted_step ha] at hcl; exact hcl
      rw [accepted_step ha]
      show (stepHandle p s e).1.started = true
      rcases Accounting.stepHandle_kind hcl' with
        hp | ⟨_, _, _, _, _, _, -, -, -, -, -, -, hst⟩ | ⟨_, -, he⟩ | ⟨_, _, _, _, _, _, hb, -⟩
      · rw [hp.started]; exact hs
      · rw [hst.started, Accounting.settle_started]; exact hs
      · rw [he, sync_started]; exact hs
      · exact absurd ⟨hs, by rw [hb]; rfl⟩ (envelope_iff.mp (accepted_open ha)).2.2.1
    · obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hr hcl
      obtain ⟨-, c, hc, -⟩ := (dispatch_claimed_iff he).mp hcl
      rw [claim_post hcl he hc]
      exact (Accounting.claim_started (key := key)).trans hs

theorem unstarted_tomb (hr : Reachable p d s) : s.started = false → s.ledger.tombstone = false := by
  induction hr with
  | init => intro _; rfl
  | @step s e hr ih =>
    intro h
    cases hs : s.started
    · cases ha : (step p s e).2.accepted
      · rw [frame ha] at h ⊢; exact ih h
      · exfalso
        have hst : e.body.isStart = true := by
          rcases (envelope_iff.mp (accepted_open ha)).1 with h' | h'
          · rw [hs] at h'; cases h'
          · exact h'
        have ha' := ha
        rw [accepted_step ha] at h ha'
        change (stepHandle p s e).1.started = false at h
        change (stepHandle p s e).2.accepted = true at ha'
        unfold stepHandle at h ha'
        split at h <;> rename_i hb <;> rw [hb] at hst <;> try cases hst
        rw [hb] at ha'
        dsimp only at ha'
        unfold handleSessionStart at h ha'
        repeat' split at ha'
        all_goals simp_all [Verdict.accepted]
    · rw [started_stays hr hs] at h; cases h

theorem started_of_tomb (hr : Reachable p d s) (ht : s.ledger.tombstone = true) :
    s.started = true := by
  cases hs : s.started
  · rw [unstarted_tomb hr hs] at ht; cases ht
  · rfl

/-- A session that has seen the tombstone: ended, or started with the tombstone on its ledger. -/
def Shut (s : State) : Prop := s.ended = true ∨ (s.started = true ∧ s.ledger.tombstone = true)

theorem writes_false {b : EventBody} (hw : writesLedger b = false) :
    (∃ l, b = .ledgerSync l) ∨ ∃ i pd r ps as l, b = .sessionStart i pd r ps as l := by
  cases b <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, _, _, _, _, _, rfl⟩ | cases hw

theorem sync_tomb {l : Ledger} (ht : s.ledger.tombstone = true) (hd : s.ended = false)
    (ha : (handleLedgerSync s l).2.accepted = true) :
    (handleLedgerSync s l).1.ledger.tombstone = true := by
  unfold handleLedgerSync at ha ⊢
  dsimp only at ha ⊢
  split at ha
  · cases ha
  · rename_i hno
    simp only [ht, hd, Bool.not_false, Bool.and_true, Bool.true_and, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, not_or] at hno
    split <;> simp_all

/-- A session that has seen the tombstone stays shut: a step that writes keeps the tombstone, a
`ledger_sync` that would clear it is refused while the session is live, and an ended session
stays ended. -/
theorem shut_step (hr : Reachable p d s) (h : Shut s) : Shut (step p s e).1 := by
  rcases h with hd | ⟨hs, ht⟩
  · exact .inl (ended_stays hd)
  · cases hd : s.ended
    · refine .inr ⟨started_stays hr hs, ?_⟩
      cases hw : writesLedger e.body
      · cases ha : (step p s e).2.accepted
        · rw [frame ha]; exact ht
        · have henv := envelope_iff.mp (accepted_open ha)
          have ha' := ha
          rw [accepted_step ha] at ha' ⊢
          change (stepHandle p s e).2.accepted = true at ha'
          change (stepHandle p s e).1.ledger.tombstone = true
          rcases writes_false hw with ⟨l, hb⟩ | ⟨_, _, _, _, _, _, hb⟩
          · unfold stepHandle at ha' ⊢
            rw [hb] at ha' ⊢
            exact sync_tomb ht hd ha'
          · exact absurd ⟨hs, by rw [hb]; rfl⟩ henv.2.2.1
      · exact tomb_stays hw ht
    · exact .inl (ended_stays hd)

theorem shut_unclaimed (h : Shut s) : (step p s e).2.claimed = false :=
  h.elim no_claim_ended fun h => no_claim_tombstone h.2

theorem shut_mem (hS : ∀ i, Reachable (pol i) (dig i) (S i)) {j : Nat} (hj : Shut (S j)) :
    ∀ y ∈ interleaveP pol L S ops, y.session = j → Shut y.pre := by
  induction ops generalizing L S with
  | nil => intro y hy; cases hy
  | cons o rest ih =>
    cases o with
    | step i e =>
      intro y hy hys
      rcases List.mem_cons.mp hy with rfl | hy
      · subst hys; exact hj
      · refine ih (update_reach hS) ?_ y hy hys
        show Shut (if j = i then _ else _)
        split
        · rename_i h; subst h; exact shut_step (hS _) hj
        · exact hj
    | store b => exact ih hS hj

theorem store_false_not_mem : Op.store false ∉ sched.map fun (i, e) => Op.step i e := by
  intro h
  obtain ⟨⟨_, _⟩, -, h⟩ := List.mem_map.mp h
  cases h

end Interleave

open Interleave

/-- Section 8, theorem 9 over several policies: every commit of session `i` is taken on a state
reachable under that session's policy and digest. -/
theorem multi_reachable (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hx : x ∈ log) : Reachable (pol x.session) (dig x.session) x.pre :=
  (memP (dig := dig) (fun _ => .init) (hlog ▸ hx)).1

/-- Section 8, theorem 9 over several policies: a claim on a principal meter found room, under
the claiming session's policy, on the stored ledger it read, and the ledger it stored stays
within that policy's cap. -/
theorem multi_cap (hwf : (pol x.session).WF)
    (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hx : x ∈ log) (h : x.verdict.claimed = true)
    (he : x.event.body = .dispatch k n dg cost g key) (hc : x.pre.calls[k]? = some c)
    (hm : (pol x.session).modeOf c.tool = .enforce) (hr : (pol x.session).action? c.tool = some r)
    (hmr : m ∈ r.meters) (hs : (pol x.session).meter? m = some spec)
    (hsc : spec.scope = .principal) (hcap : spec.cap = some cap)
    (hfresh : c.status = .authorized ∨
      ∀ en ∈ ownEntries (pol x.session) x.pre m k,
        spec.windowMs.all (en.time + · > x.event.time) = false) :
    usageAt spec x.storedBefore.entries m x.event.time + draw spec c.cost ≤ cap ∧
      usageAt spec x.storedAfter.entries m x.event.time ≤ cap := by
  subst hlog
  obtain ⟨hR, h, hpre, hst⟩ := claim_commit (dig := dig) (fun _ => .init) hdis hx h
  have hent : ∀ s', entriesOf (pol x.session) s' m = s'.ledger.entries := fun _ => by
    simp [entriesOf, hs, hsc]
  rw [← hpre, hst, ← hent, ← hent]
  refine ⟨hfresh.elim (meter_room h he hc · hm hr hmr hs hcap)
    (meter_room_retry h he hc hm hr hmr hs hcap), ?_⟩
  obtain ⟨-, c', hc', ⟨hau, -⟩, -⟩ := (dispatch_claimed_iff he).mp h
  cases hc.symm.trans hc'
  refine hau.elim (meter_cap hwf h he hc · hm hr hmr hs hcap) fun hun => ?_
  refine meter_cap_retry hwf hR h he hc hun hm hr hmr hs hcap fun en hen h1 h2 h3 => ?_
  refine hfresh.elim (fun hau => ?_) (· en (List.mem_filter.mpr ⟨hen, by simp [h1, h2, h3]⟩))
  rw [hau] at hun
  cases hun

/-- Section 8, theorem 9 and section 7 over several policies: no session claims on a stored
ledger that carries the tombstone, set by a `kill` or out of band. -/
theorem multi_kill (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hx : x ∈ log) (ht : x.storedBefore.tombstone = true) :
    x.verdict.claimed = false := by
  subst hlog
  exact no_claim_storedP (dig := dig) (fun _ => .init) hdis hx ht

/-- Section 8, theorem 9 over several policies: after an accepted `kill` under the killing
session's `kill_sets_tombstone`, and with no out-of-band clear, no later step of any session
claims. -/
theorem multi_kill_event (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hsplit : log = pre ++ x :: post)
    (hnoclear : Op.store false ∉ ops) (hk : x.event.body = .kill)
    (ha : x.verdict.accepted = true) (hp : (pol x.session).killSetsTombstone = true) :
    ∀ y ∈ post, y.verdict.claimed = false := by
  have hx : x ∈ log := by rw [hsplit]; simp
  have ht := kill_commit (dig := dig) (fun _ => .init) (hlog ▸ hx) hk ha hp
  have htomb := tomb_afterP (dig := dig) (fun _ => .init) (hlog ▸ hdis) (hlog ▸ hsplit) hnoclear ht
  exact fun y hy => multi_kill hlog hdis (by rw [hsplit]; simp [hy]) (htomb y hy)

/-- Section 8, theorem 9 over several policies that agree on principal meter `m`: a step never
drops another session's entry on `m` that `m`'s usage still counts at a time `t` no earlier than
the step. The stepping session's own entries are excluded: its commit and release change them. -/
theorem multi_window (hagree : MeterAgree pol m)
    (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hx : x ∈ log) (hs : (pol i).meter? m = some spec)
    (hsc : spec.scope = .principal) (hen : en ∈ x.storedBefore.entries) (hm : en.meter = m)
    (hother : en.session ≠ x.pre.sessionId) (ht : x.event.time ≤ t)
    (hin : 0 < usageAt spec [en] m t) :
    en ∈ x.storedAfter.entries := by
  subst hlog
  obtain ⟨hR, -, hst⟩ := memP (dig := dig) (fun _ => .init) hx
  rw [hst]
  split
  · rename_i hw
    rw [← hdis x hx hw.1 hw.2] at hen
    refine ((step_others hR hw.1).2 en hen hother).resolve_right fun hp => ?_
    unfold PrunedAt at hp
    rw [hm] at hp
    cases hs' : (pol x.session).meter? m with
    | none => rw [hs'] at hp; cases hp
    | some spec' =>
      rw [hs'] at hp
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨hsc', hexp⟩ := hp
      have hw' := (hagree _ _ _ _ hs' hs hsc' hsc).2
      unfold MeterSpec.expired MeterSpec.inWindow MeterSpec.inWindowAt at hexp
      rw [hw'] at hexp
      cases hwin : spec.windowMs with
      | none => simp [hwin] at hexp
      | some w =>
        simp [hwin] at hexp
        simp [usageAt, hm, hwin] at hin
        split at hin <;> split at hin <;> omega
  · exact hen

/-- Section 8, theorem 9 and section 7 over several policies: once a session has seen the
tombstone on its ledger, none of its later steps claims, even after the stored tombstone is
cleared out of band. -/
theorem multi_cleared (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hsplit : log = pre ++ x :: post) (ht : x.pre.ledger.tombstone = true) :
    ∀ y ∈ post, y.session = x.session → y.verdict.claimed = false := by
  subst hlog
  have hx : x ∈ interleaveP pol L (fun i => State.initial (dig i)) ops := by rw [hsplit]; simp
  have hR := (memP (dig := dig) (fun _ => .init) hx).1
  obtain ⟨S', rest, hS', -, hsx, hpost⟩ := suffixP (dig := dig) (fun _ => .init) hsplit
  have hshut : Shut (S' x.session) := by
    rw [hsx]; exact shut_step hR (.inr ⟨started_of_tomb hR ht, ht⟩)
  intro y hy hys
  subst hpost
  obtain ⟨-, hv, -⟩ := memP hS' hy
  rw [hv]
  exact shut_unclaimed (shut_mem hS' hshut y hy hys)

theorem interleave_eq :
    interleave p d L S sched = interleaveP (fun _ => p) L S (sched.map fun (i, e) => .step i e) := by
  induction sched generalizing L S with
  | nil => rfl
  | cons ie rest ih =>
    obtain ⟨i, e⟩ := ie
    exact congrArg (List.cons _) ih

theorem disciplined_eq : Disciplined p log ↔ DisciplinedP (fun _ => p) log := Iff.rfl

/-- Section 8, theorem 9 and section 7: once the stored ledger carries the tombstone, set by a
`kill` or out of band, no later step of any session claims. -/
theorem ledger_kill_stored (hS : ∀ i, Reachable p d (S i)) (hL : L.tombstone = true)
    (hdis : Disciplined p (interleave p d L S sched)) :
    ∀ y ∈ interleave p d L S sched, y.verdict.claimed = false := by
  rw [interleave_eq] at hdis ⊢
  intro y hy
  exact no_claim_storedP hS (disciplined_eq.mp hdis) hy
    (tombP hL store_false_not_mem (disciplined_eq.mp hdis) y hy)

/-- Section 8, theorem 9: every step of the interleaving is taken on a reachable state. -/
theorem interleave_reachable
    (hx : x ∈ interleave p d L (fun _ => State.initial d) sched) : Reachable p d x.pre :=
  multi_reachable (dig := fun _ => d) interleave_eq hx

/-- Section 8, theorem 9: a claim on a principal meter found room on the stored ledger it read,
and the ledger it stored stays within the cap. -/
theorem ledger_cap (hwf : p.WF) (hlog : log = interleave p d L (fun _ => State.initial d) sched)
    (hdis : Disciplined p log) (hx : x ∈ log) (h : x.verdict.claimed = true)
    (he : x.event.body = .dispatch k n dg cost g key) (hc : x.pre.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters)
    (hs : p.meter? m = some spec) (hsc : spec.scope = .principal) (hcap : spec.cap = some cap)
    (hfresh : c.status = .authorized ∨
      ∀ en ∈ ownEntries p x.pre m k, spec.windowMs.all (en.time + · > x.event.time) = false) :
    usageAt spec x.storedBefore.entries m x.event.time + draw spec c.cost ≤ cap ∧
      usageAt spec x.storedAfter.entries m x.event.time ≤ cap := by
  rw [interleave_eq] at hlog
  exact multi_cap (pol := fun _ => p) (dig := fun _ => d) hwf hlog (disciplined_eq.mp hdis) hx h
    he hc hm hr hmr hs hsc hcap hfresh

/-- Section 8, theorem 9: once a committed step stores the tombstone, no later step of any
session claims. -/
theorem ledger_kill (hlog : log = interleave p d L (fun _ => State.initial d) sched)
    (hdis : Disciplined p log) (hsplit : log = pre ++ x :: post)
    (ht : x.storedAfter.tombstone = true) : ∀ y ∈ post, y.verdict.claimed = false := by
  rw [interleave_eq] at hlog
  have hdis' := disciplined_eq.mp hdis
  have htomb := tomb_afterP (dig := fun _ => d) (fun _ => .init) (hlog ▸ hdis') (hlog ▸ hsplit)
    store_false_not_mem ht
  exact fun y hy => multi_kill hlog hdis' (by rw [hsplit]; simp [hy]) (htomb y hy)

/-- Section 8, theorem 9: after an accepted `kill` under `kill_sets_tombstone`, no later step of
any session claims. -/
theorem ledger_kill_event (hlog : log = interleave p d L (fun _ => State.initial d) sched)
    (hdis : Disciplined p log) (hsplit : log = pre ++ x :: post) (hk : x.event.body = .kill)
    (ha : x.verdict.accepted = true) (hp : p.killSetsTombstone = true) :
    ∀ y ∈ post, y.verdict.claimed = false := by
  rw [interleave_eq] at hlog
  exact multi_kill_event (dig := fun _ => d) hlog (disciplined_eq.mp hdis) hsplit
    store_false_not_mem hk ha hp

variable {y : Commit} {opsPre opsPost : List Op}

namespace Interleave

theorem events_eq : (interleaveP pol L S ops).map (·.event) = ops.filterMap Op.event? := by
  induction ops generalizing L S with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | step i e => exact congrArg (List.cons e) ih
    | store b => exact ih

theorem time_le (hord : TimeOrdered ops) (hsplit : interleaveP pol L S ops = pre ++ x :: post)
    (hy : y ∈ post) : x.event.time ≤ y.event.time := by
  have hp : (interleaveP pol L S ops).Pairwise fun a b => a.event.time ≤ b.event.time := by
    unfold TimeOrdered at hord
    rw [← events_eq (pol := pol) (L := L) (S := S)] at hord
    exact (List.pairwise_map (R := fun a b : Event => a.time ≤ b.time)).mp hord
  rw [hsplit] at hp
  exact (List.pairwise_cons.mp (List.pairwise_append.mp hp).2.1).1 y hy

/-- The commits after the op at the split point of the schedule are those of the ops after it,
run from the stored ledger and sessions that commit left. -/
theorem split_ops :
    ∀ (opsPre : List Op) (L : Ledger) (S : Nat → State) (pre : List Commit),
      (∀ i, Reachable (pol i) (dig i) (S i)) →
      interleaveP pol L S (opsPre ++ Op.step i e :: opsPost) = pre ++ x :: post →
      pre.length = (opsPre.filterMap Op.event?).length →
      x.session = i ∧ x.event = e ∧ ∃ S', (∀ i, Reachable (pol i) (dig i) (S' i)) ∧
        post = interleaveP pol x.storedAfter S' opsPost
  | [], L, S, pre, hS, h, hlen => by
    rw [List.filterMap_nil, List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    injection h with hx hp
    subst hx
    exact ⟨rfl, rfl, _, update_reach hS, hp.symm⟩
  | .step j e' :: rest, L, S, pre, hS, h, hlen => by
    cases pre with
    | nil => simp [Op.event?] at hlen
    | cons a pre =>
      injection h with _ hp
      exact split_ops rest _ _ pre (update_reach hS) hp
        (by simpa [List.filterMap_cons, Op.event?] using hlen)
  | .store b :: rest, L, S, pre, hS, h, hlen =>
    split_ops rest _ _ pre hS h (by simpa [List.filterMap_cons, Op.event?] using hlen)

end Interleave

/-- Section 8, theorem 9 over several policies, every claim changes the stored ledger: under the
discipline a claim read the stored ledger and stored the ledger it produced, at a higher version,
and that ledger holds the call's uncommitted entry on each principal meter of its action, with the
claiming session's id and the call's draw. For a first attempt the entry is new: it is dated at the
claim, and the stored ledger before had no entry of that session and call on the meter. -/
theorem claim_stored (hwf : (pol x.session).WF)
    (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hx : x ∈ log) (h : x.verdict.claimed = true)
    (he : x.event.body = .dispatch k n dg cost g key) (hc : x.pre.calls[k]? = some c)
    (hr : (pol x.session).action? c.tool = some r) :
    x.pre.ledger = x.storedBefore ∧
      x.storedAfter = (step (pol x.session) x.pre x.event).1.ledger ∧
      x.storedBefore.version < x.storedAfter.version ∧
      ∀ m spec, m ∈ r.meters → (pol x.session).meter? m = some spec → spec.scope = .principal →
        ∃ en ∈ x.storedAfter.entries, en.meter = m ∧ en.session = x.pre.sessionId ∧
          en.call = k ∧ en.committed = false ∧ en.excess = 0 ∧ en.amount = draw spec c.cost ∧
          (c.status = .authorized → en.time = x.event.time ∧
            ∀ en' ∈ x.storedBefore.entries, en'.meter = m → en'.session = x.pre.sessionId →
              en'.call ≠ k) := by
  subst hlog
  obtain ⟨hR, h', hpre, hst⟩ := claim_commit (dig := dig) (fun _ => .init) hdis hx h
  have hpost := claim_post h' he hc
  have hsid := (claim_others (p := pol x.session) (s := x.pre) (t := x.event.time) (k := k)
    (c := c) (r := ((pol x.session).action? c.tool).getD {}) (retry := c.status == .unknown)
    (key := key)).1
  refine ⟨hpre, hst, ?_, fun m spec hm hs hsc => ?_⟩
  · rw [← hpre, hst, hpost]
    exact claim_version (key := key)
  have hent : ∀ s', entriesOf (pol x.session) s' m = s'.ledger.entries := fun _ => by
    simp [entriesOf, hs, hsc]
  have hacc := accounting_reachable hwf (Reachable.step (e := x.event) hR)
  have hk' : (step (pol x.session) x.pre x.event).1.calls[k]? = some
      { c with status := .dispatched, attempts := c.attempts + 1, idempotencyKey := some key } := by
    rw [hpost]
    show (claim _ _ _ _ _ _ _ _).calls[k]? = _
    rw [AtMostOnce.claim_state.1, Std.ExtTreeMap.getElem?_insert_self]
  obtain ⟨en, hen, hu, hx0, hamt⟩ :=
    hacc.held k _ r m spec hk' hr hm hs (Nat.le_add_left _ _) (.inl rfl)
  have hin : en ∈ ownEntries (pol x.session) (step (pol x.session) x.pre x.event).1 m k := by
    rw [hen]; exact List.mem_singleton_self en
  obtain ⟨hmem, hdec⟩ := List.mem_filter.mp hin
  simp only [decide_eq_true_eq] at hdec
  obtain ⟨hm', hs', hk⟩ := hdec
  rw [hent] at hmem
  refine ⟨en, by rw [hst]; exact hmem, hm', ?_, hk, hu, hx0, hamt, fun hau => ?_⟩
  · rw [hs', hpost]; exact hsid
  have hinv := Accounting.inv_reachable hwf hR
  have h0 : c.attempts = 0 := (hinv.recs k c hc).2.1 (.inr hau)
  have hnone : ownEntries (pol x.session) x.pre m k = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun en' hen' => by
      obtain ⟨c', r', hc', ha, -⟩ := hinv.owner m k en' hen'
      rw [hc] at hc'
      cases hc'
      omega
  have hret : (c.status == .unknown) = false := by rw [hau]; rfl
  obtain ⟨x₀, hx₀, -, -, -, ht₀⟩ := Accounting.claim_first_self (p := pol x.session) (s := x.pre)
    (t := x.event.time) (c := c) (key := key) (WF.meters_nodup hwf hr) hm hnone
  have hsame : ownEntries (pol x.session) (step (pol x.session) x.pre x.event).1 m k =
      ownEntries (pol x.session)
        (claim (pol x.session) x.pre x.event.time k c r false key) m k := by
    rw [hpost, hret, hr]; rfl
  rw [hen, hx₀] at hsame
  cases hsame
  refine ⟨ht₀, fun en' hen' hm₁ hs₁ hk₁ => ?_⟩
  have : en' ∈ ownEntries (pol x.session) x.pre m k :=
    List.mem_filter.mpr ⟨by rw [hent, hpre]; exact hen', by simp [hm₁, hs₁, hk₁]⟩
  rw [hnone] at this
  cases this

/-- Section 8, theorem 9 over several policies on the trusted monotone clock of section 10: when
the schedule's event times never decrease, a commit never drops from the stored ledger an entry on
principal meter `m`, written under another session id, that `m`'s usage still counts at the time of
that commit or of any later one. -/
theorem multi_window_ordered (hagree : MeterAgree pol m)
    (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hord : TimeOrdered ops) (hsplit : log = pre ++ x :: post)
    (hy : y ∈ x :: post) (hs : (pol i).meter? m = some spec) (hsc : spec.scope = .principal)
    (hen : en ∈ x.storedBefore.entries) (hm : en.meter = m) (hother : en.session ≠ x.pre.sessionId)
    (hin : 0 < usageAt spec [en] m y.event.time) :
    en ∈ x.storedAfter.entries := by
  have hx : x ∈ log := by rw [hsplit]; simp
  have ht : x.event.time ≤ y.event.time := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_refl _
    · exact time_le hord (by rw [← hlog]; exact hsplit) hy
  exact multi_window hagree hlog hdis hx hs hsc hen hm hother ht hin

/-- Section 8, theorem 9 over several policies: after an accepted `kill` under the killing
session's `kill_sets_tombstone`, no later step of any session claims while no out-of-band clear
follows the kill. `x` is the commit of the kill's op: the schedule splits at that op, and the
commits before `x` are those of the ops before it. Clears before the kill are allowed. -/
theorem multi_kill_after (hlog : log = interleaveP pol L (fun i => State.initial (dig i)) ops)
    (hdis : DisciplinedP pol log) (hops : ops = opsPre ++ .step x.session x.event :: opsPost)
    (hsplit : log = pre ++ x :: post) (hlen : pre.length = (opsPre.filterMap Op.event?).length)
    (hnoclear : Op.store false ∉ opsPost) (hk : x.event.body = .kill)
    (ha : x.verdict.accepted = true) (hp : (pol x.session).killSetsTombstone = true) :
    ∀ y ∈ post, y.verdict.claimed = false := by
  have hx : x ∈ log := by rw [hsplit]; simp
  have hmem : ∀ y ∈ post, y ∈ log := fun y hy => by rw [hsplit]; simp [hy]
  have ht := kill_commit (dig := dig) (fun _ => .init) (hlog ▸ hx) hk ha hp
  obtain ⟨-, -, S', -, hpost⟩ := split_ops (dig := dig) opsPre L _ pre
    (fun _ => .init) (by rw [← hops, ← hlog, hsplit]) hlen
  have htomb := tombP ht hnoclear (S := S') (pol := pol)
    (fun z hz => hdis z (hmem z (hpost ▸ hz)))
  exact fun y hy => multi_kill hlog hdis (hmem y hy) (htomb y (hpost ▸ hy))

namespace Interleave

def lusd : MeterSpec := { unit := .money "USD", cap := some 100, scope := .principal }

def ledgerPolicy : Policy :=
  { meters := [("usd", lusd)], actions := [("t", Meters.capAction)], killSetsTombstone := true }

def start (sid : String) : Event := ⟨1, 1, 0, none, .sessionStart sid "pd" "u1" [] [] {}⟩

def turn : Event := ⟨2, 2, 1, none, .turnStart true⟩

def propose₀ : Event := ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨60, "USD"⟩) [] []⟩

def dispatch₀ : Event := ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩

def claim₀ : List Event := [start "s0", turn, propose₀, dispatch₀]

/-- Session 1 syncs the ledger session 0 stored, so its claim of 60 finds 60 already spent. -/
def capSched (sync : Bool) : List (Nat × Event) :=
  [ (0, start "s0"), (1, start "s1"), (0, turn), (0, propose₀), (1, turn), (1, propose₀)
  , (0, dispatch₀) ] ++
  if sync then
    [ (1, ⟨4, 5, 3, none, .ledgerSync (after ledgerPolicy "pd" claim₀).ledger⟩)
    , (1, ⟨5, 6, 4, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩)
    , (1, ⟨6, 7, 4, none, .propose "c2" "t" "d2" (some ⟨40, "USD"⟩) [] []⟩)
    , (1, ⟨7, 8, 5, none, .dispatch "c2" 1 "d2" (some ⟨40, "USD"⟩) [] "k2"⟩) ]
  else [(1, ⟨4, 5, 3, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩)]

def capLog (sync : Bool) : List Commit :=
  interleave ledgerPolicy "pd" {} (fun _ => State.initial "pd") (capSched sync)

#guard decide ledgerPolicy.WF
#guard ledgerPolicy.modeOf "t" == .enforce
#guard ledgerPolicy.meter? "usd" == some lusd
#guard decide (Disciplined ledgerPolicy (capLog true))
#guard (capLog true).map (·.verdict) ==
  [ .ok .none none, .ok .none none, .ok .none none, .ok .allowed none, .ok .none none
  , .ok .allowed none, .ok .dispatchClaimed none, .ok .none none, .rejected .meterExceeded
  , .ok .allowed none, .ok .dispatchClaimed none ]
#guard ((capLog true)[10]?).any fun x =>
  x.session == 1 && x.event.body == .dispatch "c2" 1 "d2" (some ⟨40, "USD"⟩) [] "k2" &&
  (x.pre.calls["c2"]?).any (·.status == .authorized) &&
  usageAt lusd x.storedBefore.entries "usd" x.event.time == 60 &&
  usageAt lusd x.storedAfter.entries "usd" x.event.time == 100
#guard ((capLog true)[6]?).any fun x =>
  x.session == 0 && usageAt lusd x.storedAfter.entries "usd" x.event.time == 60

-- Without the sync, session 1 claims 60 on a ledger older than the stored one.
#guard ((capLog false).map (·.verdict.claimed)).count true == 2
#guard !decide (Disciplined ledgerPolicy (capLog false))

def kill₀ : List Event := [start "s0", turn, ⟨3, 3, 2, none, .kill⟩]

def killSched (kill : Bool) : List (Nat × Event) :=
  [ (0, start "s0"), (1, start "s1"), (0, turn), (1, turn)
  , (1, ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨10, "USD"⟩) [] []⟩) ] ++
  (if kill then
    [(0, ⟨3, 3, 2, none, .kill⟩),
     (1, ⟨4, 4, 3, none, .ledgerSync (after ledgerPolicy "pd" kill₀).ledger⟩)]
   else []) ++
  [ (1, ⟨5, 5, if kill then 4 else 3, none,
      .dispatch "c1" 1 "d1" (some ⟨10, "USD"⟩) [] "k1"⟩) ]

def killLog (kill : Bool) : List Commit :=
  interleave ledgerPolicy "pd" {} (fun _ => State.initial "pd") (killSched kill)

#guard decide (Disciplined ledgerPolicy (killLog true))
#guard ((killLog true)[5]?).any fun x =>
  x.session == 0 && x.event.body == .kill && x.verdict.accepted && x.storedAfter.tombstone
#guard (killLog true).map (·.verdict) ==
  [ .ok .none none, .ok .none none, .ok .none none, .ok .none none, .ok .allowed none
  , .ok .none none, .ok .none none, .rejected .killed ]
#guard ((killLog true).drop 6).all (!·.verdict.claimed)
#guard ((killLog false).getLast?.map (·.verdict)) == some (.ok .dispatchClaimed none)

/-- The store holds a tombstone set out of band. A session that starts on it is refused its turn,
proposal and dispatch; one that starts on an older ledger claims, which the discipline forbids. -/
def storedSched (onStored : Bool) : List (Nat × Event) :=
  let v := if onStored then 1 else 2
  [ (0, ⟨1, 1, 0, none, .sessionStart "s0" "pd" "u1" [] []
      (if onStored then { tombstone := true } else {})⟩)
  , (0, turn)
  , (0, ⟨3, 3, v, none, .propose "c1" "t" "d1" (some ⟨10, "USD"⟩) [] []⟩)
  , (0, ⟨4, 4, v + 1, none, .dispatch "c1" 1 "d1" (some ⟨10, "USD"⟩) [] "k1"⟩) ]

def storedLog (onStored : Bool) : List Commit :=
  interleave ledgerPolicy "pd" { tombstone := true } (fun _ => State.initial "pd")
    (storedSched onStored)

#guard decide (Disciplined ledgerPolicy (storedLog true))
#guard (storedLog true).map (·.verdict) ==
  [.ok .none none, .rejected .killed, .ok (.denied .killed) none, .rejected .killed]
#guard (storedLog true).all (!·.verdict.claimed)
#guard ((storedLog false).getLast?.map (·.verdict)) == some (.ok .dispatchClaimed none)
#guard !decide (Disciplined ledgerPolicy (storedLog false))

def twoPol (i : Nat) : Policy :=
  if i = 0 then ledgerPolicy
  else { ledgerPolicy with meters := [("usd", { lusd with cap := some 200 })] }

def propose₁ : Event := ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨120, "USD"⟩) [] []⟩

def dispatch₁ (seq v : Nat) : Event :=
  ⟨seq, seq, v, none, .dispatch "c1" 1 "d1" (some ⟨120, "USD"⟩) [] "k1"⟩

def twoSched (sync : Bool) : List Op :=
  [ .step 0 (start "s0"), .step 1 (start "s1"), .step 0 turn, .step 0 propose₀, .step 1 turn
  , .step 1 propose₁, .step 0 dispatch₀ ] ++
  if sync then
    [ .step 1 ⟨4, 5, 3, none, .ledgerSync (after ledgerPolicy "pd" claim₀).ledger⟩
    , .step 1 (dispatch₁ 6 4) ]
  else [.step 1 (dispatch₁ 5 3)]

def twoLog (sync : Bool) : List Commit :=
  interleaveP twoPol {} (fun _ => State.initial "pd") (twoSched sync)

-- Policy 0 is ledgerPolicy; policy 1 is ledgerPolicy with cap 200 on "usd".
-- Session 0 (policy 0) claims 60; session 1 (policy 1) syncs and claims 120: 180 stays under 200,
-- the cap of the claiming policy.
#guard decide (DisciplinedP twoPol (twoLog true))
#guard ((twoLog true).map (·.verdict.claimed)).count true == 2
#guard ((twoLog true).getLast?).any fun x =>
  x.session == 1 && usageAt lusd x.storedAfter.entries "usd" x.event.time == 180
#guard !decide (DisciplinedP twoPol (twoLog false))

/-- Session 0 proposes; an out-of-band kill then sets the stored tombstone, session 1 starts on
it and session 0 syncs it, so neither dispatch claims. Without the store op session 1 starts on
the empty ledger. -/
def storeKillSched (store : Bool) : List Op :=
  -- Session 1's turn is refused on the tombstone, so its proposal comes one version earlier.
  let v := if store then 1 else 2
  [.step 0 (start "s0"), .step 0 turn, .step 0 propose₀] ++ (if store then [.store true] else []) ++
  [ .step 1 ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] (storeLedger {} store)⟩
  , .step 1 turn, .step 1 { propose₁ with stateVersion := v }, .step 1 (dispatch₁ 4 (v + 1))
  , .step 0 ⟨4, 4, 3, none, .ledgerSync (storeLedger {} store)⟩
  , .step 0 ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩ ]

def storeKillLog (store : Bool) : List Commit :=
  interleaveP twoPol {} (fun _ => State.initial "pd") (storeKillSched store)

-- A store op sets the tombstone between them: session 1 starts on it and claims nothing.
#guard (storeKillLog true).all (!·.verdict.claimed)
#guard decide (DisciplinedP twoPol (storeKillLog true))
#guard (storeKillLog true).map (·.verdict) ==
  [ .ok .none none, .ok .none none, .ok .allowed none, .ok .none none, .rejected .killed
  , .ok (.denied .killed) none, .rejected .killed, .ok .none none, .rejected .killed ]
#guard ((storeKillLog false).filter (·.session == 1)).any (·.verdict.claimed)

def wspec (w : Nat) : MeterSpec :=
  { unit := .money "USD", cap := some 100, scope := .principal, windowMs := some w }

def shortPol : Policy := { meters := [("usd", wspec 100)], actions := [("t", Meters.capAction)] }

def longPol : Policy := { meters := [("usd", wspec 1000)], actions := [("t", Meters.capAction)] }

def windowPol (i : Nat) : Policy := if i = 0 then shortPol else longPol

def settle₁ : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩, turn
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨60, "USD"⟩) [] []⟩
  , ⟨4, 10, 3, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩
  , ⟨5, 20, 4, none, .result "c1" .succeeded none false⟩ ]

def prune₀ : List Event :=
  [ ⟨1, 30, 0, none, .sessionStart "s0" "pd" "u1" [] [] (after longPol "pd" settle₁).ledger⟩
  , ⟨2, 31, 1, none, .turnStart true⟩
  , ⟨3, 32, 2, none, .propose "c1" "t" "d1" (some ⟨10, "USD"⟩) [] []⟩
  , ⟨4, 200, 3, none, .dispatch "c1" 1 "d1" (some ⟨10, "USD"⟩) [] "k1"⟩ ]

/-- Session 1 (window 1000 ms) claims 60 at time 10 and settles it; session 0 (window 100 ms)
claims 10 at time 200, which prunes that committed entry; session 1 syncs and claims 60 again at
time 300. -/
def windowSched : List Op :=
  settle₁.map (.step 1) ++ prune₀.map (.step 0) ++
  [ .step 1 ⟨6, 250, 5, none, .ledgerSync (after shortPol "pd" prune₀).ledger⟩
  , .step 1 ⟨7, 260, 6, none, .propose "c2" "t" "d2" (some ⟨60, "USD"⟩) [] []⟩
  , .step 1 ⟨8, 300, 7, none, .dispatch "c2" 1 "d2" (some ⟨60, "USD"⟩) [] "k2"⟩ ]

def windowLog : List Commit := interleaveP windowPol {} (fun _ => State.initial "pd") windowSched

-- Both of session 1's claims succeed: 130 spent inside its 1000 ms window against a cap of 100,
-- while the stored ledger counts 70.
#guard decide (DisciplinedP windowPol windowLog)
#guard (((windowLog).filter (·.session == 1)).map (·.verdict.claimed)).count true == 2
#guard ((windowLog).getLast?).any fun x =>
  x.session == 1 && usageAt (wspec 1000) x.storedAfter.entries "usd" x.event.time == 70

theorem windowPol_disagree : ¬ MeterAgree windowPol "usd" := fun h =>
  absurd (h 0 1 (wspec 100) (wspec 1000) rfl rfl rfl rfl).2 (by decide)

/-- Session 0 sees an out-of-band tombstone and a clear; its sync of the cleared ledger is refused
and its dispatch does not claim, while session 1, started on the cleared ledger, claims. -/
def clearSched : List Op :=
  [ .step 0 (start "s0"), .step 0 turn, .step 0 propose₀, .store true
  , .step 0 ⟨4, 4, 3, none, .ledgerSync (storeLedger {} true)⟩, .store false
  , .step 0 ⟨5, 5, 4, none, .ledgerSync (storeLedger (storeLedger {} true) false)⟩
  , .step 0 ⟨6, 6, 4, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩
  , .step 1 ⟨1, 1, 0, none,
      .sessionStart "s1" "pd" "u1" [] [] (storeLedger (storeLedger {} true) false)⟩
  , .step 1 turn, .step 1 propose₀, .step 1 dispatch₀ ]

def clearLog : List Commit := interleaveP twoPol {} (fun _ => State.initial "pd") clearSched

#guard decide (DisciplinedP twoPol clearLog)
#guard ((clearLog).filter (·.session == 0)).all (!·.verdict.claimed)
#guard ((clearLog).filter (·.session == 1)).any (·.verdict.claimed)
-- Session 0's dispatch reads a stored ledger without the tombstone, so `multi_kill` does not apply.
#guard (clearLog[5]?).any fun x =>
  x.session == 0 && !x.storedBefore.tombstone && x.verdict == .rejected .killed
#guard (clearLog).any fun x => x.session == 0 && x.verdict == .rejected .ledgerConflict

-- `claim_stored`: session 0's first claim reads the stored ledger and stores a new uncommitted
-- entry of its own id for its draw, dated at the claim, at a higher version.
#guard ((capLog true)[6]?).any fun x =>
  x.verdict.claimed && x.pre.ledger == x.storedBefore &&
  x.storedBefore.version < x.storedAfter.version &&
  x.storedAfter.entries.any (fun en => en.meter == "usd" && en.session == "s0" &&
    en.call == "c1" && !en.committed && en.excess == 0 && en.amount == 60 &&
    en.time == x.event.time) &&
  !x.storedBefore.entries.any fun en => en.session == "s0" && en.call == "c1"

def agreePol (_ : Nat) : Policy := longPol

theorem agreePol_agree : MeterAgree agreePol "usd" := fun _ _ _ _ hi hj _ _ => by
  simp only [agreePol] at hi hj
  rw [hi] at hj
  cases hj
  exact ⟨rfl, rfl⟩

def prune' (t : Nat) : List Event :=
  [ ⟨1, t, 0, none, .sessionStart "s0" "pd" "u1" [] [] (after longPol "pd" settle₁).ledger⟩
  , ⟨2, t + 1, 1, none, .turnStart true⟩
  , ⟨3, t + 2, 2, none, .propose "c1" "t" "d1" (some ⟨10, "USD"⟩) [] []⟩
  , ⟨4, t + 10, 3, none, .dispatch "c1" 1 "d1" (some ⟨10, "USD"⟩) [] "k1"⟩ ]

/-- Session 1 (window 1000 ms) claims 60 at time 10 and settles it; session 0, under the same
policy, claims 10 at time `t + 10`; session 1 syncs and asks for 60 more at time 300. -/
def clockSched (t : Nat) : List Op :=
  settle₁.map (.step 1) ++ (prune' t).map (.step 0) ++
  [ .step 1 ⟨6, 250, 5, none, .ledgerSync (after longPol "pd" (prune' t)).ledger⟩
  , .step 1 ⟨7, 260, 6, none, .propose "c2" "t" "d2" (some ⟨60, "USD"⟩) [] []⟩
  , .step 1 ⟨8, 300, 7, none, .dispatch "c2" 1 "d2" (some ⟨60, "USD"⟩) [] "k2"⟩ ]

def clockLog (t : Nat) : List Commit :=
  interleaveP agreePol {} (fun _ => State.initial "pd") (clockSched t)

/-- Session 0's claim keeps an entry of session 1 that the usage at time 300 still counts. -/
def keeps (x : Commit) : Bool :=
  x.storedBefore.entries.any fun en =>
    en.session == "s1" && 0 < usageAt (wspec 1000) [en] "usd" 300 &&
      x.storedAfter.entries.contains en

-- `multi_window_ordered`: on one clock (session 0 at times 30 to 40) session 0's claim keeps
-- session 1's committed 60, and session 1's later proposal of 60 more is denied at the cap.
#guard decide (TimeOrdered (clockSched 30))
#guard decide (DisciplinedP agreePol (clockLog 30))
#guard ((clockLog 30)[8]?).any fun x => x.session == 0 && x.verdict.claimed && keeps x
#guard ((clockLog 30)[10]?).map (·.verdict) == some (.ok (.denied .meterExceeded) none)

-- With session 0's clock at 1990 to 2000, ahead of session 1, its claim prunes that entry and
-- session 1's request at time 300 claims: 130 inside session 1's window against a cap of 100.
#guard !decide (TimeOrdered (clockSched 1990))
#guard decide (DisciplinedP agreePol (clockLog 1990))
#guard ((clockLog 1990)[8]?).any fun x =>
  x.session == 0 && x.verdict.claimed && !keeps x &&
    x.storedBefore.entries.any fun en => en.session == "s1" && 0 < usageAt (wspec 1000) [en] "usd" 300
#guard ((clockLog 1990).getLast?.map (·.verdict)) == some (.ok .dispatchClaimed none)

def cleared : Ledger := storeLedger (storeLedger {} true) false

def startOn (sid : String) : Event := ⟨1, 1, 0, none, .sessionStart sid "pd" "u1" [] [] cleared⟩

def killAfterClear : List Event := [startOn "s0", turn, ⟨3, 3, 2, none, .kill⟩]

/-- An out-of-band set and clear come first; then session 0 kills, and session 1 syncs and
dispatches. -/
def clearKillSched (kill : Bool) : List Op :=
  [ .store true, .store false, .step 0 (startOn "s0"), .step 1 (startOn "s1"), .step 0 turn
  , .step 1 turn, .step 1 ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨10, "USD"⟩) [] []⟩ ] ++
  (if kill then
    [ .step 0 ⟨3, 3, 2, none, .kill⟩
    , .step 1 ⟨4, 4, 3, none, .ledgerSync (after ledgerPolicy "pd" killAfterClear).ledger⟩ ]
   else []) ++
  [ .step 1 ⟨5, 5, if kill then 4 else 3, none, .dispatch "c1" 1 "d1" (some ⟨10, "USD"⟩) [] "k1"⟩ ]

def clearKillLog (kill : Bool) : List Commit :=
  interleaveP (fun _ => ledgerPolicy) {} (fun _ => State.initial "pd") (clearKillSched kill)

-- `multi_kill_after`: the schedule holds a clear, so `multi_kill_event` says nothing; the clear
-- comes before the kill (op 7, commit 5), and no commit after the kill claims.
#guard (clearKillSched true).any fun | .store false => true | _ => false
#guard decide (DisciplinedP (fun _ => ledgerPolicy) (clearKillLog true))
#guard ((clearKillSched true)[7]?).any fun
  | .step i e => i == 0 && e.body == .kill
  | .store _ => false
#guard (((clearKillSched true).take 7).filterMap Op.event?).length == 5
#guard ((clearKillLog true)[5]?).any fun x =>
  x.session == 0 && x.event.body == .kill && x.verdict.accepted
#guard ((clearKillSched true).drop 8).all fun | .store false => false | _ => true
#guard ((clearKillLog true).drop 6).all (!·.verdict.claimed)
#guard ((clearKillLog true).getLast?.map (·.verdict)) == some (.rejected .killed)
#guard ((clearKillLog false).getLast?.map (·.verdict)) == some (.ok .dispatchClaimed none)

end Interleave

end Writ.Proofs
