import WritProofs.Basic

namespace Writ.Proofs

open Writ
open Basic

variable {p : Policy} {d : String} {s : State} {e : Event} {es : List Event}

namespace Kill

theorem releaseGrant_killed : (s.releaseGrant k).killed = s.killed := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem recordFailure_killed : (s.recordFailure p t).killed = s.killed := by
  unfold State.recordFailure; dsimp only; repeat' split
  all_goals rfl

theorem updateEntries_killed : (s.updateEntries p m t f).killed = s.killed := by
  unfold State.updateEntries; split <;> rfl

theorem settle_killed : (s.settle p ms k o a ne t).1.killed = s.killed := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.killed = s.killed) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · rw [State.release, updateEntries_killed, h]
  · split <;> rw [State.commit, updateEntries_killed, h]

theorem endCall_killed : (s.endCall k st).killed = s.killed := by
  unfold State.endCall; dsimp only; rw [releaseGrant_killed]

theorem cancelPending_killed : (cancelPending s).killed = s.killed := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b : State => b.killed = s.killed) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split <;> first | exact ha | rw [endCall_killed, ha]

theorem interrupt_killed : s.interrupt.killed = s.killed := by
  unfold State.interrupt; dsimp only; rw [cancelPending_killed]

theorem stepHandle_killed (hk : s.killed = true) (hn : stepEnvelope s e = none) :
    (stepHandle p s e).1.killed = true := by
  unfold stepHandle
  split <;> rename_i hb
  -- The envelope admits a killed session only the events that stay open after a kill, so only
  -- those seven handlers are left to keep the flag.
  all_goals try
    (exfalso; unfold stepEnvelope at hn; simp [hb, hk] at hn
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
      | unfold handleLedgerSync
    repeat' (first | (dsimp only) | split)
  all_goals simp only [withStatus, settle_killed, recordFailure_killed, State.recordSuccess,
    interrupt_killed, cancelPending_killed, hk]

end Kill

open Kill

theorem killed_stays : s.killed = true → (step p s e).1.killed = true := by
  intro hk
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact hk
  · rw [accepted_step ha]
    exact stepHandle_killed hk (accepted_open ha)

theorem kill_accepted_sets (hk : e.body = .kill) (h : (step p s e).2.accepted = true) :
    (step p s e).1.killed = true := by
  rw [accepted_step h]
  show (stepHandle p s e).1.killed = true
  unfold stepHandle
  rw [hk]
  rfl

namespace Kill

theorem repeatDecision_killed (hf : (s.killed || s.ledger.tombstone) = true) :
    repeatDecision p s t k rc = (.denied .killed, none) := by
  unfold repeatDecision
  dsimp only
  simp only [hf, ↓reduceIte]

theorem handlePropose_halted (hf : (s.killed || s.ledger.tombstone) = true) :
    (handlePropose p s t k tool dg c g x).2.claimed = false := by
  cases h : (handlePropose p s t k tool dg c g x).2.claimed
  · rfl
  · exfalso
    unfold handlePropose at h
    split at h
    · split at h
      · rw [repeatDecision_killed hf] at h; cases h
      · cases h
    · repeat' (first | (dsimp only at h) | split at h)
      all_goals rw [disposition_unclaimed] at h; cases h

theorem no_claim_halted (hf : (s.killed || s.ledger.tombstone) = true) :
    (step p s e).2.claimed = false := by
  cases hc : (step p s e).2.claimed
  · rfl
  · exfalso
    have hn := accepted_open (claimed_accepted hc)
    have hh := step_claimed hc
    rcases stepHandle_claimed hh with
      ⟨_, _, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, _, _, hb, _, _⟩
    · unfold stepEnvelope at hn
      simp only [hb, hf] at hn
      repeat' split at hn
      all_goals simp_all
    · unfold stepHandle at hh
      rw [hb] at hh
      rw [handlePropose_halted hf] at hh
      cases hh

end Kill

theorem no_claim_tombstone (ht : s.ledger.tombstone = true) : (step p s e).2.claimed = false :=
  no_claim_halted (by rw [ht, Bool.or_true])

theorem no_claim_killed (hk : s.killed = true) : (step p s e).2.claimed = false :=
  no_claim_halted (by rw [hk, Bool.true_or])

namespace Kill

theorem killed_run (hk : s.killed = true) : (run p s es).1.killed = true := by
  induction es generalizing s with
  | nil => exact hk
  | cons e es ih => rw [run_cons_fst]; exact ih (killed_stays hk)

end Kill

theorem kill (es₁ es₂ : List Event) (k e : Event) (hk : k.body = .kill)
    (h : (step p (after p d es₁) k).2.accepted = true) :
    (step p (after p d (es₁ ++ k :: es₂)) e).2.claimed = false := by
  apply no_claim_killed
  rw [← List.singleton_append, ← List.append_assoc, after_append, after_snoc]
  exact killed_run (kill_accepted_sets hk h)

namespace Kill

def killPrefix : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" none [] []⟩ ]

def killEvent : Event := ⟨4, 4, 3, none, .kill⟩

def killDispatch : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩

#guard (step witnessPolicy (after witnessPolicy "pd" killPrefix) killEvent).2.accepted
#guard (trace witnessPolicy (State.initial "pd") (killPrefix ++ [killEvent, killDispatch])).map
    (·.2.2)
  == [.ok .none none, .ok .none none, .ok .allowed none, .ok .none none, .rejected .killed]
#guard !(step witnessPolicy (after witnessPolicy "pd" (killPrefix ++ [killEvent]))
    killDispatch).2.claimed
#guard (step witnessPolicy (after witnessPolicy "pd" killPrefix)
    ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" none [] "k1"⟩).2.claimed

def tombstoneSync : Event := ⟨4, 4, 3, none, .ledgerSync { version := 1, tombstone := true }⟩

#guard (step witnessPolicy (after witnessPolicy "pd" killPrefix) tombstoneSync).2.accepted
#guard (after witnessPolicy "pd" (killPrefix ++ [tombstoneSync])).ledger.tombstone
#guard !(after witnessPolicy "pd" (killPrefix ++ [tombstoneSync])).killed
#guard (step witnessPolicy (after witnessPolicy "pd" (killPrefix ++ [tombstoneSync]))
    killDispatch).2 == .rejected .killed

def killRepeat : Event := ⟨5, 5, 4, none, .propose "c1" "t" "d1" none [] []⟩

end Kill

#guard ((after witnessPolicy "pd" killPrefix).calls["c1"]?.map (·.status)) == some .authorized
#guard ((after witnessPolicy "pd" (killPrefix ++ [killEvent])).calls["c1"]?.map (·.status))
  == some .cancelled
#guard (step witnessPolicy (after witnessPolicy "pd" (killPrefix ++ [killEvent])) killRepeat).2
  == .ok (.denied .killed) none

end Writ.Proofs
