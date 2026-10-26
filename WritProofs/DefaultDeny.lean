import WritProofs.Calls
import WritProofs.Dispatch

namespace Writ.Proofs

open Writ
open Basic Calls

variable {p : Policy} {d : String} {s : State} {e : Event} {k tool dg : String} {c : CallRec}
  {cost : Option Cost} {gs es : List (String × Bool)}

structure DenyInv (p : Policy) (s : State) : Prop where
  defined : ∀ (k : String) (c : CallRec), s.calls[k]? = some c →
    ∃ r, p.action? c.tool = some r ∧ (r.exposed = false → ∃ x, c.status = .denied x)

theorem DenyInv.initial : DenyInv p (State.initial d) :=
  ⟨fun _ _ hk => by simp [State.initial] at hk⟩

theorem DenyInv.step (h : DenyInv p s) : DenyInv p (step p s e).1 := by
  refine ⟨fun k c' hc' => ?_⟩
  have hs := CallsStep.step (p := p) (s := s) (e := e) k
  rw [hc'] at hs
  cases hk : s.calls[k]? with
  | none => rw [hk] at hs; exact hs
  | some c => rw [hk] at hs; exact Fresh.keyStep (h.defined k c hk) hs

theorem denyInv_reachable : Reachable p d s → DenyInv p s := by
  intro hr
  induction hr with
  | init => exact DenyInv.initial
  | step _ ih => exact ih.step

theorem default_deny_claim (hr : Reachable p d s) (h : (step p s e).2.claimed = true) :
    ∃ k n dg cost g key c r, e.body = .dispatch k n dg cost g key ∧ s.calls[k]? = some c ∧
      p.action? c.tool = some r ∧ r.exposed = true := by
  obtain ⟨k, n, dg, cost, g, key, hb⟩ := claimed_dispatch hr h
  obtain ⟨-, rc, hrc, ⟨hst, -⟩, -⟩ := (dispatch_claimed_iff hb).mp h
  obtain ⟨r, hra, hx⟩ := (denyInv_reachable hr).defined k rc hrc
  refine ⟨k, n, dg, cost, g, key, rc, r, hb, hrc, hra, ?_⟩
  cases he : r.exposed
  · obtain ⟨x, hs⟩ := hx he
    rw [hs] at hst
    rcases hst with hst | hst <;> cases hst
  · rfl

namespace DefaultDeny

theorem repeatDecision_denied (hs : c.status = .denied x) (hm : p.modeOf c.tool = .enforce) :
    ∃ y, (repeatDecision p s t k c).1 = .denied y := by
  unfold repeatDecision
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · split <;> simp_all

theorem handlePropose_denied (hi : DenyInv p s)
    (hu : p.action? tool = none ∨ ∃ r, p.action? tool = some r ∧ r.exposed = false)
    (h : (handlePropose p s t k tool dg cost gs es).2 = .ok dc sh) : ∃ x, dc = .denied x := by
  unfold handlePropose at h
  split at h
  · rename_i rc hrc
    split at h
    · rename_i hc
      obtain ⟨r, hra, hx⟩ := hi.defined k rc hrc
      have hxf : r.exposed = false := by
        rcases hu with hu | ⟨r', hr', hx'⟩
        · rw [← hc.1, hra] at hu; cases hu
        · rw [← hc.1, hra] at hr'; cases hr'; exact hx'
      obtain ⟨x, hs⟩ := hx hxf
      obtain ⟨y, hy⟩ :=
        repeatDecision_denied (s := s) (t := t) (k := k) hs (modeOf_unexposed hra hxf)
      dsimp only at h
      cases h
      exact ⟨y, hy⟩
    · cases h
  · obtain ⟨x, hx⟩ := enforceDecision_denied (s := s) (t := t) (k := k) (dg := dg) (cs := cost)
      (gs := gs) (es := es) hu
    split at h
    rename_i _ _ hd
    rw [hd] at hx
    dsimp only at hx
    subst hx
    split at h
    · cases h; exact ⟨x, rfl⟩
    · rename_i r hra
      have hxf : r.exposed = false := by
        rcases hu with hu | ⟨r', hr', hx'⟩
        · rw [hra] at hu; cases hu
        · rw [hra] at hr'; cases hr'; exact hx'
      dsimp only at h
      rw [modeOf_unexposed hra hxf, shadowed_enforce] at h
      cases h
      exact ⟨x, rfl⟩

end DefaultDeny

open DefaultDeny

theorem default_deny_propose (hr : Reachable p d s) (he : e.body = .propose k tool dg cost gs es)
    (hu : p.action? tool = none ∨ ∃ r, p.action? tool = some r ∧ r.exposed = false) :
    ∀ dc sh, (step p s e).2 = .ok dc sh → ∃ x, dc = .denied x := by
  intro dc sh hv
  have ha : (step p s e).2.accepted = true := by rw [hv]; rfl
  rw [accepted_step ha] at hv
  dsimp only at hv
  unfold Writ.stepHandle at hv
  simp only [he] at hv
  exact handlePropose_denied (denyInv_reachable hr) hu hv

theorem default_deny_status (hr : Reachable p d s) (hc : s.calls[k]? = some c)
    (hu : ∃ r, p.action? c.tool = some r ∧ r.exposed = false) :
    ∃ x, c.status = .denied x := by
  obtain ⟨r, hra, hx⟩ := hu
  obtain ⟨r', hra', hx'⟩ := (denyInv_reachable hr).defined k c hc
  rw [hra] at hra'
  cases hra'
  exact hx' hx

namespace DefaultDeny

def hiddenPolicy : Policy :=
  { mode := .logOnly, actions := [("hidden", { exposed := false }), ("shown", {})] }

def hiddenEvents : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "hidden" "d1" none [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "nope" "d2" none [] []⟩
  , ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" none [] "k1"⟩
  , ⟨6, 6, 4, none, .propose "c3" "shown" "d3" none [] []⟩
  , ⟨7, 7, 5, none, .dispatch "c3" 1 "d3" none [] "k3"⟩ ]

end DefaultDeny

#guard (hiddenPolicy.action? "hidden").map (·.exposed) == some false
#guard (hiddenPolicy.action? "nope").isNone
#guard (hiddenPolicy.action? "shown").map (·.exposed) == some true
#guard (trace hiddenPolicy (State.initial "pd") hiddenEvents).map (·.2.2)
  == [ .ok .none none, .ok .none none, .ok (.denied .notExposed) none,
       .ok (.denied .unknownTool) none, .rejected .callEnded, .ok .allowed none,
       .ok .dispatchClaimed none ]
#guard (trace hiddenPolicy (State.initial "pd") hiddenEvents).map (·.2.2.claimed)
  == [false, false, false, false, false, false, true]
#guard ((after hiddenPolicy "pd" (hiddenEvents.take 4)).calls["c1"]?).map (·.status)
  == some (.denied .notExposed)
#guard ((after hiddenPolicy "pd" hiddenEvents).calls["c1"]?).map (·.status)
  == some (.denied .notExposed)

end Writ.Proofs
