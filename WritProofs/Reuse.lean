import WritProofs.Support

namespace Writ.Proofs

open Writ Basic Grants

variable {p : Policy} {d : String} {s : State} {e : Event} {k gid : String} {c : CallRec}
  {g : GrantRec}

namespace Reuse

theorem dispatch_ends {t n : Nat} {dg key : String} {cost : Option Cost}
    {gs : List (String × Bool)} (ha : (handleDispatch p s t k n dg cost gs key).2.accepted = true)
    (hcl : (handleDispatch p s t k n dg cost gs key).2.claimed = false) :
    ∃ st, (handleDispatch p s t k n dg cost gs key).1 = s.endCall k st := by
  revert ha hcl
  unfold handleDispatch
  repeat' (first | (dsimp only) | split)
  all_goals intro ha hcl
  all_goals first | (simp [Verdict.accepted, Verdict.claimed] at ha hcl; done) | exact ⟨_, rfl⟩

theorem ends_grants (hc : s.calls[k]? = some c) (hst : c.status = .authorized)
    (ha : (stepHandle p s e).2.accepted = true) (hcl : (stepHandle p s e).2.claimed = false)
    (he : e.body = .cancel k ∨ (∃ rid w, e.body = .reject k rid w) ∨
      ∃ n dg cost gs key, e.body = .dispatch k n dg cost gs key) :
    ∃ st, (stepHandle p s e).1.grants = (s.endCall k st).grants := by
  rcases he with he | ⟨rid, w, he⟩ | ⟨n, dg, cost, gs, key, he⟩
  · refine ⟨.cancelled, ?_⟩
    simp only [stepHandle, he, handleCancel, Std.ExtTreeMap.get?_eq_getElem?, hc, hst]
  · have h : stepHandle p s e = handleReject p s k rid w := by simp only [stepHandle, he]
    rw [h] at ha ⊢
    revert ha
    unfold handleReject
    split
    · intro ha; simp [Verdict.accepted] at ha
    · intro _; exact ⟨.rejected, rfl⟩
  · rw [Dispatch.stepHandle_dispatch he] at ha hcl ⊢
    obtain ⟨st, h⟩ := dispatch_ends ha hcl
    exact ⟨st, by rw [h]⟩

theorem le_sum {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem cost_le (hk : k ∈ reservedCalls s gid) (hc : s.calls[k]? = some c) :
    (c.cost.map (·.amount)).getD 0 ≤ costOf s (reservedCalls s gid) := by
  unfold costOf
  refine Nat.le_trans (Nat.le_of_eq ?_) (le_sum (List.mem_map_of_mem hk))
  simp [hc]

end Reuse

open Reuse

/-- Section 8, theorem 2, a use returned by a call that ended without dispatch can be reused: an
accepted `cancel`, `reject` or unclaimed `dispatch` of call `k`, Authorized with a reserved use of
grant `gid`, from a reachable state, returns that use. The grant's reserved uses drop by one and
its reserved cost by the call's cost (when it has `max_cost`), every other field and every other
grant stay as they were, and the grant then has room for one more use, and for the call's cost. -/
theorem grant_use_returned (hr : Reachable p d s) (hc : s.calls[k]? = some c)
    (hst : c.status = .authorized) (hgc : c.grant = some gid) (hg : s.grants[gid]? = some g)
    (ha : (step p s e).2.accepted = true) (hcl : (step p s e).2.claimed = false)
    (he : e.body = .cancel k ∨ (∃ rid w, e.body = .reject k rid w) ∨
      ∃ n dg cost gs key, e.body = .dispatch k n dg cost gs key) :
    1 ≤ g.reserved ∧
      (step p s e).1.grants[gid]? = some { g with
        reserved := g.reserved - 1
        costReserved := g.costReserved -
          (if g.maxCost.isSome then (c.cost.map (·.amount)).getD 0 else 0) } ∧
      (∀ x, x ≠ gid → (step p s e).1.grants[x]? = s.grants[x]?) ∧
      g.consumed + (g.reserved - 1) < g.maxUses ∧
      ∀ mc, g.maxCost = some mc → (c.cost.map (·.amount)).getD 0 ≤ g.costReserved ∧
        g.costConsumed + (g.costReserved - (c.cost.map (·.amount)).getD 0) +
          (c.cost.map (·.amount)).getD 0 ≤ mc.amount := by
  have hi := Grants.inv_reachable hr
  have hgi := hi.grantInv
  have h0 : c.attempts = 0 := (hi.recs k c hc).1 (.inr hst)
  have hk : k ∈ reservedCalls s gid := mem_reservedCalls.mpr ⟨c, hc, hgc, hst, h0⟩
  have h1 : 1 ≤ g.reserved := by
    rw [hgi.reserved gid g hg]; exact List.length_pos_of_mem hk
  have hstep := accepted_step ha
  have ha' : (stepHandle p s e).2.accepted = true := by rw [hstep] at ha; exact ha
  have hcl' : (stepHandle p s e).2.claimed = false := by rw [hstep] at hcl; exact hcl
  obtain ⟨st, hgr⟩ := ends_grants hc hst ha' hcl' he
  have hgrants : (step p s e).1.grants = s.grants.insert gid
      { g with reserved := g.reserved - 1, costReserved := g.costReserved - g.costHeld c.cost } := by
    rw [hstep]
    show (stepHandle p s e).1.grants = _
    rw [hgr]
    show (s.releaseGrant k).grants = _
    rw [releaseGrant_of hc hgc h0 hg]
  refine ⟨h1, by rw [hgrants, Std.ExtTreeMap.getElem?_insert_self]; rfl,
    fun x hx => by rw [hgrants, insert_ne hx], by have := hgi.uses gid g hg; omega,
    fun mc hmc => ?_⟩
  have hle : (c.cost.map (·.amount)).getD 0 ≤ g.costReserved := by
    rw [hgi.costReserved gid g mc hg hmc]; exact cost_le hk hc
  have := hgi.cost gid g mc hg hmc
  exact ⟨hle, by omega⟩

/-- Section 8, theorem 2: an accepted `kill`, `reset` or `session_end`, or an accepted `ledger_sync`
that brings a tombstone the session did not have, from a reachable state ends every Awaiting and
Authorized call and returns every reserved use: each grant keeps its consumed counters and limits,
and has no reserved use or reserved cost left. -/
theorem grant_released_all (hr : Reachable p d s) (hg : s.grants[gid]? = some g)
    (ha : (step p s e).2.accepted = true)
    (he : e.body = .kill ∨ e.body = .reset ∨ e.body = .sessionEnd ∨
      ∃ l, e.body = .ledgerSync l ∧ l.tombstone = true ∧ s.ledger.tombstone = false) :
    ∃ g', (step p s e).1.grants[gid]? = some g' ∧ g'.reserved = 0 ∧ g'.consumed = g.consumed ∧
      g'.costConsumed = g.costConsumed ∧ g'.maxUses = g.maxUses ∧ g'.maxCost = g.maxCost ∧
      ∀ mc, g'.maxCost = some mc → g'.costReserved = 0 := by
  have hcl : (step p s e).2.claimed = false := by
    cases h : (step p s e).2.claimed
    · rfl
    · obtain ⟨_, _, _, _, _, _, hd⟩ := claimed_dispatch hr h
      rcases he with he | he | he | ⟨l, he, -⟩ <;> rw [he] at hd <;> cases hd
  have hst := Grants.step_stepped (p := p) (e := e) (Grants.inv_reachable hr)
  have hcalm := hst.2 hcl gid
  have hgi' := hst.1.grantInv
  have hstep := accepted_step ha
  have hclosed : ∀ (k : String) (c : CallRec), (step p s e).1.calls[k]? = some c →
      ¬AtMostOnce.Open c.status := by
    rw [hstep]
    show ∀ (k : String) (c : CallRec), (stepHandle p s e).1.calls[k]? = some c →
      ¬AtMostOnce.Open c.status
    have ha' : (stepHandle p s e).2.accepted = true := by rw [hstep] at ha; exact ha
    rcases he with he | he | he | ⟨l, he, hl, hs⟩ <;> simp only [stepHandle, he] at ha' ⊢
    · exact Lifecycle.cancelPending_closed
    · exact Lifecycle.interrupt_closed
    · exact Lifecycle.interrupt_closed
    · revert ha'
      unfold handleLedgerSync
      dsimp only
      split
      · intro ha'; simp [Verdict.accepted] at ha'
      · intro _
        simp only [hl, hs, Bool.not_false, Bool.and_self, ite_true]
        exact Lifecycle.cancelPending_closed
  have hnil : reservedCalls (step p s e).1 gid = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun k hk => by
      obtain ⟨c, hc, -, hau, -⟩ := mem_reservedCalls.mp hk
      exact hclosed k c hc (.inr hau)
  rw [hg] at hcalm
  cases hg' : (step p s e).1.grants[gid]? with
  | none => rw [hg'] at hcalm; exact hcalm.elim
  | some g' =>
    rw [hg'] at hcalm
    obtain ⟨h1, h2, h3, h4⟩ := hcalm
    refine ⟨g', rfl, by rw [hgi'.reserved gid g' hg', hnil]; rfl, h1, h2, h3, h4,
      fun mc hmc => by rw [hgi'.costReserved gid g' mc hg' hmc, hnil]; rfl⟩

namespace Reuse

def sOpen : State := after usePolicy "pd" useOpen

def ev (body : EventBody) : Event := ⟨5, 5, 4, none, body⟩

-- c1 is Authorized with the only use of g1.
#guard (sOpen.calls["c1"]?).any fun c => c.status == .authorized && c.grant == some "g1"
#guard (sOpen.grants["g1"]?).any fun g => g.reserved == 1 && g.consumed == 0 && g.maxUses == 1

-- `grant_use_returned`: a cancel and a veto of c1 each return the use and change nothing else of
-- g1; c2 is then covered by g1 instead of needing an approval.
#guard (step usePolicy sOpen (ev (.cancel "c1"))).2 == .ok .none none
#guard (step usePolicy sOpen (ev (.cancel "c1"))).1.grants["g1"]? ==
  (sOpen.grants["g1"]?).map fun g => { g with reserved := 0 }
#guard (step usePolicy sOpen (ev (.reject "c1" ⟨"s1", "c1", 0⟩ "a1"))).2 == .ok .none none
#guard (step usePolicy sOpen (ev (.reject "c1" ⟨"s1", "c1", 0⟩ "a1"))).1.grants["g1"]? ==
  (sOpen.grants["g1"]?).map fun g => { g with reserved := 0 }
#guard (step usePolicy sOpen (proposeC2 5)).2 == .ok (.needsApproval ⟨"s1", "c2", 0⟩) none
#guard (step usePolicy (after usePolicy "pd" useCancel) (proposeC2 6)).2
  == .ok (.allowedByGrant "g1") none

-- `grant_released_all`: a kill, and a sync that brings a tombstone, return the use too.
#guard (step usePolicy sOpen (ev .kill)).2 == .ok .none none
#guard ((step usePolicy sOpen (ev .kill)).1.grants["g1"]?).any fun g =>
  g.reserved == 0 && g.consumed == 0 && g.maxUses == 1
#guard (step usePolicy sOpen (ev (.ledgerSync { sOpen.ledger with tombstone := true }))).2
  == .ok .none none
#guard ((step usePolicy sOpen
    (ev (.ledgerSync { sOpen.ledger with tombstone := true }))).1.grants["g1"]?).any fun g =>
  g.reserved == 0 && g.consumed == 0 && g.maxUses == 1

end Reuse

end Writ.Proofs
