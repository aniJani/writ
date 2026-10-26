import WritProofs.Dispatch
import WritProofs.WF

namespace Writ.Proofs

open Writ Usage Basic

variable {p : Policy} {s : State} {e : Event} {k m m' dg key sid : String} {n t now a : Nat}
  {cost : Option Cost} {g : List (String × Bool)} {c : CallRec} {r : Requirements}
  {spec : MeterSpec} {cap mx : Nat} {es : List MeterEntry} {sc : MeterScope}
  {f : List MeterEntry → List MeterEntry}

namespace Meters

theorem expired_zero {x : MeterEntry} (h : spec.expired x now = true) :
    (if spec.windowMs.all (x.time + · > now) then x.amount else 0) +
      (if spec.windowMs.all (x.excessAt + · > now) then x.excess else 0) = 0 := by
  simp only [MeterSpec.expired, MeterSpec.inWindow, inWindowAt_eq, Bool.and_eq_true,
    Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, -⟩, ht⟩, hx⟩ := h
  rw [ht]
  rcases hx with hx | hx <;> simp [hx]

theorem usageAt_prune (hs : p.meter? m = some spec) :
    usageAt spec (p.prune sc t es) m t = usageAt spec es m t := by
  induction es with
  | nil => rfl
  | cons x es ih =>
    unfold Policy.prune at ih ⊢
    rw [List.filter_cons]
    split
    · rw [usageAt_cons, usageAt_cons, ih]
    · rename_i hk
      rw [usageAt_cons, ih]
      by_cases hx : x.meter = m
      · rw [hx, hs] at hk
        simp only [Option.any_some, Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hk
        simp [hx, expired_zero hk.2]
      · simp [hx]

def upd (p : Policy) (sc : MeterScope) (t : Nat) (f : List MeterEntry → List MeterEntry)
    (es : List MeterEntry) : List MeterEntry :=
  if f es == es then es else p.prune sc t (f es)

theorem usageAt_upd (hs : p.meter? m = some spec) :
    usageAt spec (upd p sc t f es) m t = usageAt spec (f es) m t := by
  unfold upd
  split
  · rename_i h; rw [eq_of_beq h]
  · exact usageAt_prune hs

theorem upd_sublist : (upd p sc t f es).Sublist (f es) := by
  unfold upd
  split
  · rename_i h; rw [eq_of_beq h]; exact List.Sublist.refl _
  · exact List.filter_sublist

theorem entriesOf_update :
    entriesOf p (s.updateEntries p m' t f) m = entriesOf p s m ∨
      ∃ sc, entriesOf p (s.updateEntries p m' t f) m = upd p sc t f (entriesOf p s m) := by
  unfold State.updateEntries entriesOf
  split <;> split <;> first | (left; rfl) | (right; exact ⟨_, rfl⟩)

theorem entriesOf_update_self :
    ∃ sc, entriesOf p (s.updateEntries p m t f) m = upd p sc t f (entriesOf p s m) := by
  unfold State.updateEntries entriesOf
  split <;> split <;> first | exact ⟨_, rfl⟩ | skip
  all_goals (exfalso; cases hm : p.meter? m <;> simp_all)

theorem updateEntries_sessionId : (s.updateEntries p m' t f).sessionId = s.sessionId := by
  unfold State.updateEntries
  split <;> rfl

theorem claimed_fits (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce) (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters)
    (hst : c.status = .unknown → Stale p s e.time m k) : MeterFits p s e.time m c.cost := by
  obtain ⟨-, c', hc', -, hok⟩ := (dispatch_claimed_iff he).mp h
  rw [hc] at hc'
  cases hc'
  obtain ⟨-, -, -, -, hmet⟩ := hok hm
  simp only [hr, Option.getD_some] at hmet
  exact hmet m hmr hst

theorem claimed_entries (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c) :
    entriesOf p (step p s e).1 m =
      entriesOf p (claim p s e.time k c ((p.action? c.tool).getD {}) (c.status == .unknown) key)
        m := by
  rw [claim_post h he hc]
  rfl

theorem entriesOf_consumeGrant : entriesOf p (s.consumeGrant k) m = entriesOf p s m := by
  unfold State.consumeGrant
  split
  · split <;> rfl
  · rfl

theorem inside_now (hw : spec.windowMs ≠ some 0) : spec.windowMs.all (t + · > t) = true := by
  cases h : spec.windowMs with
  | none => rfl
  | some w =>
    have : w ≠ 0 := fun h0 => hw (h ▸ h0 ▸ rfl)
    simp only [Option.all_some, decide_eq_true_eq]
    omega

theorem reserve_other (hs : p.meter? m = some spec) (hne : m' ≠ m) :
    usageAt spec (entriesOf p (s.reserve p m' k a t) m) m t =
      usageAt spec (entriesOf p s m) m t := by
  unfold State.reserve
  rcases entriesOf_update with h | ⟨sc, h⟩ <;> rw [h]
  rw [usageAt_upd hs, usageAt_append, usageAt_cons, usageAt_nil]
  simp [hne]

theorem reserve_self (hs : p.meter? m = some spec) (hw : spec.windowMs ≠ some 0) :
    usageAt spec (entriesOf p (s.reserve p m k a t) m) m t =
      usageAt spec (entriesOf p s m) m t + a := by
  unfold State.reserve
  obtain ⟨sc, h⟩ := entriesOf_update_self (p := p) (s := s) (m := m) (t := t)
    (f := fun es => es ++ [⟨m, s.sessionId, k, t, a, false, 0, 0⟩])
  have hi : spec.windowMs.all (fun w => decide (0 < w)) = true := by
    simpa using inside_now (t := t) hw
  rw [h, usageAt_upd hs, usageAt_append, usageAt_cons, usageAt_nil]
  simp [hi]

theorem reserve_mem {x : MeterEntry} (hx : x ∈ entriesOf p (s.reserve p m' k a t) m) :
    x ∈ entriesOf p s m ∨ (x.meter = m' ∧ x.amount = a) := by
  unfold State.reserve at hx
  rcases entriesOf_update with h | ⟨sc, h⟩ <;> rw [h] at hx
  · exact .inl hx
  · have := upd_sublist.subset hx
    simp only [List.mem_append, List.mem_singleton] at this
    rcases this with hx | rfl
    · exact .inl hx
    · exact .inr ⟨rfl, rfl⟩

theorem isFor_iff {x : MeterEntry} :
    x.isFor m sid k = true ↔ x.meter = m ∧ x.session = sid ∧ x.call = k := by
  simp [MeterEntry.isFor, and_assoc]

theorem usage_retime_other (hne : m' ≠ m) :
    usageAt spec (es.map fun x => if x.isFor m' sid k then { x with time := t } else x) m now =
      usageAt spec es m now := by
  induction es with
  | nil => rfl
  | cons x es ih =>
    rw [List.map_cons, usageAt_cons, usageAt_cons, ih]
    split
    · rename_i hx
      have hxm := ((isFor_iff.mp hx).1)
      have : x.meter ≠ m := hxm ▸ hne
      simp [this]
    · rfl

theorem own_retime_other (hne : m' ≠ m) {sid' : String} :
    (es.map fun x => if x.isFor m' sid k then { x with time := t } else x).filter
      (·.isFor m sid' k) = es.filter (·.isFor m sid' k) := by
  induction es with
  | nil => rfl
  | cons x es ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons, ih]
    split
    · rename_i hx
      have hxm := ((isFor_iff.mp hx).1)
      have h1 : x.isFor m sid' k = false := by
        cases hy : x.isFor m sid' k
        · rfl
        · exact absurd (hxm.symm.trans (isFor_iff.mp hy).1) hne
      have h2 : ({ x with time := t } : MeterEntry).isFor m sid' k = false := by
        simpa [MeterEntry.isFor] using h1
      simp [h1, h2]
    · rfl

theorem usage_retime_self (hw : spec.windowMs ≠ some 0)
    (hout : ∀ x ∈ es, x.isFor m sid k = true → spec.windowMs.all (x.time + · > t) = false) :
    usageAt spec (es.map fun x => if x.isFor m sid k then { x with time := t } else x) m t =
      usageAt spec es m t + ((es.filter (·.isFor m sid k)).map (·.amount)).sum := by
  induction es with
  | nil => rfl
  | cons x es ih =>
    rw [List.map_cons, usageAt_cons, usageAt_cons,
      ih fun y hy => hout y (List.mem_cons_of_mem _ hy), List.filter_cons]
    split
    · rename_i hx
      have hxm := (isFor_iff.mp hx).1
      have ho := hout x List.mem_cons_self hx
      have hi : spec.windowMs.all (t + · > t) = true := inside_now hw
      dsimp only
      rw [ite_eq_left hxm, ite_eq_left hxm, hi, ho]
      simp only [ite_true, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
      omega
    · omega

theorem retime_other (hs : p.meter? m = some spec) (hne : m' ≠ m) :
    usageAt spec (entriesOf p (s.retime p m' k t) m) m t =
      usageAt spec (entriesOf p s m) m t := by
  unfold State.retime
  rcases entriesOf_update with h | ⟨sc, h⟩ <;> rw [h]
  rw [usageAt_upd hs, usage_retime_other hne]

theorem retime_own (hne : m' ≠ m) :
    ((entriesOf p (s.retime p m' k t) m).filter (·.isFor m sid k)).Sublist
      ((entriesOf p s m).filter (·.isFor m sid k)) := by
  unfold State.retime
  rcases entriesOf_update with h | ⟨sc, h⟩ <;> rw [h]
  · exact List.Sublist.refl _
  · refine (upd_sublist.filter _).trans ?_
    rw [own_retime_other hne]
    exact List.Sublist.refl _

theorem retime_self (hs : p.meter? m = some spec) (hw : spec.windowMs ≠ some 0)
    (hout : ∀ x ∈ entriesOf p s m, x.isFor m s.sessionId k = true →
      spec.windowMs.all (x.time + · > t) = false) :
    usageAt spec (entriesOf p (s.retime p m k t) m) m t =
      usageAt spec (entriesOf p s m) m t +
        (((entriesOf p s m).filter (·.isFor m s.sessionId k)).map (·.amount)).sum := by
  unfold State.retime
  obtain ⟨sc, h⟩ := entriesOf_update_self (p := p) (s := s) (m := m) (t := t)
    (f := List.map fun x => if x.isFor m s.sessionId k then { x with time := t } else x)
  rw [h, usageAt_upd hs, usage_retime_self hw hout]

theorem foldl_keep {α : Type _} (P : State → Prop) {f : State → α → State} {x : α}
    (hf : ∀ s y, y ≠ x → P s → P (f s y)) : ∀ (ms : List α) (s : State), x ∉ ms → P s →
      P (ms.foldl f s)
  | [], _, _, hp => hp
  | y :: ms, s, hx, hp =>
    foldl_keep P hf ms (f s y) (fun h => hx (List.mem_cons_of_mem _ h))
      (hf s y (fun h => hx (h ▸ List.mem_cons_self)) hp)

theorem reserve_fold_other (hs : p.meter? m = some spec) :
    ∀ (ms : List String) (s₀ : State), m ∉ ms →
      usageAt spec (entriesOf p (ms.foldl (fun s m' => s.reserve p m' k (p.callAmount m' cost) t)
        s₀) m) m t = usageAt spec (entriesOf p s₀ m) m t :=
  fun ms s₀ hm => foldl_keep (fun s' => usageAt spec (entriesOf p s' m) m t =
    usageAt spec (entriesOf p s₀ m) m t) (fun _ _ hy hp => (reserve_other hs hy).trans hp)
    ms s₀ hm rfl

theorem retime_fold_other (hs : p.meter? m = some spec) :
    ∀ (ms : List String) (s₀ : State), m ∉ ms →
      usageAt spec (entriesOf p (ms.foldl (fun s m' => s.retime p m' k t) s₀) m) m t =
        usageAt spec (entriesOf p s₀ m) m t :=
  fun ms s₀ hm => foldl_keep (fun s' => usageAt spec (entriesOf p s' m) m t =
    usageAt spec (entriesOf p s₀ m) m t) (fun _ _ hy hp => (retime_other hs hy).trans hp)
    ms s₀ hm rfl

theorem split_nodup {α : Type _} {ms : List α} {x : α} (hn : ms.Nodup) (hx : x ∈ ms) :
    ∃ pre post, ms = pre ++ x :: post ∧ x ∉ pre ∧ x ∉ post := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hx
  rw [List.nodup_append, List.nodup_cons] at hn
  exact ⟨pre, post, rfl, fun h => hn.2.2 x h x List.mem_cons_self rfl, hn.2.1.1⟩

theorem sum_le {l : List MeterEntry} {d : Nat} (hl : l.length ≤ 1) (hb : ∀ x ∈ l, x.amount ≤ d) :
    (l.map (·.amount)).sum ≤ d := by
  match l, hl with
  | [], _ => exact Nat.zero_le _
  | [x], _ => simpa using hb x List.mem_cons_self

theorem entriesOf_claim_first :
    entriesOf p (claim p s t k c r false key) m =
      entriesOf p (r.meters.foldl (fun s m' => s.reserve p m' k (p.callAmount m' c.cost) t)
        (s.consumeGrant k)) m := rfl

theorem entriesOf_claim_retry :
    entriesOf p (claim p s t k c r true key) m =
      entriesOf p ((s.staleMeters p t r.meters k).foldl (fun s m' => s.retime p m' k t) s) m := rfl

theorem isFor_decide {x : MeterEntry} :
    x.isFor m sid k = decide (x.meter = m ∧ x.session = sid ∧ x.call = k) := by
  cases h : x.isFor m sid k <;> simp_all [MeterEntry.isFor]

theorem shape_per_call (hwf : p.WF) (hs : p.meter? m = some spec) (hx : spec.maxPerCall = some mx)
    (h : ∀ cur, spec.unit = .money cur → ∃ cc, cost = some cc ∧ cc.currency = cur ∧
      ∀ mx, spec.maxPerCall = some mx → cc.amount ≤ mx) : draw spec cost ≤ mx := by
  obtain ⟨cur, hu⟩ := WF.perCall_money hwf hs (by simp [hx])
  obtain ⟨cc, rfl, -, hle⟩ := h cur hu
  simp only [draw, hu, Option.map_some, Option.getD_some]
  exact hle mx hx

theorem find_own :
    (entriesOf p s m).find? (fun en => en.meter == m && en.session == s.sessionId && en.call == k)
      = (ownEntries p s m k).head? := by
  rw [← List.head?_filter]
  unfold ownEntries
  congr 1
  exact List.filter_congr fun en _ => isFor_decide

theorem stale_of_out (hs : p.meter? m = some spec)
    (hout : ∀ en ∈ ownEntries p s m k, spec.windowMs.all (en.time + · > t) = false) :
    Stale p s t m k := fun en hf spec' hs' => by
  rw [hs] at hs'
  cases hs'
  rw [find_own] at hf
  exact hout en (List.mem_of_mem_head? hf)

/-- The verdict decides `overrun`. -/
def overran : Verdict → Bool
  | .ok (.overrun _) _ => true
  | _ => false

local macro "unoverrun" : tactic =>
  `(tactic| repeat' (first | rfl | (dsimp only) | split | simp only [overran]))

theorem disposition_unoverrun (x : Disposition) (sh : Option Shadow) :
    overran (.ok x.decision sh) = false := by
  cases x <;> rfl

theorem applyApprove_unoverrun (h : applyApprove p s q1 q2 q3 q4 q5 q6 q7 q8 = .ok q9) :
    overran q9.2 = false := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

theorem repeatDecision_unoverrun (hn : NoClaimed s) (hc : s.calls[k]? = some rc) :
    overran (.ok (repeatDecision p s t k rc).1 sh) = false := by
  unfold repeatDecision
  have hd := (hn k rc hc).2
  repeat' (first | rfl | (dsimp only) | split)
  all_goals (cases hr : rc.decision <;> first | rfl | exact absurd hr (hd _))

theorem recordFailure_counts {tool : String} :
    (s.recordFailure p tool).failuresThisSession = s.failuresThisSession + 1 ∧
      (s.recordFailure p tool).failures[tool]? = some (s.failures.getD tool 0 + 1) := by
  unfold State.recordFailure
  dsimp only
  repeat' split
  all_goals simp

theorem updateEntries_counts {f : List MeterEntry → List MeterEntry} :
    (s.updateEntries p m t f).failuresThisSession = s.failuresThisSession ∧
      (s.updateEntries p m t f).failures = s.failures := by
  unfold State.updateEntries; split <;> exact ⟨rfl, rfl⟩

theorem settle_counts :
    (s.settle p ms k o act ne t).1.failuresThisSession = s.failuresThisSession ∧
      (s.settle p ms k o act ne t).1.failures = s.failures := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => b.1.failuresThisSession =
    s.failuresThisSession ∧ b.1.failures = s.failures) ?_ ms _ ⟨rfl, rfl⟩
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact ⟨updateEntries_counts.1.trans h.1, updateEntries_counts.2.trans h.2⟩
  · split <;> exact ⟨updateEntries_counts.1.trans h.1, updateEntries_counts.2.trans h.2⟩

theorem ofOverrun_ne {over ms : List String} (h : Decision.ofOverrun over = .overrun ms) :
    over.isEmpty = false := by
  unfold Decision.ofOverrun at h
  split at h
  · cases h
  · rename_i hne; simpa using hne

theorem handleResult_overrun (h : (handleResult p s t k o act ne).2 = .ok (.overrun ms) sh) :
    ∃ c, s.calls[k]? = some c ∧
      (handleResult p s t k o act ne).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (handleResult p s t k o act ne).1.failures[c.tool]? =
        some (s.failures.getD c.tool 0 + 1) := by
  unfold handleResult at h ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?] at h ⊢
  cases hc : s.calls[k]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    refine ⟨c, rfl, ?_⟩
    dsimp only at h ⊢
    split at h
    · cases h
    · rename_i hd
      simp only [hd, ↓reduceIte] at h ⊢
      have hcs := settle_counts (s := withStatus s k c o.status) (p := p) (ms := callMeters p c)
        (k := k) (o := o) (act := act) (ne := ne) (t := t)
      generalize State.settle p (withStatus s k c o.status) (callMeters p c) k o act ne t = r
        at h hcs ⊢
      obtain ⟨s', over⟩ := r
      dsimp only at h hcs ⊢
      rw [ofOverrun_ne (Verdict.ok.inj h).1]
      have hf := recordFailure_counts (s := s') (p := p) (tool := c.tool)
      rw [hcs.1, hcs.2] at hf
      cases o <;> exact hf

theorem handleReconcile_overrun
    (h : (handleReconcile p s t k o act ne).2 = .ok (.overrun ms) sh) :
    ∃ c, s.calls[k]? = some c ∧
      (handleReconcile p s t k o act ne).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (handleReconcile p s t k o act ne).1.failures[c.tool]? =
        some (s.failures.getD c.tool 0 + 1) := by
  unfold handleReconcile at h ⊢
  rw [Std.ExtTreeMap.get?_eq_getElem?] at h ⊢
  cases hc : s.calls[k]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    refine ⟨c, rfl, ?_⟩
    dsimp only at h ⊢
    split at h
    · cases h
    · rename_i hu
      split at h
      · cases h
      · rename_i hn
        simp only [hu, hn, ↓reduceIte] at h ⊢
        have hcs := settle_counts (p := p) (ms := callMeters p c) (k := k) (o := o)
          (act := act) (ne := ne) (t := t)
          (s := { s with calls := s.calls.insert k { c with reconciled := some o } })
        generalize State.settle p _ (callMeters p c) k o act ne t = r at h hcs ⊢
        obtain ⟨s', over⟩ := r
        dsimp only at h hcs ⊢
        rw [ofOverrun_ne (Verdict.ok.inj h).1]
        have hf := recordFailure_counts (s := s') (p := p) (tool := c.tool)
        rw [hcs.1, hcs.2] at hf
        exact hf

theorem handleSessionStart_unoverrun :
    overran (handleSessionStart s q1 q2 q3 q4 q5 q6).2 = false := by
  unfold handleSessionStart; unoverrun

theorem handleSessionEnd_unoverrun : overran (handleSessionEnd s).2 = false := by
  unfold handleSessionEnd; unoverrun

theorem handleTurnStart_unoverrun : overran (handleTurnStart s q1).2 = false := by
  unfold handleTurnStart; unoverrun

theorem handleTurnEnd_unoverrun : overran (handleTurnEnd s).2 = false := by
  unfold handleTurnEnd; unoverrun

theorem handleStepStart_unoverrun : overran (handleStepStart p s).2 = false := by
  unfold handleStepStart; unoverrun

theorem handleApproverAttest_unoverrun : overran (handleApproverAttest s q1 q2).2 = false := by
  unfold handleApproverAttest; unoverrun

theorem handlePermissionRevoke_unoverrun : overran (handlePermissionRevoke s q1).2 = false := by
  unfold handlePermissionRevoke; unoverrun

theorem handleReject_unoverrun : overran (handleReject p s q1 q2 q3).2 = false := by
  unfold handleReject; unoverrun

theorem handleApprovalExpire_unoverrun : overran (handleApprovalExpire s q1 q2).2 = false := by
  unfold handleApprovalExpire; unoverrun

theorem handleGrantCreate_unoverrun :
    overran (handleGrantCreate p s q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11).2 = false := by
  unfold handleGrantCreate; unoverrun

theorem handleGrantRevoke_unoverrun : overran (handleGrantRevoke s q1).2 = false := by
  unfold handleGrantRevoke; unoverrun

theorem handleDispatch_unoverrun : overran (handleDispatch p s q1 q2 q3 q4 q5 q6 q7).2 = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  obtain ⟨c, -, -, -, hc⟩ := (Dispatch.handle_iff fun _ => rfl).mp h
  revert hc
  split <;> simp only [overran, and_false, Bool.false_eq_true, imp_self]

theorem handleOutcomeUnknown_unoverrun : overran (handleOutcomeUnknown p s q1).2 = false := by
  unfold handleOutcomeUnknown; unoverrun

theorem handleCancel_unoverrun : overran (handleCancel s q1).2 = false := by
  unfold handleCancel; unoverrun

theorem handleReset_unoverrun : overran (handleReset s).2 = false := by
  unfold handleReset; unoverrun

theorem handleKill_unoverrun : overran (handleKill p s).2 = false := by
  unfold handleKill; unoverrun

theorem handlePermissionAdd_unoverrun : overran (handlePermissionAdd p s q1 q2).2 = false := by
  unfold handlePermissionAdd; unoverrun

theorem handleEscalationAck_unoverrun : overran (handleEscalationAck p s q1 q2).2 = false := by
  unfold handleEscalationAck; unoverrun

theorem handleLedgerSync_unoverrun : overran (handleLedgerSync s q1).2 = false := by
  unfold handleLedgerSync; unoverrun

theorem handleApprove_unoverrun : overran (handleApprove p s q1 q2 q3 q4 q5 q6 q7).2 = false := by
  unfold handleApprove
  repeat' (first | rfl | (dsimp only) | split)
  exact applyApprove_unoverrun (by assumption)

theorem handlePropose_unoverrun (hn : NoClaimed s) :
    overran (handlePropose p s t k q1 q2 q3 q4 q5).2 = false := by
  unfold handlePropose
  split
  · rename_i rc hrc
    split
    · have := repeatDecision_unoverrun (p := p) (t := t) (sh := (repeatDecision p s t k rc).2) hn
        (by rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hrc)
      revert this
      generalize repeatDecision p s t k rc = r
      obtain ⟨d, sh⟩ := r
      exact id
    · rfl
  · repeat' (first | (dsimp only) | split)
    all_goals exact disposition_unoverrun _ _

theorem stepHandle_overrun (hn : NoClaimed s)
    (h : (stepHandle p s e).2 = .ok (.overrun ms) sh) :
    ∃ (k : String) (c : CallRec), s.calls[k]? = some c ∧
      (stepHandle p s e).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (stepHandle p s e).1.failures[c.tool]? = some (s.failures.getD c.tool 0 + 1) ∧
      ((∃ o act ne, e.body = .result k o act ne) ∨ ∃ o act ne, e.body = .reconcile k o act ne) := by
  have ho := congrArg overran h
  revert h ho
  unfold stepHandle
  split <;> rename_i hb <;> intro h ho
  all_goals first
    | (obtain ⟨c, hc, h1, h2⟩ := handleResult_overrun h
       exact ⟨_, c, hc, h1, h2, .inl ⟨_, _, _, hb⟩⟩)
    | (obtain ⟨c, hc, h1, h2⟩ := handleReconcile_overrun h
       exact ⟨_, c, hc, h1, h2, .inr ⟨_, _, _, hb⟩⟩)
    | (rw [handlePropose_unoverrun hn] at ho; cases ho)
    | (rw [handleApprove_unoverrun] at ho; cases ho)
    | (rw [handleSessionStart_unoverrun] at ho; cases ho)
    | (rw [handleSessionEnd_unoverrun] at ho; cases ho)
    | (rw [handleTurnStart_unoverrun] at ho; cases ho)
    | (rw [handleTurnEnd_unoverrun] at ho; cases ho)
    | (rw [handleStepStart_unoverrun] at ho; cases ho)
    | (rw [handleApproverAttest_unoverrun] at ho; cases ho)
    | (rw [handlePermissionRevoke_unoverrun] at ho; cases ho)
    | (rw [handleReject_unoverrun] at ho; cases ho)
    | (rw [handleApprovalExpire_unoverrun] at ho; cases ho)
    | (rw [handleGrantCreate_unoverrun] at ho; cases ho)
    | (rw [handleGrantRevoke_unoverrun] at ho; cases ho)
    | (rw [handleDispatch_unoverrun] at ho; cases ho)
    | (rw [handleOutcomeUnknown_unoverrun] at ho; cases ho)
    | (rw [handleCancel_unoverrun] at ho; cases ho)
    | (rw [handleReset_unoverrun] at ho; cases ho)
    | (rw [handleKill_unoverrun] at ho; cases ho)
    | (rw [handlePermissionAdd_unoverrun] at ho; cases ho)
    | (rw [handleEscalationAck_unoverrun] at ho; cases ho)
    | (rw [handleLedgerSync_unoverrun] at ho; cases ho)

end Meters

open Meters

theorem meter_cap (hwf : p.WF) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .authorized) (hm : p.modeOf c.tool = .enforce)
    (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap) :
    usageAt spec (entriesOf p (step p s e).1 m) m e.time ≤ cap := by
  obtain ⟨spec', hs', -, hroom⟩ := claimed_fits h he hc hm hr hmr fun hu => by
    rw [hst] at hu; cases hu
  rw [hs] at hs'
  cases hs'
  have hR : (p.action? c.tool).getD {} = r := by rw [hr]; rfl
  have hret : (c.status == .unknown) = false := by rw [hst]; rfl
  rw [claimed_entries h he hc, hR, hret, entriesOf_claim_first]
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup (WF.meters_nodup hwf hr) hmr
  rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [reserve_fold_other hs post _ hpost, reserve_self hs (WF.window_pos hwf hs),
    reserve_fold_other hs pre _ hpre, entriesOf_consumeGrant, callAmount_eq hs]
  exact hroom cap hcap

/-- The step-local form of `meter_cap_retry`: it takes `hone` and `hamt` as hypotheses, and
`meter_cap_retry` discharges them from the accounting invariant. -/
theorem meter_cap_retry_of (hwf : p.WF) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .unknown) (hm : p.modeOf c.tool = .enforce)
    (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap)
    (hout : ∀ en ∈ entriesOf p s m, en.meter = m → en.session = s.sessionId → en.call = k →
      spec.windowMs.all (en.time + · > e.time) = false)
    (hone : ((entriesOf p s m).filter fun en =>
      en.meter = m ∧ en.session = s.sessionId ∧ en.call = k).length ≤ 1)
    (hamt : ∀ en ∈ entriesOf p s m, en.meter = m → en.session = s.sessionId → en.call = k →
      en.amount ≤ draw spec c.cost) :
    usageAt spec (entriesOf p (step p s e).1 m) m e.time ≤ cap := by
  have hout' : ∀ x ∈ entriesOf p s m, x.isFor m s.sessionId k = true →
      spec.windowMs.all (x.time + · > e.time) = false := fun x hx hi =>
    hout x hx (isFor_iff.mp hi).1 (isFor_iff.mp hi).2.1 (isFor_iff.mp hi).2.2
  have hstale : Stale p s e.time m k := fun en hf spec' hs' => by
    rw [hs] at hs'
    cases hs'
    have hi := List.find?_some hf
    exact hout' en (List.mem_of_find?_eq_some hf) hi
  have hsm := Dispatch.stale_iff.mpr ⟨hmr, hstale⟩
  obtain ⟨spec', hs', -, hroom⟩ := claimed_fits h he hc hm hr hmr fun _ => hstale
  rw [hs] at hs'
  cases hs'
  have hroom := hroom cap hcap
  have hR : (p.action? c.tool).getD {} = r := by rw [hr]; rfl
  have hret : (c.status == .unknown) = true := by rw [hst]; rfl
  have hnd : (s.staleMeters p e.time r.meters k).Nodup := by
    unfold State.staleMeters
    exact (WF.meters_nodup hwf hr).filter _
  have hw := WF.window_pos hwf hs
  rw [claimed_entries h he hc, hR, hret, entriesOf_claim_retry]
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup hnd hsm
  rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [retime_fold_other hs post _ hpost]
  obtain ⟨hu, hsub, hsid⟩ := foldl_keep (fun s' => usageAt spec (entriesOf p s' m) m e.time =
      usageAt spec (entriesOf p s m) m e.time ∧
      ((entriesOf p s' m).filter (·.isFor m s.sessionId k)).Sublist
        ((entriesOf p s m).filter (·.isFor m s.sessionId k)) ∧ s'.sessionId = s.sessionId)
    (f := fun s m' => s.retime p m' k e.time) (fun s' _ hy ⟨hu, hsub, hsid⟩ =>
      ⟨(retime_other hs hy).trans hu, (retime_own hy).trans hsub,
        updateEntries_sessionId.trans hsid⟩)
    pre s hpre ⟨rfl, List.Sublist.refl _, rfl⟩
  rw [retime_self hs hw (fun x hx hi => by
    rw [hsid] at hi
    have hm := hsub.subset (List.mem_filter.mpr ⟨hx, hi⟩)
    exact hout' x (List.mem_filter.mp hm).1 hi), hu, hsid]
  have hone' : ((entriesOf p s m).filter (·.isFor m s.sessionId k)).length ≤ 1 := by
    simpa only [isFor_decide] using hone
  have hsum := sum_le (Nat.le_trans hsub.length_le hone') fun x hx => by
    have hm := List.mem_filter.mp (hsub.subset hx)
    have hi := isFor_iff.mp hm.2
    exact hamt x hm.1 hi.1 hi.2.1 hi.2.2
  omega

theorem meter_per_call (hwf : p.WF) (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .authorized) (hm : p.modeOf c.tool = .enforce)
    (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hx : spec.maxPerCall = some mx) :
    ∀ en ∈ entriesOf p (step p s e).1 m, en ∉ entriesOf p s m → en.meter = m → en.amount ≤ mx := by
  obtain ⟨spec', hs', hshape, -⟩ := claimed_fits h he hc hm hr hmr fun hu => by
    rw [hst] at hu; cases hu
  rw [hs] at hs'
  cases hs'
  have hshape := shape_per_call hwf hs hx hshape
  have hR : (p.action? c.tool).getD {} = r := by rw [hr]; rfl
  have hret : (c.status == .unknown) = false := by rw [hst]; rfl
  rw [claimed_entries h he hc, hR, hret, entriesOf_claim_first]
  have inv := foldl_invariant
    (f := fun s m' => s.reserve p m' k (p.callAmount m' c.cost) e.time)
    (fun s' => ∀ x ∈ entriesOf p s' m, x ∉ entriesOf p s m →
      x.meter = m → x.amount = p.callAmount m c.cost)
    (fun s' m' ih x hx hn hxm => by
      rcases reserve_mem hx with hx | ⟨hm', ha⟩
      · exact ih x hx hn hxm
      · rw [ha, ← hm', hxm])
    r.meters (s.consumeGrant k) (fun x hx hn _ => absurd (entriesOf_consumeGrant ▸ hx) hn)
  intro x hx hn hxm
  rw [inv x hx hn hxm, callAmount_eq hs]
  exact hshape

/-- Section 8, theorem 8: a claimed first attempt found room for its draw on each meter it
reserves. -/
theorem meter_room (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hst : c.status = .authorized) (hm : p.modeOf c.tool = .enforce)
    (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap) :
    usageAt spec (entriesOf p s m) m e.time + draw spec c.cost ≤ cap := by
  obtain ⟨spec', hs', -, hroom⟩ := claimed_fits h he hc hm hr hmr fun hu => by
    rw [hst] at hu; cases hu
  rw [hs] at hs'
  cases hs'
  exact hroom cap hcap

/-- Section 8, theorem 8: a claimed retry whose reservation has left the window found room for
its draw again. -/
theorem meter_room_retry (h : (step p s e).2.claimed = true)
    (he : e.body = .dispatch k n dg cost g key) (hc : s.calls[k]? = some c)
    (hm : p.modeOf c.tool = .enforce)
    (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap)
    (hout : ∀ en ∈ ownEntries p s m k, spec.windowMs.all (en.time + · > e.time) = false) :
    usageAt spec (entriesOf p s m) m e.time + draw spec c.cost ≤ cap := by
  obtain ⟨spec', hs', -, hroom⟩ := claimed_fits h he hc hm hr hmr fun _ => stale_of_out hs hout
  rw [hs] at hs'
  cases hs'
  exact hroom cap hcap

/-- Section 8, theorem 8: while usage is above the cap, no first attempt on the meter is claimed,
nor a retry whose reservation has left the window. -/
theorem no_claim_over_cap (he : e.body = .dispatch k n dg cost g key)
    (hc : s.calls[k]? = some c) (hm : p.modeOf c.tool = .enforce)
    (hr : p.action? c.tool = some r) (hmr : m ∈ r.meters) (hs : p.meter? m = some spec)
    (hcap : spec.cap = some cap) (hover : cap < usageAt spec (entriesOf p s m) m e.time)
    (hfresh : c.status = .authorized ∨
      ∀ en ∈ ownEntries p s m k, spec.windowMs.all (en.time + · > e.time) = false) :
    (step p s e).2.claimed = false := by
  cases h : (step p s e).2.claimed
  · rfl
  · have hroom : usageAt spec (entriesOf p s m) m e.time + draw spec c.cost ≤ cap := by
      rcases hfresh with hst | hout
      · exact meter_room h he hc hst hm hr hmr hs hcap
      · exact meter_room_retry h he hc hm hr hmr hs hcap hout
    omega

/-- Section 8, theorem 8: every overrun counts as one failure, of the session and of the tool of
the call the `result` or `reconcile` reports, a failed outcome with an overrun included. -/
theorem overrun_fails (hrch : Reachable p d s) (h : (step p s e).2 = .ok (.overrun ms) sh) :
    ∃ (k : String) (c : CallRec), s.calls[k]? = some c ∧
      (step p s e).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (step p s e).1.failures[c.tool]? = some (s.failures.getD c.tool 0 + 1) ∧
      ((∃ o act ne, e.body = .result k o act ne) ∨ ∃ o act ne, e.body = .reconcile k o act ne) := by
  have ha : (step p s e).2.accepted = true := by rw [h]; rfl
  rw [accepted_step ha] at h ⊢
  exact stepHandle_overrun (NoClaimed.reachable hrch) h

namespace Meters

def usd : MeterSpec := { unit := .money "USD", cap := some 100, windowMs := some 10 }

def capAction : Requirements :=
  { meters := ["usd"], idempotent := true, retryAfterUnknown := true, maxAttempts := 2 }

def capPolicy : Policy := { meters := [("usd", usd)], actions := [("t", capAction)] }

def capOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨60, "USD"⟩) [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "t" "d2" (some ⟨60, "USD"⟩) [] []⟩ ]

def firstClaim : Event := ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩

def secondClaim : Event := ⟨6, 6, 5, none, .dispatch "c2" 1 "d2" (some ⟨60, "USD"⟩) [] "k2"⟩

def capUnknown : List Event := capOpen ++ [firstClaim, ⟨6, 6, 5, none, .outcomeUnknown "c1"⟩]

/-- Time 20 is past the first reservation's window (5 + 10), so the retry must fit the cap again. -/
def retryClaim : Event := ⟨7, 20, 6, none, .dispatch "c1" 2 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩

def own (s : State) (en : MeterEntry) : Bool :=
  en.meter == "usd" && en.session == s.sessionId && en.call == "c1"

#guard decide capPolicy.WF
#guard capPolicy.modeOf "t" == .enforce
#guard capPolicy.meter? "usd" == some usd

#guard (step capPolicy (after capPolicy "pd" capOpen) firstClaim).2.claimed
#guard ((after capPolicy "pd" capOpen).calls["c1"]?.map (·.status)) == some .authorized
#guard usageAt usd (entriesOf capPolicy (step capPolicy (after capPolicy "pd" capOpen) firstClaim).1
  "usd") "usd" 5 == 60
#guard (step capPolicy (after capPolicy "pd" (capOpen ++ [firstClaim])) secondClaim).2
  == .rejected .meterExceeded

#guard (trace capPolicy (State.initial "pd") capUnknown).all (·.2.2.accepted)
#guard (step capPolicy (after capPolicy "pd" capUnknown) retryClaim).2.claimed
#guard ((after capPolicy "pd" capUnknown).calls["c1"]?.map (·.status)) == some .unknown
#guard (entriesOf capPolicy (after capPolicy "pd" capUnknown) "usd").all fun en =>
  !own (after capPolicy "pd" capUnknown) en || !usd.windowMs.all (en.time + · > 20)
#guard ((entriesOf capPolicy (after capPolicy "pd" capUnknown) "usd").filter
  (own (after capPolicy "pd" capUnknown))).length == 1
#guard (entriesOf capPolicy (after capPolicy "pd" capUnknown) "usd").all fun en =>
  !own (after capPolicy "pd" capUnknown) en || decide (en.amount ≤ draw usd (some ⟨60, "USD"⟩))
#guard usageAt usd (entriesOf capPolicy (step capPolicy (after capPolicy "pd" capUnknown)
  retryClaim).1 "usd") "usd" 20 == 60

def small : MeterSpec := { unit := .money "USD", maxPerCall := some 50 }

def perCallPolicy : Policy :=
  { meters := [("small", small)], actions := [("t", { meters := ["small"] })] }

def perCallOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨40, "USD"⟩) [] []⟩ ]

def perCallClaim : Event := ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" (some ⟨40, "USD"⟩) [] "k1"⟩

def overPerCall : Event := ⟨4, 4, 3, none, .propose "c2" "t" "d2" (some ⟨60, "USD"⟩) [] []⟩

#guard decide perCallPolicy.WF
#guard (step perCallPolicy (after perCallPolicy "pd" perCallOpen) perCallClaim).2.claimed
#guard ((after perCallPolicy "pd" perCallOpen).calls["c1"]?.map (·.status)) == some .authorized
#guard (entriesOf perCallPolicy (step perCallPolicy (after perCallPolicy "pd" perCallOpen)
  perCallClaim).1 "small").map (·.amount) == [40]
#guard (step perCallPolicy (after perCallPolicy "pd" perCallOpen) overPerCall).2
  == .ok (.denied .costAbovePerCall) none

-- Shows `meter_per_call` needs `en.meter = m`: a calls entry of 1 lands in a list capped at 0.
def zeroPolicy : Policy :=
  { meters := [("usd", { unit := .money "USD", maxPerCall := some 0 }), ("n", { unit := .calls })]
    actions := [("t", { meters := ["usd", "n"] })] }

def zeroOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨0, "USD"⟩) [] []⟩ ]

def zeroClaim : Event := ⟨4, 4, 3, none, .dispatch "c1" 1 "d1" (some ⟨0, "USD"⟩) [] "k1"⟩

#guard decide zeroPolicy.WF
#guard (step zeroPolicy (after zeroPolicy "pd" zeroOpen) zeroClaim).2.claimed
#guard (entriesOf zeroPolicy (after zeroPolicy "pd" zeroOpen) "usd").isEmpty
#guard (entriesOf zeroPolicy (step zeroPolicy (after zeroPolicy "pd" zeroOpen) zeroClaim).1
  "usd").map (fun en => (en.meter, en.amount)) == [("usd", 0), ("n", 1)]

-- A synced ledger that lists the retried call's reservation twice is refused, so the retry after
-- it stays within the cap instead of retiming both copies to 120.
def dupPolicy : Policy :=
  { meters := [("usd", { usd with scope := .principal })], actions := [("t", capAction)] }

def dupEntry : MeterEntry :=
  { meter := "usd", session := "s1", call := "c1", time := 5, amount := 60, committed := false }

def syncOf (entries : List MeterEntry) : Event :=
  ⟨7, 7, 6, none, .ledgerSync { version := 5, entries }⟩

def dupSync : List Event := capUnknown ++ [syncOf [dupEntry, dupEntry]]

def dupRetry : Event := ⟨8, 20, 6, none, .dispatch "c1" 2 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩

#guard decide dupPolicy.WF
#guard (after dupPolicy "pd" capUnknown).ledger.entries == [dupEntry]
#guard (step dupPolicy (after dupPolicy "pd" capUnknown) (syncOf [dupEntry])).2.accepted
#guard (trace dupPolicy (State.initial "pd") capUnknown).all (·.2.2.accepted)
#guard (step dupPolicy (after dupPolicy "pd" capUnknown) (syncOf [dupEntry, dupEntry])).2
  == .rejected .ledgerConflict
#guard (step dupPolicy (after dupPolicy "pd" dupSync) dupRetry).2.claimed
#guard usageAt usd (entriesOf dupPolicy (step dupPolicy (after dupPolicy "pd" dupSync)
  dupRetry).1 "usd") "usd" 20 == 60

-- Shows `meter_cap_retry_of` needs `hamt`: an own entry above the draw passes the room check and
-- reaches 1000.
def bigState : State :=
  let s := after capPolicy "pd" capUnknown
  { s with sessionMeters := [{ dupEntry with amount := 1000 }] }

#guard (step capPolicy bigState retryClaim).2.claimed
#guard ((entriesOf capPolicy bigState "usd").filter (own bigState)).length == 1
#guard usageAt usd (entriesOf capPolicy (step capPolicy bigState retryClaim).1 "usd") "usd" 20
  == 1000

def overrunOpen : List Event := capOpen ++ [firstClaim]

/-- `c1` reserved 60 and reports 120, so 60 of excess lands at time 6 on a cap of 100. -/
def overrunResult : Event := ⟨6, 6, 5, none, .result "c1" .succeeded (some 120) false⟩

def afterOverrun : List Event := overrunOpen ++ [overrunResult]

def overClaim : Event := ⟨7, 7, 6, none, .dispatch "c2" 1 "d2" (some ⟨60, "USD"⟩) [] "k2"⟩

#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" capOpen) "usd") "usd" 5 +
  draw usd (some ⟨60, "USD"⟩) == 60
#guard (trace capPolicy (State.initial "pd") afterOverrun).all (·.2.2.accepted)
#guard ((after capPolicy "pd" overrunOpen).calls["c1"]?.map (·.status)) == some .dispatched
#guard ((after capPolicy "pd" overrunOpen).calls["c1"]?.map (·.tool)) == some "t"
#guard (step capPolicy (after capPolicy "pd" overrunOpen) overrunResult).2
  == .ok (.overrun ["usd"]) none
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" overrunOpen) "usd") "usd" 6 == 60
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" afterOverrun) "usd") "usd" 6 == 120
#guard (after capPolicy "pd" overrunOpen).failuresThisSession == 0
#guard (after capPolicy "pd" afterOverrun).failuresThisSession == 1
#guard (after capPolicy "pd" overrunOpen).failures.getD "t" 0 == 0
#guard (after capPolicy "pd" afterOverrun).failures["t"]? == some 1
#guard ((after capPolicy "pd" afterOverrun).calls["c2"]?.map (·.status)) == some .authorized
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" afterOverrun) "usd") "usd" 7 == 120
#guard (step capPolicy (after capPolicy "pd" afterOverrun) overClaim).2
  == .rejected .meterExceeded

/-- `c1` goes Unknown, then `c2` reserves at 16, after `c1`'s window (5 + 10), and overruns. -/
def staleOver : List Event :=
  capUnknown ++
    [ ⟨7, 16, 6, none, .dispatch "c2" 1 "d2" (some ⟨60, "USD"⟩) [] "k2"⟩
    , ⟨8, 17, 7, none, .result "c2" .succeeded (some 120) false⟩ ]

def staleRetry : Event := ⟨9, 18, 8, none, .dispatch "c1" 2 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩

#guard (trace capPolicy (State.initial "pd") staleOver).all (·.2.2.accepted)
#guard ((after capPolicy "pd" staleOver).calls["c1"]?.map (·.status)) == some .unknown
#guard (ownEntries capPolicy (after capPolicy "pd" staleOver) "usd" "c1").length == 1
#guard (ownEntries capPolicy (after capPolicy "pd" staleOver) "usd" "c1").all fun en =>
  !usd.windowMs.all (en.time + · > 18)
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" staleOver) "usd") "usd" 18 == 120
#guard (step capPolicy (after capPolicy "pd" staleOver) staleRetry).2 == .rejected .meterExceeded

def fullOpen : List Event :=
  [ ⟨1, 1, 0, none, .sessionStart "s1" "pd" "u1" [] [] {}⟩
  , ⟨2, 2, 1, none, .turnStart true⟩
  , ⟨3, 3, 2, none, .propose "c1" "t" "d1" (some ⟨60, "USD"⟩) [] []⟩
  , ⟨4, 4, 3, none, .propose "c2" "t" "d2" (some ⟨40, "USD"⟩) [] []⟩
  , ⟨5, 5, 4, none, .dispatch "c1" 1 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩
  , ⟨6, 6, 5, none, .dispatch "c2" 1 "d2" (some ⟨40, "USD"⟩) [] "k2"⟩
  , ⟨7, 7, 6, none, .outcomeUnknown "c1"⟩ ]

/-- Time 8 is inside `c1`'s reservation window (5 + 10), so the retry reuses it on a full meter. -/
def reuseRetry : Event := ⟨8, 8, 7, none, .dispatch "c1" 2 "d1" (some ⟨60, "USD"⟩) [] "k1"⟩

#guard (trace capPolicy (State.initial "pd") fullOpen).all (·.2.2.accepted)
#guard ((after capPolicy "pd" fullOpen).calls["c1"]?.map (·.status)) == some .unknown
#guard (ownEntries capPolicy (after capPolicy "pd" fullOpen) "usd" "c1").any fun en =>
  usd.windowMs.all (en.time + · > 8)
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" fullOpen) "usd") "usd" 8 == 100
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" fullOpen) "usd") "usd" 8 +
  draw usd (some ⟨60, "USD"⟩) > 100
#guard (step capPolicy (after capPolicy "pd" fullOpen) reuseRetry).2.claimed
#guard usageAt usd (entriesOf capPolicy (step capPolicy (after capPolicy "pd" fullOpen)
  reuseRetry).1 "usd") "usd" 8 == 100

#guard (ownEntries capPolicy (after capPolicy "pd" capUnknown) "usd" "c1").all fun en =>
  !usd.windowMs.all (en.time + · > 20)
#guard usageAt usd (entriesOf capPolicy (after capPolicy "pd" capUnknown) "usd") "usd" 20 +
  draw usd (some ⟨60, "USD"⟩) == 60

def logPolicy : Policy :=
  { meters := [("usd", usd)], actions := [("t", { capAction with mode := some .logOnly })] }

def logOpen : List Event := capOpen ++ [firstClaim]

#guard decide logPolicy.WF
#guard logPolicy.modeOf "t" == .logOnly
#guard (trace logPolicy (State.initial "pd") logOpen).all (·.2.2.accepted)
#guard (step logPolicy (after logPolicy "pd" logOpen) secondClaim).2
  == .ok .dispatchClaimed (some (.wouldDeny .meterExceeded))
#guard usageAt usd (entriesOf logPolicy (after logPolicy "pd" logOpen) "usd") "usd" 6 == 60
#guard usageAt usd (entriesOf logPolicy (step logPolicy (after logPolicy "pd" logOpen)
  secondClaim).1 "usd") "usd" 6 == 120

end Meters

end Writ.Proofs
