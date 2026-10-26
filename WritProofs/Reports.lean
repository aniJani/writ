import WritProofs.Support

namespace Writ.Proofs

open Writ Usage Basic Meters Accounting

variable {p : Policy} {d : String} {s : State} {e : Event} {k m : String} {c : CallRec}
  {r : Requirements} {spec : MeterSpec} {t : Nat} {o : Outcome} {act : Option Nat} {ne : Bool}
  {ms : List String} {en : MeterEntry}

namespace Reports

/-- One step of the kernel's `State.settle` fold, so the fold can be taken apart by induction. -/
def settleStep (p : Policy) (k : String) (o : Outcome) (act : Option Nat) (ne : Bool) (t : Nat) :
    State × List String → String → State × List String :=
  fun (acc, over) m =>
    let held := acc.reserved p m k
    if ne || o == .declined then (acc.release p m k t, over)
    else if p.isMoney m then
      let amount := act.getD held
      (acc.commit p m k amount t, if amount > held then over ++ [m] else over)
    else (acc.commit p m k held t, over)

theorem settle_eq : s.settle p ms k o act ne t = ms.foldl (settleStep p k o act ne t) (s, []) :=
  rfl

theorem reserved_own :
    s.reserved p m k = ((ownEntries p s m k).head?.map (·.amount)).getD 0 := by
  unfold State.reserved State.entry?
  rw [meterEntries_eq, ← List.head?_filter, ← own_eq]

theorem step_prunes (b : State × List String) {m' : String} (hne : m' ≠ m) :
    Prunes p t (ownEntries p b.1 m k) (ownEntries p (settleStep p k o act ne t b m').1 m k) := by
  obtain ⟨acc, over⟩ := b
  unfold settleStep
  dsimp only
  split
  · exact own_release_other (.inl hne)
  · split <;> exact own_commit_other (.inl hne)

theorem step_other {b : State × List String} {m' : String} (hne : m' ≠ m)
    (h1 : ownEntries p b.1 m k = [en]) (hu : en.committed = false) :
    ownEntries p (settleStep p k o act ne t b m').1 m k = [en] := by
  have hp := step_prunes (p := p) (k := k) (o := o) (act := act) (ne := ne) (t := t) b hne
  rw [h1] at hp
  exact hp.single hu

theorem step_over {over : List String} (hrel : (ne || o == .declined) = false) :
    (settleStep p k o act ne t (s, over) m).2 = over ++
      (if (p.isMoney m && decide (act.getD (s.reserved p m k) > s.reserved p m k)) = true
        then [m] else []) := by
  unfold settleStep
  dsimp only
  rw [hrel]
  cases hm : p.isMoney m <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.true_and,
    Bool.false_and, List.append_nil, decide_eq_true_eq]
  split <;> simp

theorem fold_over (hrel : (ne || o == .declined) = false) :
    ∀ (ms : List String) (s : State) (over : List String), ms.Nodup →
      (∀ m ∈ ms, ∃ en, ownEntries p s m k = [en] ∧ en.committed = false) →
      (ms.foldl (settleStep p k o act ne t) (s, over)).2 = over ++ ms.filter fun m =>
        p.isMoney m && decide (act.getD (s.reserved p m k) > s.reserved p m k)
  | [], _, over, _, _ => by simp
  | m₀ :: ms, s, over, hnd, hown => by
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    have hs : ∀ m ∈ ms, ownEntries p (settleStep p k o act ne t (s, over) m₀).1 m k =
        ownEntries p s m k := by
      intro m hm
      obtain ⟨en, h1, hu⟩ := hown m (List.mem_cons_of_mem _ hm)
      rw [h1]
      exact step_other (fun h => hnd.1 (h ▸ hm)) h1 hu
    have ih := fold_over hrel ms (settleStep p k o act ne t (s, over) m₀).1
      (settleStep p k o act ne t (s, over) m₀).2 hnd.2 fun m hm => by
        rw [hs m hm]; exact hown m (List.mem_cons_of_mem _ hm)
    have hf : (ms.filter fun m =>
        p.isMoney m && decide (act.getD ((settleStep p k o act ne t (s, over) m₀).1.reserved p m k) >
          (settleStep p k o act ne t (s, over) m₀).1.reserved p m k)) =
        ms.filter fun m => p.isMoney m && decide (act.getD (s.reserved p m k) > s.reserved p m k) :=
      List.filter_congr fun m hm => by rw [reserved_own, reserved_own (s := s), hs m hm]
    have hp : (settleStep p k o act ne t (s, over) m₀) =
        ((settleStep p k o act ne t (s, over) m₀).1, (settleStep p k o act ne t (s, over) m₀).2) :=
      rfl
    rw [hp, ih, hf, step_over hrel, List.filter_cons, List.append_assoc]
    split <;> simp

/-- The overrun meters a settle that does not release reports: the money meters on which the
actual cost (or the reservation, when none is reported) is above the reservation. -/
theorem settle_over (hnd : ms.Nodup) (hrel : (ne || o == .declined) = false)
    (hown : ∀ m ∈ ms, ∃ en, ownEntries p s m k = [en] ∧ en.committed = false) :
    (s.settle p ms k o act ne t).2 = ms.filter fun m =>
      p.isMoney m && decide (act.getD (s.reserved p m k) > s.reserved p m k) := by
  rw [settle_eq, fold_over hrel ms s [] hnd hown, List.nil_append]

/-- A settle that does not release commits a single uncommitted own entry on `m` at exactly the
actual cost on a money meter (the reservation when none is reported) and at the reservation on a
calls meter; the committed entry then stays unless pruning drops it at `t`. -/
theorem settle_entry (hnd : ms.Nodup) (hm : m ∈ ms) (hrel : (ne || o == .declined) = false)
    (h1 : ownEntries p s m k = [en]) (hu : en.committed = false) :
    ownEntries p (s.settle p ms k o act ne t).1 m k =
        [commitAs (if p.isMoney m then act.getD en.amount else en.amount) t en] ∨
      (ownEntries p (s.settle p ms k o act ne t).1 m k = [] ∧
        Pruned p t (commitAs (if p.isMoney m then act.getD en.amount else en.amount) t en)) := by
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup hnd hm
  rw [settle_eq, hsplit]
  obtain ⟨l₁, l₂, h₁, hR, h₃⟩ := fold_focus (fun b : State × List String => ownEntries p b.1 m k)
    (R := fun l l' => ∀ x, l = [x] →
      l' = [commitAs (if p.isMoney m then act.getD x.amount else x.amount) t x])
    (fun b m' hm' => step_prunes b fun he => hpre (he ▸ hm'))
    (fun b m' hm' => step_prunes b fun he => hpost (he ▸ hm'))
    (fun ⟨acc, over⟩ => by
      refine ⟨(ownEntries p acc m k).map
        (commitAs (if p.isMoney m then act.getD (acc.reserved p m k) else acc.reserved p m k) t),
        fun x hx => by rw [hx, reserved_own, hx]; rfl, ?_⟩
      unfold settleStep
      dsimp only
      rw [hrel]
      cases p.isMoney m
      · exact own_commit_map
      · exact own_commit_map)
    (s, [])
  rw [h1] at h₁
  rw [hR en (h₁.single hu)] at h₃
  exact h₃.single_or

theorem draw_money {cur : String} {cost : Option Cost} (hu : spec.unit = .money cur) :
    draw spec cost = (cost.map (·.amount)).getD 0 := by
  unfold draw; rw [hu]

theorem isMoney_of {cur : String} (hs : p.meter? m = some spec) (hu : spec.unit = .money cur) :
    p.isMoney m = true := by
  simp [Policy.isMoney, hs, hu]

theorem money_of (h : p.isMoney m = true) :
    ∃ spec cur, p.meter? m = some spec ∧ spec.unit = .money cur := by
  unfold Policy.isMoney at h
  cases hs : p.meter? m with
  | none => rw [hs] at h; cases h
  | some spec =>
    rw [hs] at h
    cases hu : spec.unit with
    | money cur => exact ⟨spec, cur, rfl, hu⟩
    | calls => simp [hu] at h

/-- What an accepted `result` or `reconcile` of call `k` that does not release does to the call's
own entries and what it decides, from a reachable state. -/
theorem report_settle (hwf : p.WF) (hr : Reachable p d s) (ha : (step p s e).2.accepted = true)
    (he : e.body = .result k o act false ∨ e.body = .reconcile k o act false)
    (ho : o ≠ .declined) (hc : s.calls[k]? = some c) (hra : p.action? c.tool = some r) :
    (∀ m ∈ r.meters, ∀ spec, p.meter? m = some spec → ∃ en, ownEntries p s m k = [en] ∧
      en.committed = false ∧ en.excess = 0 ∧ en.amount = draw spec c.cost ∧
      (ownEntries p (step p s e).1 m k =
          [commitAs (if p.isMoney m then act.getD en.amount else en.amount) e.time en] ∨
        (ownEntries p (step p s e).1 m k = [] ∧
          Pruned p e.time (commitAs (if p.isMoney m then act.getD en.amount else en.amount)
            e.time en)))) ∧
    (step p s e).2 = .ok (.ofOverrun (r.meters.filter fun m =>
      p.isMoney m && decide (act.getD (s.reserved p m k) > s.reserved p m k))) none := by
  have hh : Holds c := by
    rcases he with he | he
    · obtain ⟨-, c₀, hc₀, hst⟩ := (accepted_iff_result he).mp ha
      rw [hc] at hc₀; cases hc₀; exact .inl hst
    · obtain ⟨-, c₀, hc₀, hst, hrc⟩ := (accepted_iff_reconcile he).mp ha
      rw [hc] at hc₀; cases hc₀; exact .inr ⟨hst, hrc⟩
  have h := inv_reachable hwf hr
  have ha1 : 1 ≤ c.attempts := (h.recs k c hc).2.2 (hh.imp id (·.1))
  have hk := accepted_step ha
  have ha' : (stepHandle p s e).2.accepted = true := by rw [hk] at ha; exact ha
  obtain ⟨c₀, c', hc₀, hsame, hv⟩ : ∃ c₀ c', s.calls[k]? = some c₀ ∧
      Same (State.settle p { s with calls := s.calls.insert k c' } (callMeters p c₀) k o act false
        e.time).1 (stepHandle p s e).1 ∧
      (stepHandle p s e).2 = .ok (.ofOverrun (State.settle p { s with calls := s.calls.insert k c' }
        (callMeters p c₀) k o act false e.time).2) none := by
    rcases he with he | he
    · have hs : stepHandle p s e = handleResult p s e.time k o act false := by
        simp only [stepHandle, he]
      rw [hs] at ha' ⊢
      exact handleResult_settles ha'
    · have hs : stepHandle p s e = handleReconcile p s e.time k o act false := by
        simp only [stepHandle, he]
      rw [hs] at ha' ⊢
      exact handleReconcile_settles ha'
  rw [hc] at hc₀
  cases hc₀
  have hms : callMeters p c = r.meters := by unfold callMeters; rw [hra]; rfl
  rw [hms] at hsame hv
  have hrel : (false || o == .declined) = false := by cases o <;> simp_all
  have hnd := WF.meters_nodup hwf hra
  have hown : ∀ m ∈ r.meters, ∃ en, ownEntries p s m k = [en] ∧ en.committed = false := by
    intro m hm
    obtain ⟨en, hen, hu, -⟩ := h.held k c r m hc hra hm ha1 hh
    exact ⟨en, hen, hu⟩
  have hstep : Same (State.settle p { s with calls := s.calls.insert k c' } r.meters k o act false
      e.time).1 (step p s e).1 :=
    hsame.trans (s₂ := (step p s e).1) (by rw [hk]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  refine ⟨fun m hm spec hs => ?_, ?_⟩
  · obtain ⟨en, hen, hu, hx0, hamt⟩ := h.held k c r m hc hra hm ha1 hh
    refine ⟨en, hen, hu, hx0, by rw [hamt, callAmount_eq hs], ?_⟩
    rw [own_same hstep]
    exact settle_entry (s := { s with calls := s.calls.insert k c' }) hnd hm hrel hen hu
  · rw [hk]
    dsimp only
    rw [hv, settle_over (s := { s with calls := s.calls.insert k c' }) hnd hrel hown]
    rfl

theorem own_meter (hen : ownEntries p s m k = [en]) : en.meter = m := by
  have hin : en ∈ ownEntries p s m k := by rw [hen]; exact List.mem_singleton_self en
  exact (isFor_iff.mp (own_isFor hin)).1

theorem reserved_of (hen : ownEntries p s m k = [en]) : s.reserved p m k = en.amount := by
  rw [reserved_own, hen]; rfl

end Reports

open Reports

/-- Section 8, theorem 8, an overrun is committed in full: an accepted `result` or `reconcile` that
does not release (no `no_effect`, an outcome other than `declined`) and reports an actual cost `a`
above the call's draw on money meter `m` of its action turns the call's reservation `en` on `m`
into one committed entry whose amount plus excess is `a`: the reserved amount at the reservation's
time, and the rest dated at the report. -/
theorem overrun_commits_actual {a : Nat} {cur : String} (hwf : p.WF) (hr : Reachable p d s)
    (ha : (step p s e).2.accepted = true)
    (he : e.body = .result k o (some a) false ∨ e.body = .reconcile k o (some a) false)
    (ho : o ≠ .declined) (hc : s.calls[k]? = some c) (hra : p.action? c.tool = some r)
    (hmr : m ∈ r.meters) (hs : p.meter? m = some spec) (hu : spec.unit = .money cur)
    (hover : draw spec c.cost < a) :
    ∃ en en', ownEntries p s m k = [en] ∧ en.committed = false ∧ en.amount = draw spec c.cost ∧
      ownEntries p (step p s e).1 m k = [en'] ∧ en'.committed = true ∧
      en'.amount + en'.excess = a ∧ en'.amount = en.amount ∧ en'.time = en.time ∧
      en'.excessAt = e.time := by
  obtain ⟨hent, -⟩ := report_settle hwf hr ha he ho hc hra
  obtain ⟨en, hen, hu', hx0, hamt, hy⟩ := hent m hmr spec hs
  have hgt : a > en.amount := by omega
  simp only [isMoney_of hs hu, ite_true, Option.getD_some, commitAs, hgt] at hy
  rcases hy with hy | ⟨-, hp⟩
  · exact ⟨en, _, hen, hu', hamt, hy, rfl, by simp only; omega, rfl, rfl, rfl⟩
  · obtain ⟨-, spec', w, hs', hw, -, hx⟩ := hp
    rw [own_meter hen] at hs'
    have hw0 : w ≠ 0 := fun h0 => WF.window_pos hwf hs' (by rw [hw, h0])
    simp only at hx
    omega

/-- Section 8, theorem 8, every overrun counts as a failure: such a report is answered `overrun`
naming `m`, and raises the session's failure total and the call's tool counter by one each. -/
theorem overrun_verdict {a : Nat} {cur : String} (hwf : p.WF) (hr : Reachable p d s)
    (ha : (step p s e).2.accepted = true)
    (he : e.body = .result k o (some a) false ∨ e.body = .reconcile k o (some a) false)
    (ho : o ≠ .declined) (hc : s.calls[k]? = some c) (hra : p.action? c.tool = some r)
    (hmr : m ∈ r.meters) (hs : p.meter? m = some spec) (hu : spec.unit = .money cur)
    (hover : draw spec c.cost < a) :
    ∃ ms, (step p s e).2 = .ok (.overrun ms) none ∧ m ∈ ms ∧
      (step p s e).1.failuresThisSession = s.failuresThisSession + 1 ∧
      (step p s e).1.failures[c.tool]? = some (s.failures.getD c.tool 0 + 1) := by
  obtain ⟨hent, hv⟩ := report_settle hwf hr ha he ho hc hra
  obtain ⟨en, hen, -, -, hamt, -⟩ := hent m hmr spec hs
  have hin : m ∈ r.meters.filter fun m =>
      p.isMoney m && decide ((some a).getD (s.reserved p m k) > s.reserved p m k) :=
    List.mem_filter.mpr ⟨hmr, by
      simp only [isMoney_of hs hu, Bool.true_and, Option.getD_some, reserved_of hen,
        decide_eq_true_eq]
      omega⟩
  rw [ofOverrun_mem hin] at hv
  refine ⟨_, hv, hin, ?_⟩
  obtain ⟨k', c', hc', h1, h2, hb⟩ := overrun_fails hr hv
  have hk : k' = k := by
    rcases hb with ⟨o', a', n', hb⟩ | ⟨o', a', n', hb⟩ <;> rcases he with he | he <;>
      rw [he] at hb <;> cases hb <;> rfl
  subst hk
  rw [hc] at hc'
  cases hc'
  exact ⟨h1, h2⟩

/-- Section 8, theorem 8, what a report at or below the reservation commits: an accepted `result`
or `reconcile` that does not release and reports no actual cost, or one at most the call's draw on
money meter `m` of its action, decides nothing (no overrun on any meter) and turns the call's
reservation `en` on `m` into one committed entry of exactly the reported cost (the reservation when
none is reported), with no excess and the reservation's time; or pruning drops it at once, because
the reservation's time is outside the window. -/
theorem report_commits_actual {cur : String} (hwf : p.WF) (hr : Reachable p d s)
    (ha : (step p s e).2.accepted = true)
    (he : e.body = .result k o act false ∨ e.body = .reconcile k o act false)
    (ho : o ≠ .declined) (hc : s.calls[k]? = some c) (hra : p.action? c.tool = some r)
    (hmr : m ∈ r.meters) (hs : p.meter? m = some spec) (hu : spec.unit = .money cur)
    (hle : ∀ a, act = some a → a ≤ draw spec c.cost) :
    (step p s e).2 = .ok .none none ∧
      ∃ en, ownEntries p s m k = [en] ∧ en.committed = false ∧ en.amount = draw spec c.cost ∧
        ((∃ en', ownEntries p (step p s e).1 m k = [en'] ∧ en'.committed = true ∧
            en'.amount = act.getD en.amount ∧ en'.excess = 0 ∧ en'.time = en.time) ∨
          (ownEntries p (step p s e).1 m k = [] ∧ ∃ w, spec.windowMs = some w ∧
            en.time + w ≤ e.time)) := by
  obtain ⟨hent, hv⟩ := report_settle hwf hr ha he ho hc hra
  have hnone : (r.meters.filter fun m =>
      p.isMoney m && decide (act.getD (s.reserved p m k) > s.reserved p m k)) = [] := by
    refine List.filter_eq_nil_iff.mpr fun m' hm' => ?_
    cases hmo : p.isMoney m'
    · simp
    · obtain ⟨spec', cur', hs', hu'⟩ := money_of hmo
      obtain ⟨en', hen', -, -, hamt', -⟩ := hent m' hm' spec' hs'
      rw [reserved_of hen', hamt', draw_money hu', ← draw_money (cost := c.cost) hu]
      cases hact : act with
      | none => simp
      | some a => simpa using hle a hact
  refine ⟨by rw [hv, hnone]; rfl, ?_⟩
  obtain ⟨en, hen, hu', hx0, hamt, hy⟩ := hent m hmr spec hs
  have hle' : ¬ act.getD en.amount > en.amount := by
    cases hact : act with
    | none => simp
    | some a => have := hle a hact; simp only [Option.getD_some]; omega
  simp only [isMoney_of hs hu, ite_true, commitAs, hle', ite_false] at hy
  refine ⟨en, hen, hu', hamt, ?_⟩
  rcases hy with hy | ⟨hy, hp⟩
  · exact .inl ⟨_, hy, rfl, rfl, hx0, rfl⟩
  · obtain ⟨-, spec', w, hs', hw, ht, -⟩ := hp
    rw [own_meter hen, hs] at hs'
    cases hs'
    exact .inr ⟨hy, w, hw, ht⟩

namespace Reports

def sClaimed : State := after Meters.capPolicy "pd" (Meters.capOpen ++ [Meters.firstClaim])
def sUnknown : State := after Meters.capPolicy "pd" Meters.capUnknown

def reportOf (o : Outcome) (a : Option Nat) : Event := ⟨6, 6, 5, none, .result "c1" o a false⟩
def reconcileOf (o : Outcome) (a : Option Nat) : Event := ⟨7, 7, 6, none, .reconcile "c1" o a false⟩

/-- Amount, excess, time, excess time and committed flag of call `c1`'s entries on `usd`. -/
def c1Entries (x : State) : List (Nat × Nat × Nat × Nat × Bool) :=
  (ownEntries Meters.capPolicy x "usd" "c1").map fun en =>
    (en.amount, en.excess, en.time, en.excessAt, en.committed)

def counts (x : State) : Nat × Nat × Nat × Bool :=
  (x.failuresThisSession, x.failures.getD "t" 0, x.escalations, x.escalated)

#guard decide Meters.capPolicy.WF
#guard Meters.capPolicy.meter? "usd" == some Meters.usd && Meters.usd.unit == .money "USD"
#guard Meters.capPolicy.action? "t" == some Meters.capAction && Meters.capAction.meters == ["usd"]
#guard (sClaimed.calls["c1"]?).any fun c =>
  c.tool == "t" && c.status == .dispatched && draw Meters.usd c.cost == 60
#guard c1Entries sClaimed == [(60, 0, 5, 0, false)]
#guard (sUnknown.calls["c1"]?).any fun c =>
  c.tool == "t" && c.status == .unknown && c.reconciled.isNone && draw Meters.usd c.cost == 60
#guard c1Entries sUnknown == [(60, 0, 5, 0, false)]

-- `overrun_commits_actual` and `overrun_verdict`: a result and a reconcile reporting 90 and 150
-- against a reservation of 60.
#guard (step Meters.capPolicy sClaimed (reportOf .succeeded (some 90))).2
  == .ok (.overrun ["usd"]) none
#guard c1Entries (step Meters.capPolicy sClaimed (reportOf .succeeded (some 90))).1
  == [(60, 30, 5, 6, true)]
#guard counts sClaimed == (0, 0, 0, false)
#guard counts (step Meters.capPolicy sClaimed (reportOf .succeeded (some 90))).1 == (1, 1, 0, false)
#guard (step Meters.capPolicy sUnknown (reconcileOf .succeeded (some 150))).2
  == .ok (.overrun ["usd"]) none
#guard c1Entries (step Meters.capPolicy sUnknown (reconcileOf .succeeded (some 150))).1
  == [(60, 90, 5, 7, true)]
#guard counts sUnknown == (1, 1, 0, false)
#guard counts (step Meters.capPolicy sUnknown (reconcileOf .succeeded (some 150))).1
  == (2, 2, 0, false)

-- `report_commits_actual`: a partial capture, a report without a cost, an exact reconcile.
#guard (step Meters.capPolicy sClaimed (reportOf .succeeded (some 25))).2 == .ok .none none
#guard c1Entries (step Meters.capPolicy sClaimed (reportOf .succeeded (some 25))).1
  == [(25, 0, 5, 0, true)]
#guard (step Meters.capPolicy sClaimed (reportOf .succeeded none)).2 == .ok .none none
#guard c1Entries (step Meters.capPolicy sClaimed (reportOf .succeeded none)).1
  == [(60, 0, 5, 0, true)]
#guard (step Meters.capPolicy sUnknown (reconcileOf .failed (some 60))).2 == .ok .none none
#guard c1Entries (step Meters.capPolicy sUnknown (reconcileOf .failed (some 60))).1
  == [(60, 0, 5, 0, true)]

end Reports

/-- Section 6, Failures and escalation: step `e` from `s` counts one failure of call `k`. It is an
accepted `result` of `k` with outcome `failed`, an accepted `outcome_unknown` of `k`, or an accepted
`result` or `reconcile` of `k` answered `overrun`. A report that is both failed and an overrun is
one step, so it counts once. -/
def CountsFailure (p : Policy) (s : State) (e : Event) (k : String) : Prop :=
  (step p s e).2.accepted = true ∧
    ((∃ act ne, e.body = .result k .failed act ne) ∨ e.body = .outcomeUnknown k ∨
      ∃ o act ne ms sh, (e.body = .result k o act ne ∨ e.body = .reconcile k o act ne) ∧
        (step p s e).2 = .ok (.overrun ms) sh)

/-- Section 6, Failures and escalation: step `e` from `s` is a success of call `k`, an accepted
`result` of `k` with outcome `succeeded` that is not answered `overrun`. -/
def Succeeds (p : Policy) (s : State) (e : Event) (k : String) : Prop :=
  (step p s e).2.accepted = true ∧ (∃ act ne, e.body = .result k .succeeded act ne) ∧
    ∀ ms sh, (step p s e).2 ≠ .ok (.overrun ms) sh

/-- Section 6, Failures and escalation: step `e` from `s` is an accepted `escalation_ack`. -/
def Acks (p : Policy) (s : State) (e : Event) : Prop :=
  (step p s e).2.accepted = true ∧ ∃ a n, e.body = .escalationAck a n

namespace Reports

open Escalation

/-- The escalation state with the escalation count. -/
def eview (s : State) : (Bool × List String × Std.ExtTreeMap String Nat compare × Nat) × Nat :=
  (view s, s.escalations)

theorem releaseGrant_eview : eview (s.releaseGrant k) = eview s := by
  unfold State.releaseGrant; repeat' split
  all_goals rfl

theorem consumeGrant_eview : eview (s.consumeGrant k) = eview s := by
  unfold State.consumeGrant; repeat' split
  all_goals rfl

theorem updateEntries_eview {f : List MeterEntry → List MeterEntry} :
    eview (s.updateEntries p m t f) = eview s := by
  unfold State.updateEntries; split <;> rfl

theorem foldl_eview {α : Type _} {f : State → α → State} (hf : ∀ s a, eview (f s a) = eview s)
    (l : List α) (s : State) : eview (l.foldl f s) = eview s :=
  foldl_invariant (fun b => eview b = eview s) (fun b a hb => (hf b a).trans hb) l s rfl

theorem settle_eview : eview (s.settle p ms k o act ne t).1 = eview s := by
  unfold State.settle
  refine foldl_invariant (fun b : State × List String => eview b.1 = eview s) ?_ ms _ rfl
  intro ⟨acc, over⟩ m h
  dsimp only at h ⊢
  split
  · exact updateEntries_eview.trans h
  · split <;> exact updateEntries_eview.trans h

theorem endCall_eview {st : CallStatus} : eview (s.endCall k st) = eview s := releaseGrant_eview

theorem cancelPending_eview : eview (cancelPending s) = eview s := by
  unfold cancelPending
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  refine foldl_invariant (fun b => eview b = eview s) ?_ _ _ rfl
  intro acc ⟨k, c⟩ ha
  dsimp only
  split
  · exact endCall_eview.trans ha
  · exact endCall_eview.trans ha
  · exact ha

theorem interrupt_eview : eview s.interrupt = eview s := cancelPending_eview

theorem claim_eview {rc : CallRec} {r : Requirements} {key : String} {retry : Bool} :
    eview (claim p s t k rc r retry key) = eview s := by
  unfold claim
  dsimp only
  split
  · exact foldl_eview (fun _ _ => updateEntries_eview) _ _
  · exact (foldl_eview (fun _ _ => updateEntries_eview) _ _).trans consumeGrant_eview

theorem applyApprove_eview {rc : CallRec} {w pr dg : String}
    {cs : Option Cost} {ed : Option Edit} {res : State × Verdict}
    (h : applyApprove p s t k rc w pr dg cs ed = .ok res) : eview res.1 = eview s := by
  unfold applyApprove at h
  repeat' (first | (dsimp only at h) | split at h)
  all_goals (cases h <;> rfl)

local macro "keeps" : tactic =>
  `(tactic| (repeat' (first | (dsimp only) | split)) <;>
    first
      | rfl
      | exact cancelPending_eview
      | exact interrupt_eview
      | exact endCall_eview
      | exact claim_eview
      | exact applyApprove_eview (by assumption))

theorem stepHandle_keeps (h1 : ∀ k o act ne, e.body ≠ .result k o act ne)
    (h2 : ∀ k, e.body ≠ .outcomeUnknown k) (h3 : ∀ k o act ne, e.body ≠ .reconcile k o act ne)
    (h4 : ∀ a n, e.body ≠ .escalationAck a n) : eview (stepHandle p s e).1 = eview s := by
  unfold stepHandle
  split <;> rename_i hb
  · unfold handleSessionStart; keeps
  · unfold handleSessionEnd; keeps
  · unfold handleTurnStart; keeps
  · unfold handleTurnEnd; keeps
  · unfold handleStepStart; keeps
  · unfold handleApproverAttest; keeps
  · unfold handlePermissionRevoke; keeps
  · unfold handlePropose; keeps
  · unfold handleApprove; keeps
  · unfold handleReject
    split
    · rfl
    · exact endCall_eview (s := s) (st := .rejected)
  · unfold handleApprovalExpire; keeps
  · unfold handleGrantCreate; keeps
  · unfold handleGrantRevoke; keeps
  · rcases Dispatch.handle_cases with he | ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] <;>
      first | rfl | exact endCall_eview | exact claim_eview
  · exact absurd hb (h1 _ _ _ _)
  · exact absurd hb (h2 _)
  · exact absurd hb (h3 _ _ _ _)
  · unfold handleCancel; keeps
  · unfold handleReset; keeps
  · unfold handleKill; keeps
  · unfold handlePermissionAdd; keeps
  · exact absurd hb (h4 _ _)
  · unfold handleLedgerSync; keeps

theorem bump_escalations (x : State) :
    (if x.anyBlocked then { x with escalations := x.escalations + 1 } else x).escalations =
      if ((if x.anyBlocked then { x with escalations := x.escalations + 1 } else x).escalated ||
          !(if x.anyBlocked then { x with escalations := x.escalations + 1 } else x).blockedTools.isEmpty)
        = true then x.escalations + 1 else x.escalations := by
  unfold State.anyBlocked
  split <;> simp_all

theorem recordFailure_escalations {tool : String} :
    (s.recordFailure p tool).escalations =
      if ((s.recordFailure p tool).escalated || !(s.recordFailure p tool).blockedTools.isEmpty) = true
      then s.escalations + 1 else s.escalations := by
  unfold State.recordFailure
  dsimp only
  split <;> exact bump_escalations _

theorem handleResult_shape (ha : (handleResult p s t k o act ne).2.accepted = true) :
    ∃ c s₁, s.calls[k]? = some c ∧ eview s₁ = eview s ∧
      (((o = .failed ∨ ∃ ms, (handleResult p s t k o act ne).2 = .ok (.overrun ms) none) ∧
          (handleResult p s t k o act ne).1 = s₁.recordFailure p c.tool) ∨
        (o = .succeeded ∧ (handleResult p s t k o act ne).2 = .ok .none none ∧
          (handleResult p s t k o act ne).1 = s₁.recordSuccess c.tool) ∨
        (o = .declined ∧ (handleResult p s t k o act ne).2 = .ok .none none ∧
          (handleResult p s t k o act ne).1 = s₁)) := by
  revert ha
  unfold handleResult
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hc : s.calls[k]? with
  | none => intro h; cases h
  | some c =>
    intro ha
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hd
      simp only [hd, ↓reduceIte]
      have hv : eview (State.settle p (withStatus s k c o.status) (callMeters p c) k o act ne t).1 =
          eview s := settle_eview
      revert hv
      generalize State.settle p (withStatus s k c o.status) (callMeters p c) k o act ne t = S
      obtain ⟨s₁, over⟩ := S
      intro hv
      refine ⟨c, s₁, rfl, hv, ?_⟩
      cases o <;> cases hov : over.isEmpty <;> simp [Decision.ofOverrun, hov]

theorem handleReconcile_shape (ha : (handleReconcile p s t k o act ne).2.accepted = true) :
    ∃ c s₁, s.calls[k]? = some c ∧ eview s₁ = eview s ∧
      (((∃ ms, (handleReconcile p s t k o act ne).2 = .ok (.overrun ms) none) ∧
          (handleReconcile p s t k o act ne).1 = s₁.recordFailure p c.tool) ∨
        ((handleReconcile p s t k o act ne).2 = .ok .none none ∧
          (handleReconcile p s t k o act ne).1 = s₁)) := by
  revert ha
  unfold handleReconcile
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hc : s.calls[k]? with
  | none => intro h; cases h
  | some c =>
    intro ha
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hu
      split at ha
      · cases ha
      · rename_i hn
        simp only [hu, hn, ↓reduceIte]
        have hv : eview (State.settle p { s with calls := s.calls.insert k { c with reconciled := some o } }
            (callMeters p c) k o act ne t).1 = eview s := settle_eview
        revert hv
        generalize State.settle p { s with calls := s.calls.insert k { c with reconciled := some o } }
          (callMeters p c) k o act ne t = S
        obtain ⟨s₁, over⟩ := S
        intro hv
        refine ⟨c, s₁, rfl, hv, ?_⟩
        cases hov : over.isEmpty <;> simp [Decision.ofOverrun, hov]

theorem handleOutcomeUnknown_shape (ha : (handleOutcomeUnknown p s k).2.accepted = true) :
    ∃ c s₁, s.calls[k]? = some c ∧ eview s₁ = eview s ∧
      (handleOutcomeUnknown p s k).1 = s₁.recordFailure p c.tool := by
  revert ha
  unfold handleOutcomeUnknown
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  cases hc : s.calls[k]? with
  | none => intro h; cases h
  | some c =>
    intro ha
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hd
      simp only [hd, ↓reduceIte]
      exact ⟨c, withStatus s k c .unknown, rfl, rfl, rfl⟩

theorem handleEscalationAck_shape {a : String} {n : Nat}
    (ha : (handleEscalationAck p s a n).2.accepted = true) :
    (handleEscalationAck p s a n).1 =
      { s with escalated := false, blockedTools := [], failures := {}, failuresThisSession := 0 } := by
  revert ha
  unfold handleEscalationAck
  repeat' split
  all_goals first | (intro; rfl) | (intro h; cases h)

theorem counters :
    (∀ k, CountsFailure p s e k → ∃ c s₁, s.calls[k]? = some c ∧ eview s₁ = eview s ∧
      eview (step p s e).1 = eview (s₁.recordFailure p c.tool)) ∧
    (∀ k, Succeeds p s e k → ∃ c s₁, s.calls[k]? = some c ∧ eview s₁ = eview s ∧
      eview (step p s e).1 = eview (s₁.recordSuccess c.tool)) ∧
    (Acks p s e → eview (step p s e).1 =
      eview { s with escalated := false, blockedTools := [], failures := {}, failuresThisSession := 0 }) ∧
    ((∀ k, ¬ CountsFailure p s e k) → (∀ k, ¬ Succeeds p s e k) → ¬ Acks p s e →
      eview (step p s e).1 = eview s) := by
  unfold CountsFailure Succeeds Acks
  cases ha : (step p s e).2.accepted
  · simp only [Bool.false_eq_true, false_and, false_implies, implies_true, true_and]
    intro _ _ _
    rw [frame ha]
  have hk := accepted_step ha
  have ha' : (stepHandle p s e).2.accepted = true := by rw [hk] at ha; exact ha
  have hE : eview (step p s e).1 = eview (stepHandle p s e).1 := by rw [hk]; rfl
  have hV : (step p s e).2 = (stepHandle p s e).2 := by rw [hk]
  rw [hE, hV]
  simp only [true_and]
  clear hE hV hk ha
  by_cases hR : ∃ k o act ne, e.body = .result k o act ne
  · obtain ⟨k, o, act, ne, hb⟩ := hR
    have hs : stepHandle p s e = handleResult p s e.time k o act ne := by simp only [stepHandle, hb]
    rw [hs] at ha'
    obtain ⟨c, s₁, hc, hv1, hsh⟩ := handleResult_shape ha'
    rw [← hs] at hsh
    clear hs ha'
    generalize (stepHandle p s e).2 = v at *
    generalize (stepHandle p s e).1 = s' at *
    simp only [hb, EventBody.result.injEq, reduceCtorEq, exists_false, or_false, false_or,
      exists_and_left, exists_and_right, and_true, exists_eq', true_and, false_implies,
      not_false_eq_true]
    refine ⟨fun k' h => ?_, fun k' h => ?_, fun h1 h2 _ => ?_⟩
    · have hk' : k = k' := by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
      subst hk'
      rcases hsh with ⟨-, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩
      · exact ⟨c, hc, s₁, hv1, rfl⟩
      all_goals simp_all
    · obtain ⟨⟨rfl, ho⟩, hno⟩ := h
      rcases hsh with ⟨h | ⟨ms, hv⟩, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h, rfl, rfl⟩
      · simp_all
      · exact absurd hv (hno ms none)
      · exact ⟨c, hc, s₁, hv1, rfl⟩
      · simp_all
    · rcases hsh with ⟨h | ⟨ms, hv⟩, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨-, -, rfl⟩
      · exact absurd (.inl ⟨rfl, h⟩) (h1 k)
      · exact absurd (.inr ⟨rfl, ms, none, hv⟩) (h1 k)
      · exact absurd ⟨⟨rfl, ho⟩, fun _ _ h => by cases h⟩ (h2 k)
      · exact hv1
  by_cases hU : ∃ k, e.body = .outcomeUnknown k
  · obtain ⟨k, hb⟩ := hU
    have hs : stepHandle p s e = handleOutcomeUnknown p s k := by simp only [stepHandle, hb]
    rw [hs] at ha'
    obtain ⟨c, s₁, hc, hv1, hsh⟩ := handleOutcomeUnknown_shape ha'
    rw [← hs] at hsh
    clear hs ha'
    generalize (stepHandle p s e).2 = v at *
    generalize (stepHandle p s e).1 = s' at *
    subst hsh
    refine ⟨fun k' h => ?_, fun k' h => ?_, fun h => ?_, fun h1 _ _ => ?_⟩
    · rcases h with ⟨_, _, h⟩ | h | ⟨_, _, _, _, _, h | h, -⟩ <;> rw [hb] at h <;> cases h
      exact ⟨c, s₁, hc, hv1, rfl⟩
    · obtain ⟨⟨_, _, h⟩, -⟩ := h; rw [hb] at h; cases h
    · obtain ⟨_, _, h⟩ := h; rw [hb] at h; cases h
    · exact absurd (.inr (.inl hb)) (h1 k)
  by_cases hC : ∃ k o act ne, e.body = .reconcile k o act ne
  · obtain ⟨k, o, act, ne, hb⟩ := hC
    have hs : stepHandle p s e = handleReconcile p s e.time k o act ne := by
      simp only [stepHandle, hb]
    rw [hs] at ha'
    obtain ⟨c, s₁, hc, hv1, hsh⟩ := handleReconcile_shape ha'
    rw [← hs] at hsh
    clear hs ha'
    generalize (stepHandle p s e).2 = v at *
    generalize (stepHandle p s e).1 = s' at *
    refine ⟨fun k' h => ?_, fun k' h => ?_, fun h => ?_, fun h1 _ _ => ?_⟩
    · rcases h with ⟨_, _, h⟩ | h | ⟨_, _, _, ms, sh, h | h, hov⟩ <;> rw [hb] at h <;> cases h
      rcases hsh with ⟨-, rfl⟩ | ⟨hv, -⟩
      · exact ⟨c, s₁, hc, hv1, rfl⟩
      · rw [hv] at hov; cases hov
    · obtain ⟨⟨_, _, h⟩, -⟩ := h; rw [hb] at h; cases h
    · obtain ⟨_, _, h⟩ := h; rw [hb] at h; cases h
    · rcases hsh with ⟨⟨ms, hv⟩, -⟩ | ⟨-, rfl⟩
      · exact absurd (.inr (.inr ⟨o, act, ne, ms, none, .inr hb, hv⟩)) (h1 k)
      · exact hv1
  by_cases hA : ∃ a n, e.body = .escalationAck a n
  · obtain ⟨a, n, hb⟩ := hA
    have hs : stepHandle p s e = handleEscalationAck p s a n := by simp only [stepHandle, hb]
    rw [hs] at ha'
    have hsh := handleEscalationAck_shape ha'
    rw [← hs] at hsh
    clear hs ha'
    refine ⟨fun k' h => ?_, fun k' h => ?_, fun _ => by rw [hsh], fun _ _ h3 => absurd ⟨a, n, hb⟩ h3⟩
    · rcases h with ⟨_, _, h⟩ | h | ⟨_, _, _, _, _, h | h, -⟩ <;> rw [hb] at h <;> cases h
    · obtain ⟨⟨_, _, h⟩, -⟩ := h; rw [hb] at h; cases h
  refine ⟨fun k' h => ?_, fun k' h => ?_, fun h => absurd h hA, fun _ _ _ => stepHandle_keeps
    (fun k o act ne h => hR ⟨k, o, act, ne, h⟩) (fun k h => hU ⟨k, h⟩)
    (fun k o act ne h => hC ⟨k, o, act, ne, h⟩) (fun a n h => hA ⟨a, n, h⟩)⟩
  · rcases h with ⟨act, ne, h⟩ | h | ⟨o, act, ne, -, -, h | h, -⟩
    · exact absurd ⟨k', _, act, ne, h⟩ hR
    · exact absurd ⟨k', h⟩ hU
    · exact absurd ⟨k', o, act, ne, h⟩ hR
    · exact absurd ⟨k', o, act, ne, h⟩ hC
  · obtain ⟨⟨act, ne, h⟩, -⟩ := h
    exact absurd ⟨k', _, act, ne, h⟩ hR

theorem eview_eq {a b : State} (h : eview a = eview b) :
    a.escalated = b.escalated ∧ a.blockedTools = b.blockedTools ∧ a.failures = b.failures ∧
      a.failuresThisSession = b.failuresThisSession ∧ a.escalations = b.escalations := by
  simp only [eview, view, Prod.mk.injEq] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩

theorem getD_insert_ne {f : Std.ExtTreeMap String Nat compare} {a b : String} {v : Nat}
    (h : b ≠ a) : (f.insert a v).getD b 0 = f.getD b 0 := by
  rw [Std.ExtTreeMap.getD_insert]
  split
  · rename_i he
    rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
    exact absurd he.symm h
  · rfl

theorem getD_insert_same {f : Std.ExtTreeMap String Nat compare} {a : String} {v : Nat} :
    (f.insert a v).getD a 0 = v := by
  rw [Std.ExtTreeMap.getD_insert]
  simp

end Reports

open Reports

/-- Section 8, theorem 11, the session failure total counts failures: a step that counts a failure
(`CountsFailure`) raises it by exactly one, an accepted `escalation_ack` resets it to 0, and every
other step, rejected or accepted, leaves it unchanged. -/
theorem failure_total_step :
    (∀ k, CountsFailure p s e k →
      (step p s e).1.failuresThisSession = s.failuresThisSession + 1) ∧
    (Acks p s e → (step p s e).1.failuresThisSession = 0) ∧
    ((∀ k, ¬ CountsFailure p s e k) → ¬ Acks p s e →
      (step p s e).1.failuresThisSession = s.failuresThisSession) := by
  obtain ⟨hf, hs, ha, ho⟩ := counters (p := p) (s := s) (e := e)
  refine ⟨fun k h => ?_, fun h => (eview_eq (ha h)).2.2.2.1, fun h1 h3 => ?_⟩
  · obtain ⟨c, s₁, -, hv, he⟩ := hf k h
    rw [(eview_eq he).2.2.2.1, Escalation.recordFailure_total, (eview_eq hv).2.2.2.1]
  · by_cases h2 : ∃ k, Succeeds p s e k
    · obtain ⟨k, h2⟩ := h2
      obtain ⟨c, s₁, -, hv, he⟩ := hs k h2
      rw [(eview_eq he).2.2.2.1, ← (eview_eq hv).2.2.2.1]
      rfl
    · exact (eview_eq (ho h1 (fun k h => h2 ⟨k, h⟩) h3)).2.2.2.1

/-- Section 8, theorem 11, each tool's consecutive-failure counter: a step that counts a failure of
call `k` raises the counter of `k`'s tool by exactly one, a success of `k` (`Succeeds`) resets that
tool's counter to 0, an accepted `escalation_ack` resets every counter to 0, and every other step
leaves every counter unchanged; no step changes the counter of a tool other than the reported
call's. -/
theorem failure_tool_step :
    (∀ k, CountsFailure p s e k → ∃ c, s.calls[k]? = some c ∧
      (step p s e).1.failures.getD c.tool 0 = s.failures.getD c.tool 0 + 1 ∧
      ∀ t, t ≠ c.tool → (step p s e).1.failures.getD t 0 = s.failures.getD t 0) ∧
    (∀ k, Succeeds p s e k → ∃ c, s.calls[k]? = some c ∧
      (step p s e).1.failures.getD c.tool 0 = 0 ∧
      ∀ t, t ≠ c.tool → (step p s e).1.failures.getD t 0 = s.failures.getD t 0) ∧
    (Acks p s e → ∀ t, (step p s e).1.failures.getD t 0 = 0) ∧
    ((∀ k, ¬ CountsFailure p s e k) → (∀ k, ¬ Succeeds p s e k) → ¬ Acks p s e →
      ∀ t, (step p s e).1.failures.getD t 0 = s.failures.getD t 0) := by
  obtain ⟨hf, hs, ha, ho⟩ := counters (p := p) (s := s) (e := e)
  refine ⟨fun k h => ?_, fun k h => ?_, fun h t => ?_, fun h1 h2 h3 t => ?_⟩
  · obtain ⟨c, s₁, hc, hv, he⟩ := hf k h
    rw [(eview_eq he).2.2.1, Escalation.recordFailure_failures, (eview_eq hv).2.2.1]
    exact ⟨c, hc, getD_insert_same, fun t ht => getD_insert_ne ht⟩
  · obtain ⟨c, s₁, hc, hv, he⟩ := hs k h
    rw [(eview_eq he).2.2.1]
    refine ⟨c, hc, ?_, fun t ht => ?_⟩
    · exact getD_insert_same
    · show (s₁.failures.insert c.tool 0).getD t 0 = _
      rw [getD_insert_ne ht, (eview_eq hv).2.2.1]
  · rw [(eview_eq (ha h)).2.2.1]
    exact Std.ExtTreeMap.getD_empty
  · rw [(eview_eq (ho h1 h2 h3)).2.2.1]

/-- Section 8, theorem 11, the escalation count: a step that counts a failure raises it by one
when, after the step, the session is escalated or some tool is blocked, and leaves it unchanged
otherwise; every other step, an `escalation_ack` included, leaves it unchanged. -/
theorem escalations_step :
    (∀ k, CountsFailure p s e k →
      ((step p s e).1.escalated = true ∨ (step p s e).1.blockedTools ≠ []) →
        (step p s e).1.escalations = s.escalations + 1) ∧
    (∀ k, CountsFailure p s e k → (step p s e).1.escalated = false →
      (step p s e).1.blockedTools = [] → (step p s e).1.escalations = s.escalations) ∧
    ((∀ k, ¬ CountsFailure p s e k) → (step p s e).1.escalations = s.escalations) := by
  obtain ⟨hf, hs, ha, ho⟩ := counters (p := p) (s := s) (e := e)
  refine ⟨fun k h hb => ?_, fun k h he hb => ?_, fun h1 => ?_⟩
  · obtain ⟨c, s₁, -, hv, hst⟩ := hf k h
    obtain ⟨h1, h2, -, -, h5⟩ := eview_eq hst
    rw [h1, h2] at hb
    rw [h5, recordFailure_escalations, (eview_eq hv).2.2.2.2]
    rcases hb with hb | hb <;> simp [hb]
  · obtain ⟨c, s₁, -, hv, hst⟩ := hf k h
    obtain ⟨h1, h2, -, -, h5⟩ := eview_eq hst
    rw [h1] at he
    rw [h2] at hb
    rw [h5, recordFailure_escalations, (eview_eq hv).2.2.2.2]
    simp [he, hb]
  · by_cases h3 : Acks p s e
    · rw [(eview_eq (ha h3)).2.2.2.2]
    · by_cases h2 : ∃ k, Succeeds p s e k
      · obtain ⟨k, h2⟩ := h2
        obtain ⟨c, s₁, -, hv, hst⟩ := hs k h2
        rw [(eview_eq hst).2.2.2.2, ← (eview_eq hv).2.2.2.2]
        rfl
      · exact (eview_eq (ho h1 (fun k h => h2 ⟨k, h⟩) h3)).2.2.2.2

namespace Reports

-- A failed result that also overruns counts once.
#guard (step Meters.capPolicy sClaimed (reportOf .failed (some 90))).2
  == .ok (.overrun ["usd"]) none
#guard counts (step Meters.capPolicy sClaimed (reportOf .failed (some 90))).1 == (1, 1, 0, false)

-- A reconcile counts nothing without an overrun, a failed one included.
#guard counts (step Meters.capPolicy sUnknown (reconcileOf .failed (some 60))).1 == (1, 1, 0, false)

/-- Section 6's counting scenario: failed, succeeded, failed, succeeded, failed under a session
total of 3, then an acknowledgment and a declined result. -/
def alternating : List Event :=
  Escalation.failTwice.take 2 ++
  [ Escalation.ev 3 (.propose "c1" "t" "d1" none [] [])
  , Escalation.ev 4 (.dispatch "c1" 1 "d1" none [] "k1")
  , Escalation.ev 5 (.result "c1" .failed none false)
  , Escalation.ev 6 (.propose "c2" "t" "d2" none [] [])
  , Escalation.ev 7 (.dispatch "c2" 1 "d2" none [] "k2")
  , Escalation.ev 8 (.result "c2" .succeeded none false)
  , Escalation.ev 9 (.propose "c3" "t" "d3" none [] [])
  , Escalation.ev 10 (.dispatch "c3" 1 "d3" none [] "k3")
  , Escalation.ev 11 (.result "c3" .failed none false)
  , Escalation.ev 12 (.propose "c4" "t" "d4" none [] [])
  , Escalation.ev 13 (.dispatch "c4" 1 "d4" none [] "k4")
  , Escalation.ev 14 (.result "c4" .succeeded none false)
  , Escalation.ev 15 (.propose "c5" "t" "d5" none [] [])
  , Escalation.ev 16 (.dispatch "c5" 1 "d5" none [] "k5")
  , Escalation.ev 17 (.result "c5" .failed none false)
  , Escalation.ev 18 (.escalationAck "a1" 1)
  , Escalation.ev 19 (.propose "c6" "t" "d6" none [] [])
  , Escalation.ev 20 (.dispatch "c6" 1 "d6" none [] "k6")
  , Escalation.ev 21 (.result "c6" .declined none false) ]

def totalPolicy : Policy := Escalation.escPolicy .session (some 3)

#guard decide totalPolicy.WF
#guard (trace totalPolicy (State.initial "pd") alternating).all (·.2.2.accepted)
#guard [4, 5, 8, 11, 14, 17, 18, 21].map (fun n => counts (after totalPolicy "pd" (alternating.take n)))
  == [(0, 0, 0, false), (1, 1, 0, false), (1, 0, 0, false), (2, 1, 0, false), (2, 0, 0, false),
    (3, 1, 1, true), (0, 0, 1, false), (0, 0, 1, false)]

end Reports

namespace Reports

/-- Every session-scope entry carries the session's own id. -/
def SmOwn (s : State) : Prop := ∀ en ∈ s.sessionMeters, en.session = s.sessionId

/-- `SmOwn`, and no session-scope entry before `session_start` sets the id. -/
def SmInv (s : State) : Prop := SmOwn s ∧ (s.started = false → s.sessionMeters = [])

theorem SmInv.of (h : SmInv s) (hsm : s'.sessionMeters = s.sessionMeters)
    (hsid : s'.sessionId = s.sessionId) (hst : s'.started = s.started) : SmInv s' :=
  ⟨fun en hen => by rw [hsid]; exact h.1 en (hsm ▸ hen),
   fun hf => by rw [hsm]; exact h.2 (hst ▸ hf)⟩

theorem SmOwn.of (h : SmOwn s) (hsm : s'.sessionMeters = s.sessionMeters)
    (hsid : s'.sessionId = s.sessionId) : SmOwn s' :=
  fun en hen => by rw [hsid]; exact h en (hsm ▸ hen)

theorem updateEntries_smOwn {f : List MeterEntry → List MeterEntry}
    (hf : ∀ l : List MeterEntry, (∀ en ∈ l, en.session = s.sessionId) →
      ∀ en ∈ f l, en.session = s.sessionId) (h : SmOwn s) :
    SmOwn (s.updateEntries p m t f) := by
  unfold SmOwn State.updateEntries
  split
  · exact h
  · dsimp only
    intro en hen
    split at hen
    · exact h en hen
    · unfold Policy.prune at hen
      exact hf _ h en (List.mem_filter.mp hen).1

theorem reserve_smOwn {a : Nat} (h : SmOwn s) : SmOwn (s.reserve p m k a t) :=
  updateEntries_smOwn (fun _ hl en hen => by
    rcases List.mem_append.mp hen with hen | hen
    · exact hl en hen
    · rw [List.mem_singleton.mp hen]) h

theorem retime_smOwn (h : SmOwn s) : SmOwn (s.retime p m k t) :=
  updateEntries_smOwn (fun _ hl en hen => by
    obtain ⟨en', hen', rfl⟩ := List.mem_map.mp hen
    split <;> exact hl en' hen') h

theorem commit_smOwn {a : Nat} (h : SmOwn s) : SmOwn (s.commit p m k a t) :=
  updateEntries_smOwn (fun _ hl en hen => by
    obtain ⟨en', hen', rfl⟩ := List.mem_map.mp hen
    repeat' split
    all_goals exact hl en' hen') h

theorem release_smOwn (h : SmOwn s) : SmOwn (s.release p m k t) :=
  updateEntries_smOwn (fun _ hl en hen => hl en (List.mem_filter.mp hen).1) h

theorem claim_smOwn {rc : CallRec} {retry : Bool} {key : String} (h : SmOwn s) :
    SmOwn (claim p s t k rc r retry key) := by
  unfold claim
  dsimp only
  refine SmOwn.of (s := if retry then _ else _) ?_ rfl rfl
  split
  · exact foldl_invariant SmOwn (fun _ _ hb => retime_smOwn hb) _ s h
  · exact foldl_invariant SmOwn (fun _ _ hb => reserve_smOwn hb) _ _
      (h.of consumeGrant_same.sm consumeGrant_same.sid)

theorem settle_smOwn (h : SmOwn s) : SmOwn (s.settle p ms k o act ne t).1 := by
  rw [settle_eq]
  refine foldl_invariant (fun b : State × List String => SmOwn b.1) ?_ ms _ h
  intro ⟨acc, over⟩ m hb
  unfold settleStep
  dsimp only at hb ⊢
  split
  · exact release_smOwn hb
  · split
    · exact commit_smOwn hb
    · exact commit_smOwn hb

theorem smInv_step (hr : Reachable p d s) (h : SmInv s) : SmInv (step p s e).1 := by
  cases ha : (step p s e).2.accepted
  · rw [frame ha]; exact h
  have henv := envelope_iff.mp (accepted_open ha)
  have hstep := accepted_step ha
  cases hs : s.started
  · have hstart : e.body.isStart = true := by
      rcases henv.1 with h' | h'
      · rw [hs] at h'; cases h'
      · exact h'
    have hsm := h.2 hs
    rw [hstep]
    refine SmInv.of (s := (stepHandle p s e).1) ?_ rfl rfl rfl
    unfold stepHandle
    cases hb : e.body
    all_goals (rw [hb] at hstart; try cases hstart)
    dsimp only
    unfold handleSessionStart
    split
    · exact h
    · split
      · exact h
      · exact ⟨fun en hen => by simp [hsm] at hen, fun _ => hsm⟩
  cases hcl : (step p s e).2.claimed
  · have hcl' : (stepHandle p s e).2.claimed = false := by rw [hstep] at hcl; exact hcl
    rw [hstep]
    refine SmInv.of (s := (stepHandle p s e).1) ?_ rfl rfl rfl
    rcases stepHandle_kind hcl' with
      hp | ⟨k, c, c', o, act, ne, -, -, -, -, -, -, hsame⟩ | ⟨l, hb, he⟩ |
        ⟨i, pd, r, ps, as, l, hb, he⟩
    · exact h.of hp.sm hp.sid hp.started
    · refine ⟨SmOwn.of (settle_smOwn (h.1.of (s' := { s with calls := s.calls.insert k c' }) rfl
        rfl)) hsame.sm hsame.sid, fun hf => ?_⟩
      rw [hsame.started, settle_started] at hf
      rw [hs] at hf
      cases hf
    · rw [he]
      unfold handleLedgerSync
      dsimp only
      split
      · exact h
      · have hp : Plain s (if (l.tombstone && !s.ledger.tombstone) = true then cancelPending s
            else s) := by
          split
          · exact cancelPending_plain
          · exact Plain.refl
        exact h.of hp.sm hp.sid hp.started
    · exact absurd ⟨hs, by rw [hb]; rfl⟩ henv.2.2.1
  · obtain ⟨k, n, dg, cost, g, key, he⟩ := claimed_dispatch hr hcl
    obtain ⟨-, c, hc, -⟩ := (dispatch_claimed_iff he).mp hcl
    rw [claim_post hcl he hc]
    refine ⟨SmOwn.of (claim_smOwn (key := key) h.1) rfl rfl, fun hf => ?_⟩
    dsimp only at hf
    rw [claim_started, hs] at hf
    cases hf

theorem smInv_reachable (hr : Reachable p d s) : SmInv s := by
  induction hr with
  | init => exact ⟨fun en hen => by simp [State.initial] at hen, fun _ => rfl⟩
  | step hr ih => exact smInv_step hr ih

end Reports

open Reports

/-- Section 8, theorem 8: at every reachable state every entry of the session-scope meter list
carries the session's own id, so the accounting invariant's own-entry restriction leaves none of
them out. -/
theorem session_entries_own (hr : Reachable p d s) :
    ∀ en ∈ s.sessionMeters, en.session = s.sessionId :=
  (smInv_reachable hr).1

/-- Section 8, theorem 8, the accounting invariant for every entry of a session-scope meter: at
every reachable state each entry of `m` is the only entry of its call on `m`, that call was
dispatched at least once and its action uses `m`, and the entry is uncommitted with no excess and
the call's draw while the call holds its reservation, and committed once it does not. -/
theorem accounting_session (hwf : p.WF) (hr : Reachable p d s) (hs : p.meter? m = some spec)
    (hsc : spec.scope = .session) (hen : en ∈ entriesOf p s m) (hm : en.meter = m) :
    en.session = s.sessionId ∧ ownEntries p s m en.call = [en] ∧
      ∃ c r, s.calls[en.call]? = some c ∧ 1 ≤ c.attempts ∧ p.action? c.tool = some r ∧
        m ∈ r.meters ∧
        (Holds c → en.committed = false ∧ en.excess = 0 ∧ en.amount = draw spec c.cost) ∧
        (¬Holds c → en.committed = true) := by
  have hsm : entriesOf p s m = s.sessionMeters := by simp [entriesOf, hs, hsc]
  have hsid : en.session = s.sessionId := session_entries_own hr en (hsm ▸ hen)
  have hacc := accounting_reachable hwf hr
  have hown : en ∈ ownEntries p s m en.call :=
    List.mem_filter.mpr ⟨hen, by simp [hm, hsid]⟩
  have h1 : ownEntries p s m en.call = [en] := one_of (hacc.unique m en.call) hown
  obtain ⟨c, r, hc, ha, hra, hmr⟩ := hacc.owner m en hen hm hsid
  refine ⟨hsid, h1, c, r, hc, ha, hra, hmr, fun hh => ?_,
    fun hh => hacc.settled en.call c m en hc hown hh⟩
  obtain ⟨en', hen', hu, hx, hamt⟩ := hacc.held en.call c r m spec hc hra hmr hs ha hh
  rw [h1] at hen'
  cases hen'
  exact ⟨hu, hx, hamt⟩

/-- Section 8, theorem 8: on a calls meter, an accepted `result` or `reconcile` that does not
release commits exactly the reservation, 1, whatever cost it reports: the call's single
uncommitted entry on that meter becomes one committed entry of amount 1 with no excess and the
reservation's time, or pruning drops it at once because that time is outside the window. -/
theorem report_commits_calls (hwf : p.WF) (hr : Reachable p d s)
    (ha : (step p s e).2.accepted = true)
    (he : e.body = .result k o act false ∨ e.body = .reconcile k o act false)
    (ho : o ≠ .declined) (hc : s.calls[k]? = some c) (hra : p.action? c.tool = some r)
    (hmr : m ∈ r.meters) (hs : p.meter? m = some spec) (hu : spec.unit = .calls) :
    ∃ en, ownEntries p s m k = [en] ∧ en.committed = false ∧ en.amount = 1 ∧
      ((∃ en', ownEntries p (step p s e).1 m k = [en'] ∧ en'.committed = true ∧
          en'.amount = 1 ∧ en'.excess = 0 ∧ en'.time = en.time) ∨
        (ownEntries p (step p s e).1 m k = [] ∧ ∃ w, spec.windowMs = some w ∧
          en.time + w ≤ e.time)) := by
  obtain ⟨hent, -⟩ := report_settle hwf hr ha he ho hc hra
  obtain ⟨en, hen, hu', hx0, hamt, hy⟩ := hent m hmr spec hs
  have hmo : p.isMoney m = false := by simp [Policy.isMoney, hs, hu]
  have h1 : en.amount = 1 := by rw [hamt]; unfold draw; rw [hu]
  simp only [hmo, Bool.false_eq_true, ite_false, commitAs, Nat.lt_irrefl, ite_false] at hy
  refine ⟨en, hen, hu', h1, ?_⟩
  rcases hy with hy | ⟨hy, hp⟩
  · exact .inl ⟨_, hy, rfl, h1, hx0, rfl⟩
  · obtain ⟨-, spec', w, hs', hw, ht, -⟩ := hp
    rw [own_meter hen, hs] at hs'
    cases hs'
    exact .inr ⟨hy, w, hw, ht⟩

namespace Reports

def callsPolicy : Policy :=
  { meters := [("usd", Meters.usd), ("n", { unit := .calls, cap := some 5 })]
    actions := [("t", { Meters.capAction with meters := ["usd", "n"] })] }

def callsClaimed : State := after callsPolicy "pd" (Meters.capOpen ++ [Meters.firstClaim])

/-- Amount, excess, time and committed flag of call `c1`'s entries on the calls meter `n`. -/
def nEntries (x : State) : List (Nat × Nat × Nat × Bool) :=
  (ownEntries callsPolicy x "n" "c1").map fun en => (en.amount, en.excess, en.time, en.committed)

#guard decide callsPolicy.WF
#guard callsPolicy.meter? "n" == some { unit := .calls, cap := some 5 }
#guard (callsClaimed.calls["c1"]?).any (·.status == .dispatched)
#guard nEntries callsClaimed == [(1, 0, 5, false)]

-- `report_commits_calls`: an overrun of 90 and a partial capture of 0 both commit 1 on `n`.
#guard (step callsPolicy callsClaimed (reportOf .succeeded (some 90))).2
  == .ok (.overrun ["usd"]) none
#guard nEntries (step callsPolicy callsClaimed (reportOf .succeeded (some 90))).1
  == [(1, 0, 5, true)]
#guard nEntries (step callsPolicy callsClaimed (reportOf .succeeded (some 0))).1
  == [(1, 0, 5, true)]

-- `session_entries_own` and `accounting_session`: `usd` is session-scope, and its one entry
-- carries the session's id and is the only entry of its call on `usd`.
#guard Meters.usd.scope == .session
#guard sClaimed.sessionMeters.length == 1
#guard sClaimed.sessionMeters.all (·.session == sClaimed.sessionId)
#guard sClaimed.sessionMeters.all fun en =>
  (ownEntries Meters.capPolicy sClaimed "usd" en.call).length == 1

end Reports

end Writ.Proofs
