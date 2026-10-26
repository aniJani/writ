import Writ.Author.Check

namespace Writ.Proofs

open Writ

/-- Section 8, policy check soundness for degenerate limits: what `writ check` guarantees of a
policy it accepts, for every action `t` with requirements `r` and every meter `m`. -/
structure WFacts (p : Policy) : Prop where
  maxAttempts_pos : ∀ {t r}, p.action? t = some r → 1 ≤ r.maxAttempts
  meters_nodup : ∀ {t r}, p.action? t = some r → r.meters.Nodup
  meters_defined : ∀ {t r m}, p.action? t = some r → m ∈ r.meters → (p.meter? m).isSome
  window_pos : ∀ {m spec}, p.meter? m = some spec → spec.windowMs ≠ some 0
  perCall_money : ∀ {m spec}, p.meter? m = some spec → spec.maxPerCall.isSome →
    ∃ cur, spec.unit = .money cur
  failureLimit_pos : p.limits.maxConsecutiveFailures ≠ some 0
  sessionFailureLimit_pos : p.limits.maxFailuresPerSession ≠ some 0
  unexposed_not_logOnly : ∀ {t r}, p.action? t = some r → r.exposed = false →
    r.mode ≠ some .logOnly
  single_currency : ∀ {t r m₁ m₂ spec₁ spec₂ cur₁ cur₂}, p.action? t = some r →
    m₁ ∈ r.meters → m₂ ∈ r.meters → p.meter? m₁ = some spec₁ → p.meter? m₂ = some spec₂ →
    spec₁.unit = .money cur₁ → spec₂.unit = .money cur₂ → cur₁ = cur₂

variable {p : Policy} {t : String} {r : Requirements}

namespace WF

/-- The checks `writ check` makes of action `t`, spelled out because the kernel's
`actionProblems` is private; `cp` stands for its private clause checks. -/
private theorem action (h : p.WF) (hr : p.action? t = some r) :
    ∃ (name : String) (cp : List Problem),
    let clauses := r.consent.clauses ++ r.escalate.flatMap (·.2.consent.clauses)
    let grantableEscalators := r.escalate.filter (·.2.grantable)
    let currencies := r.meters.filterMap fun m => (p.meter? m).bind fun spec =>
      match spec.unit with
      | .money c => some c
      | .calls => none
    (r.meters.filter (p.meter? · |>.isNone)).map (Problem.unknownMeter name) ++
    (r.meters.zipIdx.filterMap fun (m, i) =>
      if m ∈ r.meters.take i then some (Problem.duplicateMeterInAction name m) else none) ++
    (r.escalate.zipIdx.filterMap fun ((e, _), i) =>
      if e ∈ (r.escalate.take i).map (·.1) then some (Problem.duplicateEscalator name e)
      else none) ++
    (if currencies.eraseDups.length > 1 then [Problem.mixedCurrencies name] else []) ++
    cp ++
    (if (r.consent.groups ++ r.escalate.flatMap (·.2.consent.groups)).any (·.clauses.isEmpty)
      then [Problem.emptyConsentGroup name] else []) ++
    (if !clauses.isEmpty && p.approverRoles.isEmpty then [Problem.noApproverRoles name]
      else []) ++
    (match r.grantable with
      | none => grantableEscalators.map (Problem.grantableEscalatorWithoutGrantable name ·.1)
      | some g =>
        (if !r.grantConsent.single then [Problem.grantableNeedsSingleApproval name] else []) ++
        (if r.consent.clauses.isEmpty && grantableEscalators.isEmpty
          then [Problem.grantableWithoutConsent name] else []) ++
        (if g.maxUses = 0 then [Problem.zeroMaxUses name] else []) ++
        (if g.anyArgs && g.maxDurationMs.isNone then [Problem.anyArgsNeedsDuration name]
          else []) ++
        (if g.anyArgs && !r.meters.isEmpty && !g.allowAnyArgsMetered
          then [Problem.anyArgsMetered name] else [])) ++
    (if r.retryAfterUnknown && !r.idempotent then [Problem.retryNeedsIdempotent name] else []) ++
    (if r.maxAttempts = 0 then [Problem.zeroMaxAttempts name] else []) ++
    (if !r.exposed && r.mode = some .logOnly then [Problem.unexposedLogOnly name] else []) =
      [] := by
  unfold Policy.action? at hr
  obtain ⟨⟨name, r'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hz : ((name, r'), i) ∈ p.actions.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  unfold Policy.WF Policy.check at h
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  exact ⟨name, _, (h.1.1.1.1 _ hz).2⟩

private theorem meter (h : p.WF) {m : String} {spec : MeterSpec} (hs : p.meter? m = some spec) :
    spec.windowMs ≠ some 0 ∧ (spec.unit = .calls → spec.maxPerCall.isSome = false) := by
  unfold Policy.meter? at hs
  obtain ⟨⟨name, spec'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hz : ((name, spec'), i) ∈ p.meters.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  unfold Policy.WF Policy.check at h
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  have hm := h.1.1.1.2 _ hz
  simp only [ite_eq_right_iff, List.cons_ne_nil, imp_false] at hm
  refine ⟨hm.1.2, fun hc => ?_⟩
  have := hm.2
  simp_all

private theorem nodup_of_take {l : List String}
    (h : ∀ x ∈ l.zipIdx, x.1 ∉ l.take x.2) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro a b ha hb hab heq
  have hza : (l[b], b) ∈ l.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hb)
  apply h _ hza
  rw [← heq]
  exact List.mem_iff_getElem.mpr ⟨a, by simp; omega, by simp⟩

private theorem eq_of_length_le_one {a b : String} :
    ∀ {l : List String}, l.length ≤ 1 → a ∈ l → b ∈ l → a = b
  | [_], _, h₁, h₂ => by simp_all
  | _ :: _ :: _, hn, _, _ => by simp at hn

end WF

theorem Policy.WF.facts (h : p.WF) : WFacts p where
  maxAttempts_pos hr := by
    obtain ⟨_, _, ha⟩ := WF.action h hr
    simp only [List.append_eq_nil_iff] at ha
    have hm := ha.1.2
    split at hm
    · cases hm
    · omega
  meters_nodup hr := by
    obtain ⟨_, _, ha⟩ := WF.action h hr
    simp only [List.append_eq_nil_iff, List.filterMap_eq_nil_iff] at ha
    refine WF.nodup_of_take fun x hx => ?_
    have hn := ha.1.1.1.1.1.1.1.1.1.2 x hx
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false] at hn
    exact hn
  meters_defined hr hm := by
    obtain ⟨_, _, ha⟩ := WF.action h hr
    simp only [List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at ha
    exact Option.ne_none_iff_isSome.mp (by simpa using ha.1.1.1.1.1.1.1.1.1.1 _ hm)
  window_pos hs := (WF.meter h hs).1
  perCall_money {_ spec} hs hx := by
    cases hu : spec.unit with
    | money cur => exact ⟨cur, rfl⟩
    | calls => simp [(WF.meter h hs).2 hu] at hx
  failureLimit_pos hz := by
    unfold Policy.WF Policy.check at h
    simp [hz] at h
  sessionFailureLimit_pos hz := by
    unfold Policy.WF Policy.check at h
    simp [hz] at h
  unexposed_not_logOnly hr hx hl := by
    obtain ⟨_, _, ha⟩ := WF.action h hr
    simp only [List.append_eq_nil_iff] at ha
    have hn := ha.2
    simp [hx, hl] at hn
  single_currency {_ r m₁ m₂ _ _ cur₁ cur₂} hr hm₁ hm₂ hs₁ hs₂ hu₁ hu₂ := by
    obtain ⟨_, _, ha⟩ := WF.action h hr
    simp only [List.append_eq_nil_iff] at ha
    have hn := ha.1.1.1.1.1.1.1.2
    simp only [ite_eq_right_iff, List.cons_ne_nil, imp_false, Nat.not_lt] at hn
    have hmem : ∀ m spec cur, m ∈ r.meters → p.meter? m = some spec → spec.unit = .money cur →
        cur ∈ (r.meters.filterMap fun m => (p.meter? m).bind fun spec =>
          match spec.unit with
          | .money c => some c
          | .calls => none).eraseDups := by
      intro m spec cur hm hs hu
      rw [List.mem_eraseDups, List.mem_filterMap]
      exact ⟨m, hm, by rw [hs]; simp [hu]⟩
    have h₁ := hmem _ _ _ hm₁ hs₁ hu₁
    have h₂ := hmem _ _ _ hm₂ hs₂ hu₂
    exact WF.eq_of_length_le_one hn h₁ h₂

end Writ.Proofs

-- An alias in the kernel type's namespace makes `h.facts` resolve for `h : p.WF` while the
-- theorem stays in `Writ.Proofs`.
namespace Writ.Policy.WF
export Writ.Proofs.Policy.WF (facts)
end Writ.Policy.WF

namespace Writ.Proofs

variable {p : Policy} {t : String} {r : Requirements} {m : String} {spec : MeterSpec}

theorem WF.maxAttempts_pos (h : p.WF) (hr : p.action? t = some r) : 1 ≤ r.maxAttempts :=
  h.facts.maxAttempts_pos hr

theorem WF.meters_nodup (h : p.WF) (hr : p.action? t = some r) : r.meters.Nodup :=
  h.facts.meters_nodup hr

theorem WF.window_pos (h : p.WF) (hs : p.meter? m = some spec) : spec.windowMs ≠ some 0 :=
  h.facts.window_pos hs

theorem WF.perCall_money (h : p.WF) (hs : p.meter? m = some spec) (hx : spec.maxPerCall.isSome) :
    ∃ cur, spec.unit = .money cur :=
  h.facts.perCall_money hs hx

theorem WF.failureLimit_pos (h : p.WF) : p.limits.maxConsecutiveFailures ≠ some 0 :=
  h.facts.failureLimit_pos

theorem WF.sessionFailureLimit_pos (h : p.WF) : p.limits.maxFailuresPerSession ≠ some 0 :=
  h.facts.sessionFailureLimit_pos

namespace WF

def usd (w : Option Nat := none) : MeterSpec := { unit := .money "USD", windowMs := w }

def checked : Policy :=
  { meters := [("a", usd (some 10)), ("b", usd), ("n", { unit := .calls })]
    limits := { maxConsecutiveFailures := some 1, maxFailuresPerSession := some 1 }
    actions := [("t", { meters := ["a", "b", "n"], exposed := false })] }

def withAction (r : Requirements) : Policy := { checked with actions := [("t", r)] }

#guard checked.check == []
#guard ({ checked with meters := [("a", usd (some 0)), ("b", usd), ("n", { unit := .calls })] } :
  Policy).check == [.zeroWindow "a"]
#guard ({ checked with limits.maxConsecutiveFailures := some 0 } : Policy).check
  == [.zeroFailureLimit]
#guard ({ checked with limits.maxFailuresPerSession := some 0 } : Policy).check
  == [.zeroSessionFailureLimit]
#guard (withAction { exposed := false, mode := some .logOnly }).check == [.unexposedLogOnly "t"]
#guard ({ checked with
  meters := [("a", usd), ("b", { unit := .money "EUR" }), ("n", { unit := .calls })] } :
  Policy).check == [.mixedCurrencies "t"]
#guard (withAction { maxAttempts := 0 }).check == [.zeroMaxAttempts "t"]
#guard (withAction { meters := ["a", "a"] }).check == [.duplicateMeterInAction "t" "a"]
#guard (withAction { meters := ["x"] }).check == [.unknownMeter "t" "x"]
#guard ({ checked with
  meters := [("a", usd), ("b", usd), ("n", { unit := .calls, maxPerCall := some 1 })] } :
  Policy).check == [.perCallOnCallsMeter "n"]

end WF

end Writ.Proofs
