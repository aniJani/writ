import Writ.Profile.McpToolApproval
import WritProofs.Dispatch

namespace Writ.Proofs

open Writ
open Basic

variable {p : Policy} {s : State} {e : Event} {k : String} {c : CallRec}

theorem profile_no_retry (hp : Profile.McpToolApproval.errors p = []) (t : String) :
    ((p.action? t).getD {}).retryAfterUnknown = false := by
  cases ha : p.action? t with
  | none => rfl
  | some r =>
    obtain ⟨⟨name, r'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp ha
    have hmem := List.mem_of_find?_eq_some hf
    cases hr : r'.retryAfterUnknown with
    | false => exact hr
    | true =>
      have hin : Profile.McpToolApproval.Problem.retryAfterUnknown name ∈
          Profile.McpToolApproval.errors p := by
        simp only [Profile.McpToolApproval.errors, Profile.McpToolApproval.problems, List.mem_filter,
          List.mem_flatMap]
        exact ⟨⟨(name, r'), hmem, by simp [hr]⟩, rfl⟩
      rw [hp] at hin
      exact absurd hin List.not_mem_nil

/-- SEP-2848's "outcome-unknown is final": under a policy with no profile error (in particular one
whose profile problems are empty), from any state, no `dispatch` of a call whose status is Unknown
is accepted. -/
theorem profile_unknown_final (hp : Profile.McpToolApproval.errors p = [])
    (hc : s.calls[k]? = some c) (hu : c.status = .unknown) (hd : e.body.dispatchOf k = true) :
    (step p s e).2.accepted = false := by
  cases hb : e.body with
  | dispatch k' n dg cost g key =>
    have hk : k' = k := by rw [hb] at hd; simpa [EventBody.dispatchOf] using hd
    subst hk
    cases ha : (step p s e).2.accepted with
    | false => rfl
    | true =>
      obtain ⟨-, c', hc', hpr, -⟩ := (dispatch_accepted_iff hb).mp ha
      rw [hc, Option.some.injEq] at hc'
      subst hc'
      have := (hpr.2.1 hu).2.1
      rw [profile_no_retry hp] at this
      exact absurd this Bool.false_ne_true
  | _ => rw [hb] at hd; simp [EventBody.dispatchOf] at hd

end Writ.Proofs
