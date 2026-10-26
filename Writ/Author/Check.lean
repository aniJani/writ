import Writ.Core.Consent

namespace Writ

inductive Problem where
  | duplicateAction (name : String) | duplicateMeter (name : String)
  | unknownMeter (action meter : String) | zeroQuorum (action : String)
  | unknownRole (action role : String) | noApproverRoles (action : String)
  | emptyRoles (action : String) | grantableNeedsSingleApproval (action : String)
  | grantableWithoutConsent (action : String)
  | grantableEscalatorWithoutGrantable (action escalator : String)
  | anyArgsNeedsDuration (action : String) | anyArgsMetered (action : String)
  | zeroMaxUses (action : String) | retryNeedsIdempotent (action : String)
  | zeroMaxAttempts (action : String) | zeroFailureLimit | zeroSessionFailureLimit
  | unknownEscalationRole (role : String) | unexposedLogOnly (action : String)
  | zeroWindow (meter : String) | mixedCurrencies (action : String)
  | perCallOnCallsMeter (meter : String) | duplicateMeterInAction (action meter : String)
  | duplicateEscalator (action escalator : String)
  | emptyConsentGroup (action : String)
  deriving DecidableEq, Repr

private def clauseProblems (p : Policy) (name : String) (cl : Clause) : List Problem :=
  (if cl.k = 0 then [Problem.zeroQuorum name] else []) ++
  ((cl.roles.getD []).filter (· ∉ p.approverRoles)).map (Problem.unknownRole name) ++
  (if cl.roles = some [] then [Problem.emptyRoles name] else [])

private def actionProblems (p : Policy) (name : String) (r : Requirements) : List Problem :=
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
    if e ∈ (r.escalate.take i).map (·.1) then some (Problem.duplicateEscalator name e) else none) ++
  (if currencies.eraseDups.length > 1 then [Problem.mixedCurrencies name] else []) ++
  clauses.flatMap (clauseProblems p name) ++
  (if (r.consent.groups ++ r.escalate.flatMap (·.2.consent.groups)).any (·.clauses.isEmpty)
    then [Problem.emptyConsentGroup name] else []) ++
  (if !clauses.isEmpty && p.approverRoles.isEmpty then [Problem.noApproverRoles name] else []) ++
  (match r.grantable with
    | none => grantableEscalators.map (Problem.grantableEscalatorWithoutGrantable name ·.1)
    | some g =>
      (if !r.grantConsent.single then [Problem.grantableNeedsSingleApproval name] else []) ++
      (if r.consent.clauses.isEmpty && grantableEscalators.isEmpty
        then [Problem.grantableWithoutConsent name] else []) ++
      (if g.maxUses = 0 then [Problem.zeroMaxUses name] else []) ++
      (if g.anyArgs && g.maxDurationMs.isNone then [Problem.anyArgsNeedsDuration name] else []) ++
      (if g.anyArgs && !r.meters.isEmpty && !g.allowAnyArgsMetered
        then [Problem.anyArgsMetered name] else [])) ++
  (if r.retryAfterUnknown && !r.idempotent then [Problem.retryNeedsIdempotent name] else []) ++
  (if r.maxAttempts = 0 then [Problem.zeroMaxAttempts name] else []) ++
  (if !r.exposed && r.mode = some .logOnly then [Problem.unexposedLogOnly name] else [])

def Policy.check (p : Policy) : List Problem :=
  let names := p.actions.map (·.1)
  let perAction := p.actions.zipIdx.flatMap fun ((name, r), i) =>
    (if name ∈ names.take i then [Problem.duplicateAction name] else []) ++
    actionProblems p name r
  let meterNames := p.meters.map (·.1)
  let meterProblems := p.meters.zipIdx.flatMap fun ((name, spec), i) =>
    (if name ∈ meterNames.take i then [Problem.duplicateMeter name] else []) ++
    (if spec.windowMs = some 0 then [Problem.zeroWindow name] else []) ++
    (if spec.unit = .calls && spec.maxPerCall.isSome then [Problem.perCallOnCallsMeter name] else [])
  perAction ++ meterProblems ++
  (if p.limits.maxConsecutiveFailures = some 0 then [Problem.zeroFailureLimit] else []) ++
  (if p.limits.maxFailuresPerSession = some 0 then [Problem.zeroSessionFailureLimit] else []) ++
  ((p.escalationRoles.getD []).filter (· ∉ p.approverRoles)).map Problem.unknownEscalationRole

def Problem.code : Problem → String
  | .duplicateAction _ => "duplicate_action"
  | .duplicateMeter _ => "duplicate_meter"
  | .unknownMeter .. => "unknown_meter"
  | .zeroQuorum _ => "zero_quorum"
  | .unknownRole .. => "unknown_role"
  | .noApproverRoles _ => "no_approver_roles"
  | .emptyRoles _ => "empty_roles"
  | .grantableNeedsSingleApproval _ => "grantable_needs_single_approval"
  | .grantableWithoutConsent _ => "grantable_without_consent"
  | .grantableEscalatorWithoutGrantable .. => "grantable_escalator_without_grantable"
  | .anyArgsNeedsDuration _ => "any_args_needs_duration"
  | .anyArgsMetered _ => "any_args_metered"
  | .zeroMaxUses _ => "zero_max_uses"
  | .retryNeedsIdempotent _ => "retry_needs_idempotent"
  | .zeroMaxAttempts _ => "zero_max_attempts"
  | .zeroFailureLimit => "zero_failure_limit"
  | .zeroSessionFailureLimit => "zero_session_failure_limit"
  | .unknownEscalationRole _ => "unknown_escalation_role"
  | .unexposedLogOnly _ => "unexposed_log_only"
  | .zeroWindow _ => "zero_window"
  | .mixedCurrencies _ => "mixed_currencies"
  | .perCallOnCallsMeter _ => "per_call_on_calls_meter"
  | .duplicateMeterInAction .. => "duplicate_meter_in_action"
  | .duplicateEscalator .. => "duplicate_escalator"
  | .emptyConsentGroup _ => "empty_consent_group"

def Problem.action? : Problem → Option String
  | .duplicateAction n => some n
  | .unknownMeter a _ | .unknownRole a _ | .grantableEscalatorWithoutGrantable a _
  | .duplicateMeterInAction a _ | .duplicateEscalator a _ => some a
  | .zeroQuorum a | .noApproverRoles a | .emptyRoles a | .grantableNeedsSingleApproval a
  | .grantableWithoutConsent a | .anyArgsNeedsDuration a | .anyArgsMetered a | .zeroMaxUses a
  | .retryNeedsIdempotent a | .zeroMaxAttempts a | .unexposedLogOnly a | .mixedCurrencies a
  | .emptyConsentGroup a => some a
  | .duplicateMeter _ | .zeroFailureLimit | .zeroSessionFailureLimit | .unknownEscalationRole _
  | .zeroWindow _ | .perCallOnCallsMeter _ => none

def Problem.message : Problem → String
  | .duplicateAction _ => "the action is defined twice"
  | .duplicateMeter n => s!"meter \"{n}\" is defined twice"
  | .unknownMeter _ m => s!"it uses meter \"{m}\", which is not defined"
  | .zeroQuorum _ => "a consent clause has a quorum of 0"
  | .unknownRole _ r => s!"a consent clause names role \"{r}\", which is not an approver role"
  | .noApproverRoles _ => "it needs approval but the policy has no approver roles"
  | .emptyRoles _ => "a consent clause has an empty role list, so nobody can approve"
  | .grantableNeedsSingleApproval _ => "it is grantable but its consent needs more than one approval"
  | .grantableWithoutConsent _ => "it is grantable but needs no consent, so there is nothing to grant"
  | .grantableEscalatorWithoutGrantable _ e => s!"escalator \"{e}\" is grantable but the action has no grantable"
  | .anyArgsNeedsDuration _ => "a grantable with any_args needs max_duration_ms"
  | .anyArgsMetered _ => "a grantable with any_args on a metered action needs allow_any_args_metered"
  | .zeroMaxUses _ => "its grantable has max_uses of 0"
  | .retryNeedsIdempotent _ => "retry_after_unknown needs the action to be idempotent"
  | .zeroMaxAttempts _ => "max_attempts is 0"
  | .zeroFailureLimit => "max_consecutive_failures is 0"
  | .zeroSessionFailureLimit => "max_failures_per_session is 0"
  | .unknownEscalationRole r => s!"escalation role \"{r}\" is not an approver role"
  | .unexposedLogOnly _ => "it is not exposed, so log_only mode has no effect"
  | .zeroWindow m => s!"meter \"{m}\" has a window of 0"
  | .mixedCurrencies _ => "its money meters use different currencies"
  | .perCallOnCallsMeter m => s!"calls meter \"{m}\" has max_per_call, which only applies to money"
  | .duplicateMeterInAction _ m => s!"meter \"{m}\" is listed twice"
  | .duplicateEscalator _ e => s!"escalator \"{e}\" is defined twice"
  | .emptyConsentGroup _ => "a consent group has no clauses, so it allows everything"

def Policy.WF (p : Policy) : Prop := p.check = []

instance (p : Policy) : Decidable p.WF := inferInstanceAs (Decidable (p.check = []))

end Writ
