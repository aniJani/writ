import Writ.Core.Policy
import Writ.Json.Value

namespace Writ

inductive Warning where
  | lethalTrifecta (readsPrivate ingestsUntrusted sendsExternal : String)
  | noApprovalTtl
  | zeroTtl (action : String)
  | costThresholdUnmetered (action : String)
  | retriesExceedFailureLimit (action : String)
  | costThresholdWithoutConsent (action : String)
  | messagesNotApplied (action : String)
  | meterWithoutCap (meter : String)
  | principalMeterWithoutWindow (meter : String)
  | perCallAboveCap (meter : String)
  | retryWithoutAttempts (action : String)
  deriving DecidableEq, Repr

private def Requirements.canNeedApproval (r : Requirements) : Bool :=
  !r.consent.clauses.isEmpty || !r.escalate.isEmpty

private def flagged (p : Policy) (f : Flag) (ok : Requirements → Bool := fun _ => true) :
    Option String :=
  (p.actions.find? fun (_, r) => f ∈ r.flags && ok r).map (·.1)

private def unguardedSend (r : Requirements) : Bool :=
  r.consent.clauses.isEmpty || (r.grantable.map (·.anyArgs)).getD false

private def meterWarnings (name : String) (m : MeterSpec) : List Warning :=
  match m.cap with
  | none => [Warning.meterWithoutCap name]
  | some cap =>
    (if m.scope = .principal && m.windowMs.isNone then [Warning.principalMeterWithoutWindow name] else []) ++
    (match m.maxPerCall with
      | some n => if n > cap then [Warning.perCallAboveCap name] else []
      | none => [])

private def actionWarnings (p : Policy) (name : String) (r : Requirements) : List Warning :=
  (if r.approvalTtlMs = some 0 || r.authorizedTtlMs = some 0 then [Warning.zeroTtl name] else []) ++
  (if r.consentIfCostOver.isSome && !r.meters.any fun m =>
      match (p.meter? m).map (·.unit) with
      | some (MeterUnit.money _) => true
      | _ => false
    then [Warning.costThresholdUnmetered name] else []) ++
  (if r.consentIfCostOver.isSome && r.consent == Consent.none
    then [Warning.costThresholdWithoutConsent name] else []) ++
  (match p.limits.maxConsecutiveFailures with
    | some n =>
      if r.retryAfterUnknown && r.maxAttempts > n && p.limits.escalationScope = .session
      then [Warning.retriesExceedFailureLimit name] else []
    | none => []) ++
  (if r.retryAfterUnknown && r.maxAttempts = 1 then [Warning.retryWithoutAttempts name] else [])

def Policy.warnings (p : Policy) : List Warning :=
  (match flagged p .readsPrivate, flagged p .ingestsUntrusted, flagged p .sendsExternal unguardedSend with
    | some a, some b, some c => [Warning.lethalTrifecta a b c]
    | _, _, _ => []) ++
  (if p.limits.approvalTtlMs.isNone &&
      p.actions.any fun (_, r) => r.canNeedApproval && r.approvalTtlMs.isNone
    then [Warning.noApprovalTtl] else []) ++
  p.meters.flatMap (fun (name, m) => meterWarnings name m) ++
  p.actions.flatMap fun (name, r) => actionWarnings p name r

/-- Messages are validated by the decoder but not stored, so this reads the document. -/
def messageWarnings : Json → List Warning
  | .obj top =>
    match top.find? (·.1 == "actions") with
    | some (_, .obj acts) =>
      acts.toList.filterMap fun
        | (name, .obj kvs) => if kvs.any (·.1 == "messages") then some (.messagesNotApplied name) else none
        | _ => none
    | _ => []
  | _ => []

def Warning.code : Warning → String
  | .lethalTrifecta .. => "lethal_trifecta"
  | .noApprovalTtl => "no_approval_ttl"
  | .zeroTtl _ => "zero_ttl"
  | .costThresholdUnmetered _ => "cost_threshold_unmetered"
  | .retriesExceedFailureLimit _ => "retries_exceed_failure_limit"
  | .costThresholdWithoutConsent _ => "cost_threshold_without_consent"
  | .messagesNotApplied _ => "messages_not_applied"
  | .meterWithoutCap _ => "meter_without_cap"
  | .principalMeterWithoutWindow _ => "principal_meter_without_window"
  | .perCallAboveCap _ => "per_call_above_cap"
  | .retryWithoutAttempts _ => "retry_without_attempts"

def Warning.action? : Warning → Option String
  | .lethalTrifecta .. | .noApprovalTtl
  | .meterWithoutCap _ | .principalMeterWithoutWindow _ | .perCallAboveCap _ => none
  | .zeroTtl a | .costThresholdUnmetered a | .retriesExceedFailureLimit a
  | .costThresholdWithoutConsent a | .messagesNotApplied a | .retryWithoutAttempts a => some a

def Warning.message : Warning → String
  | .lethalTrifecta r i s =>
    s!"this policy combines private data (\"{r}\"), untrusted input (\"{i}\") and an unguarded way to send data out (\"{s}\")"
  | .noApprovalTtl => "some actions can need approval but no approval_ttl_ms is set, so requests never expire"
  | .zeroTtl _ => "a TTL of 0 expires the call at once"
  | .costThresholdUnmetered _ => "consent_if_cost_over is set but the action has no money meter, so no cost is ever checked"
  | .retriesExceedFailureLimit _ =>
    "max_attempts is above max_consecutive_failures, so failures can escalate the session before retries finish"
  | .costThresholdWithoutConsent _ =>
    "consent_if_cost_over is set but the action's consent is none, so it has no effect"
  | .messagesNotApplied _ => "messages are checked but not applied in 0.1; the binding applies them"
  | .meterWithoutCap m => s!"meter \"{m}\" has no cap, so it records usage but never denies a call"
  | .principalMeterWithoutWindow m =>
    s!"principal meter \"{m}\" has no window_ms, so its cap is a lifetime limit for each principal"
  | .perCallAboveCap m =>
    s!"meter \"{m}\" has max_per_call above its cap, so the cap denies calls the per-call limit allows"
  | .retryWithoutAttempts _ =>
    "retry_after_unknown is set but max_attempts is 1, so an unknown call can never be retried"

end Writ
