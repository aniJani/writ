import Writ.Codec.Common
import Writ.Core.Reason

namespace Writ

open Decoder Encode

instance : FromJson Clause where
  fromJson j := do
    let fs ← object ["quorum", "roles", "human_only", "exclude_requester"] j
    pure ⟨← req fs "quorum" nat, ← opt fs "roles" strings,
      ← dflt fs "human_only" true bool, ← dflt fs "exclude_requester" false bool⟩

instance : ToJson Clause where
  toJson c := obj [
    some ("quorum", nat c.k),
    some' "roles" c.roles strings,
    when (!c.humanOnly) "human_only" (.bool false),
    when c.excludeRequester "exclude_requester" (.bool true)]

instance : FromJson Group where
  fromJson j := do
    let fs ← object ["all", "distinct"] j
    pure ⟨← req fs "all" (array (FromJson.fromJson (α := Clause))), ← dflt fs "distinct" false bool⟩

def groupJson (g : Group) : Json :=
  obj [some ("all", .arr (g.clauses.map toJson).toArray), when g.distinct "distinct" (.bool true)]

instance : FromJson Consent where
  fromJson
    | .str "none" => pure Consent.none
    | .str "per_call" => pure Consent.perCall
    | .str _ => fail "unknown value, expected \"none\", \"per_call\" or an object"
    | j@(.obj kvs) =>
      if kvs.any (·.1 == "groups") then do
        let fs ← object ["groups"] j
        pure ⟨← req fs "groups" (array (FromJson.fromJson (α := Group)))⟩
      else if kvs.any (·.1 == "all") then do
        pure ⟨[← FromJson.fromJson j]⟩
      else do
        pure ⟨[⟨[← FromJson.fromJson j], false⟩]⟩
    | _ => fail "expected \"none\", \"per_call\" or an object"

instance : ToJson Consent where
  toJson
    | ⟨[]⟩ => .str "none"
    | c@⟨[⟨[k], false⟩]⟩ => if c == Consent.perCall then .str "per_call" else toJson k
    | ⟨[g]⟩ => groupJson g
    | ⟨gs⟩ => obj [some ("groups", .arr (gs.map groupJson).toArray)]

instance : FromJson Escalator where
  fromJson j := do
    let fs ← object ["consent", "grantable"] j
    pure ⟨← req fs "consent" FromJson.fromJson, ← dflt fs "grantable" false bool⟩

instance : ToJson Escalator where
  toJson e := obj [some ("consent", toJson e.consent),
    when e.grantable "grantable" (.bool true)]

instance : FromJson Grantable where
  fromJson j := do
    let fs ← object ["scope", "max_uses", "max_duration_ms", "any_args", "allow_any_args_metered"] j
    pure ⟨← req fs "scope" FromJson.fromJson, ← req fs "max_uses" nat, ← opt fs "max_duration_ms" nat,
      ← dflt fs "any_args" false bool, ← dflt fs "allow_any_args_metered" false bool⟩

instance : ToJson Grantable where
  toJson g := obj [
    some ("scope", toJson g.scope), some ("max_uses", nat g.maxUses),
    some' "max_duration_ms" g.maxDurationMs nat,
    when g.anyArgs "any_args" (.bool true),
    when g.allowAnyArgsMetered "allow_any_args_metered" (.bool true)]

def objectOrFail : Json → Decoder Unit
  | .obj _ => pure ()
  | _ => fail "expected an object"

def messagesShape : Json → Decoder Unit
  | .obj kvs => kvs.forM fun (code, v) => at' code do
    unless (Reason.ofCode? code).isSome do fail "unknown reason code"
    let fs ← object ["model", "user"] v
    let _ ← opt fs "model" string
    let _ ← opt fs "user" string
  | _ => fail "expected an object"

def maxSourceStringBytes : Nat := 512

def isToolDigest (s : String) : Bool :=
  s.startsWith "sha256:" && s.length == 71 &&
    (s.toList.drop 7).all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def sourceString (j : Json) : Decoder Unit := do
  let s ← string j
  if s.utf8ByteSize > maxSourceStringBytes then fail s!"longer than {maxSourceStringBytes} bytes"

def sourceShape (j : Json) : Decoder Unit := do
  let fs ← object ["tool_digest", "server", "tool", "annotations"] j
  req fs "tool_digest" fun
    | .str d => unless isToolDigest d do fail "expected \"sha256:\" followed by 64 lowercase hex digits"
    | _ => fail "expected a string"
  let _ ← opt fs "server" sourceString
  let _ ← opt fs "tool" sourceString
  let _ ← opt fs "annotations" objectOrFail

def requirementFields : List String :=
  ["permission", "consent", "consent_if_cost_over", "escalate", "grantable", "idempotent",
    "retry_after_unknown", "max_attempts", "guards", "meters", "approval_ttl_ms",
    "authorized_ttl_ms", "exposed", "mode", "flags", "review", "messages", "source"]

instance : FromJson Requirements where
  fromJson j := do
    let fs ← object requirementFields j
    let _ ← opt fs "review" objectOrFail
    let _ ← opt fs "messages" messagesShape
    let _ ← opt fs "source" sourceShape
    let permission ← match fs.find? (·.1 == "permission") with
      | some (_, .null) => pure none
      | _ => opt fs "permission" string
    pure {
      permission
      consent := ← dflt fs "consent" Consent.none FromJson.fromJson
      consentIfCostOver := ← opt fs "consent_if_cost_over" FromJson.fromJson
      escalate := ← dflt fs "escalate" [] (map FromJson.fromJson)
      grantable := ← opt fs "grantable" FromJson.fromJson
      idempotent := ← dflt fs "idempotent" false bool
      retryAfterUnknown := ← dflt fs "retry_after_unknown" false bool
      maxAttempts := ← dflt fs "max_attempts" 1 nat
      guards := ← dflt fs "guards" [] strings
      meters := ← dflt fs "meters" [] strings
      approvalTtlMs := ← opt fs "approval_ttl_ms" nat
      authorizedTtlMs := ← opt fs "authorized_ttl_ms" nat
      exposed := ← dflt fs "exposed" true bool
      mode := ← opt fs "mode" FromJson.fromJson
      flags := ← dflt fs "flags" [] (array FromJson.fromJson) }

instance : ToJson Requirements where
  toJson r := obj [
    some' "permission" r.permission .str,
    when (r.consent != Consent.none) "consent" (toJson r.consent),
    some' "consent_if_cost_over" r.consentIfCostOver toJson,
    when (!r.escalate.isEmpty) "escalate" (encodeMap toJson r.escalate),
    some' "grantable" r.grantable toJson,
    when r.idempotent "idempotent" (.bool true),
    when r.retryAfterUnknown "retry_after_unknown" (.bool true),
    when (r.maxAttempts != 1) "max_attempts" (nat r.maxAttempts),
    when (!r.guards.isEmpty) "guards" (strings r.guards),
    when (!r.meters.isEmpty) "meters" (strings r.meters),
    some' "approval_ttl_ms" r.approvalTtlMs nat,
    some' "authorized_ttl_ms" r.authorizedTtlMs nat,
    when (!r.exposed) "exposed" (.bool false),
    some' "mode" r.mode toJson,
    when (!r.flags.isEmpty) "flags" (.arr (r.flags.map toJson).toArray)]

instance : FromJson MeterSpec where
  fromJson j := do
    let fs ← object ["currency", "unit", "cap", "scope", "window_ms", "max_per_call"] j
    let unit ← match fs.any (·.1 == "currency"), fs.any (·.1 == "unit") with
      | true, true => fail "give either currency or unit, not both"
      | false, false => fail "give either currency or unit"
      | true, false => MeterUnit.money <$> req fs "currency" string
      | false, true => do
        let u ← req fs "unit" string
        if u == "calls" then pure MeterUnit.calls
        else at' "unit" (fail s!"unknown value \"{u}\", expected one of calls")
    pure ⟨unit, ← opt fs "cap" nat, ← dflt fs "scope" .session FromJson.fromJson,
      ← opt fs "window_ms" nat, ← opt fs "max_per_call" nat⟩

instance : ToJson MeterSpec where
  toJson m := obj [
    match m.unit with
    | .money c => some ("currency", .str c)
    | .calls => some ("unit", .str "calls"),
    some' "cap" m.cap nat,
    when (m.scope != .session) "scope" (toJson m.scope),
    some' "window_ms" m.windowMs nat,
    some' "max_per_call" m.maxPerCall nat]

instance : FromJson Limits where
  fromJson j := do
    let fs ← object ["max_steps_per_turn", "max_proposals_per_turn", "max_approval_requests_per_turn",
      "max_proposals_per_session", "max_approval_requests_per_session", "max_consecutive_failures",
      "max_failures_per_session", "escalation_scope", "approval_ttl_ms", "authorized_ttl_ms"] j
    pure {
      maxStepsPerTurn := ← opt fs "max_steps_per_turn" nat
      maxProposalsPerTurn := ← opt fs "max_proposals_per_turn" nat
      maxApprovalRequestsPerTurn := ← opt fs "max_approval_requests_per_turn" nat
      maxProposalsPerSession := ← opt fs "max_proposals_per_session" nat
      maxApprovalRequestsPerSession := ← opt fs "max_approval_requests_per_session" nat
      maxConsecutiveFailures := ← opt fs "max_consecutive_failures" nat
      maxFailuresPerSession := ← opt fs "max_failures_per_session" nat
      escalationScope := ← dflt fs "escalation_scope" .session FromJson.fromJson
      approvalTtlMs := ← opt fs "approval_ttl_ms" nat
      authorizedTtlMs := ← opt fs "authorized_ttl_ms" nat }

instance : ToJson Limits where
  toJson l := obj [
    some' "max_steps_per_turn" l.maxStepsPerTurn nat,
    some' "max_proposals_per_turn" l.maxProposalsPerTurn nat,
    some' "max_approval_requests_per_turn" l.maxApprovalRequestsPerTurn nat,
    some' "max_proposals_per_session" l.maxProposalsPerSession nat,
    some' "max_approval_requests_per_session" l.maxApprovalRequestsPerSession nat,
    some' "max_consecutive_failures" l.maxConsecutiveFailures nat,
    some' "max_failures_per_session" l.maxFailuresPerSession nat,
    when (l.escalationScope != .session) "escalation_scope" (toJson l.escalationScope),
    some' "approval_ttl_ms" l.approvalTtlMs nat,
    some' "authorized_ttl_ms" l.authorizedTtlMs nat]

def policyVersion : String := "0.1"

instance : FromJson Policy where
  fromJson j := do
    let fs ← object ["writ", "$schema", "mode", "approver_roles", "escalation_roles", "meters",
      "limits", "actions", "binding", "kill_scope"] j
    let v ← req fs "writ" string
    unless v == policyVersion do
      at' "writ" (fail s!"unsupported version \"{v}\", expected \"{policyVersion}\"")
    let _ ← opt fs "$schema" string
    let binding ← dflt fs "binding" true (decodeEnum [true, false] fun b => if b then "mutable" else "immutable")
    let kill ← dflt fs "kill_scope" false (decodeEnum [false, true] fun b => if b then "principal" else "session")
    pure {
      mode := ← dflt fs "mode" .enforce FromJson.fromJson
      approverRoles := ← dflt fs "approver_roles" [] strings
      escalationRoles := ← opt fs "escalation_roles" strings
      meters := ← dflt fs "meters" [] (map FromJson.fromJson)
      limits := ← dflt fs "limits" {} FromJson.fromJson
      actions := ← dflt fs "actions" [] (map FromJson.fromJson)
      bindingMutable := binding
      killSetsTombstone := kill }

instance : ToJson Policy where
  toJson p := obj [
    some ("writ", .str policyVersion),
    when (p.mode != .enforce) "mode" (toJson p.mode),
    when (!p.approverRoles.isEmpty) "approver_roles" (strings p.approverRoles),
    some' "escalation_roles" p.escalationRoles strings,
    when (!p.meters.isEmpty) "meters" (encodeMap toJson p.meters),
    when (p.limits != {}) "limits" (toJson p.limits),
    when (!p.actions.isEmpty) "actions" (encodeMap toJson p.actions),
    when (!p.bindingMutable) "binding" (.str "immutable"),
    when p.killSetsTombstone "kill_scope" (.str "principal")]

def Policy.parseDoc (text : String) : Except String (Policy × Json) := do
  let j ← Json.parse text
  match (decode j : Except DecodeError Policy) with
  | .ok p => pure (p, j)
  | .error e => throw e.render

end Writ
