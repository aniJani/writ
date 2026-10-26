import Writ
import WritTests.JsonHelpers
import WritTests.Fuzz.Gen

open Writ

namespace WritTests.Codec

def minimal : String := "{ \"writ\": \"0.1\", \"actions\": { \"send_email\": { \"consent\": \"per_call\" } } }"

def specExample : String := "{
  \"writ\": \"0.1\",
  \"mode\": \"enforce\",
  \"approver_roles\": [\"owner\", \"admin\"],
  \"meters\": {
    \"usd_day\": { \"currency\": \"USD\", \"cap\": 500000, \"scope\": \"principal\", \"window_ms\": 86400000, \"max_per_call\": 100000 },
    \"usd_month\": { \"currency\": \"USD\", \"cap\": 5000000, \"scope\": \"principal\", \"window_ms\": 2592000000 },
    \"tool_calls\": { \"unit\": \"calls\", \"cap\": 600, \"scope\": \"principal\", \"window_ms\": 3600000 }
  },
  \"limits\": {
    \"max_steps_per_turn\": 4,
    \"max_proposals_per_turn\": 12,
    \"max_approval_requests_per_turn\": 3,
    \"max_proposals_per_session\": 200,
    \"max_approval_requests_per_session\": 30,
    \"max_consecutive_failures\": 3,
    \"escalation_scope\": \"tool\",
    \"approval_ttl_ms\": 600000,
    \"authorized_ttl_ms\": 300000
  },
  \"escalation_roles\": [\"owner\"],
  \"actions\": {
    \"calendar.list\": { \"permission\": \"calendar.read\", \"consent\": \"none\" },
    \"calendar.create\": {
      \"permission\": \"calendar.write\",
      \"consent\": \"per_call\",
      \"grantable\": { \"scope\": \"session\", \"max_uses\": 20, \"max_duration_ms\": 3600000 },
      \"guards\": [\"calendar_connected\"]
    },
    \"shop.buy\": {
      \"permission\": \"payments\",
      \"consent\": { \"quorum\": 1, \"roles\": [\"owner\", \"admin\"], \"human_only\": true, \"exclude_requester\": true },
      \"meters\": [\"usd_day\", \"usd_month\"],
      \"escalate\": {
        \"over_limit\": { \"consent\": { \"all\": [
          { \"quorum\": 2, \"roles\": [\"finance\"], \"exclude_requester\": true },
          { \"quorum\": 1, \"roles\": [\"requester_manager\"] } ] } }
      },
      \"approval_ttl_ms\": 86400000
    },
    \"shell.run\": {
      \"consent\": \"none\",
      \"grantable\": { \"scope\": \"session\", \"max_uses\": 50, \"max_duration_ms\": 3600000 },
      \"escalate\": {
        \"not_allowlisted\": { \"consent\": \"per_call\", \"grantable\": true },
        \"dangerous\": { \"consent\": \"per_call\" }
      },
      \"meters\": [\"tool_calls\"]
    },
    \"http.post\": { \"consent\": \"per_call\", \"flags\": [\"sends_external\"] },
    \"files.delete_all\": { \"exposed\": false }
  }
}"

def decodeErr (text : String) : String :=
  match Json.parse text with
  | .error e => e
  | .ok j =>
    match (decode j : Except DecodeError Policy) with
    | .ok _ => ""
    | .error e => e.render

def amountDoc (amount : String) : String :=
  "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"consent_if_cost_over\":{\"amount\":" ++ amount ++ ",\"currency\":\"USD\"}}}}"

def amountOf (amount : String) : Except String (Option Nat) :=
  (Policy.parseDoc (amountDoc amount)).map fun (p, _) =>
    (p.action? "a").bind (·.consentIfCostOver) |>.map (·.amount)

#guard (Policy.parseDoc specExample).map (fun (p, _) => (p.action? "shop.buy").map (·.escalate.map (·.1))) == .ok (some ["over_limit"])
#guard (Policy.parseDoc specExample).map (fun (p, _) => (p.action? "shop.buy").bind (·.escalate.lookup "over_limit") |>.map (·.consent.clauses.length)) == .ok (some 2)
#guard (Policy.parseDoc minimal).map (·.1.actions.map (·.1)) == .ok ["send_email"]
#guard (Policy.parseDoc minimal).map (·.1.action? "send_email" |>.map (·.consent)) == .ok (some .perCall)
#guard decodeErr "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"consnet\":\"none\"}}}" == "actions.a.consnet: unknown field"
#guard decodeErr "{\"writ\":\"0.2\",\"actions\":{}}" == "writ: unsupported version \"0.2\", expected \"0.1\""
#guard decodeErr "{\"writ\":\"0.1\",\"meters\":{\"m\":{\"currency\":\"USD\",\"unit\":\"calls\"}}}" == "meters.m: give either currency or unit, not both"

#guard amountOf "\"0\"" == .ok (some 0)
#guard amountOf "\"1200\"" == .ok (some 1200)
#guard amountOf "\"340282366920938463463374607431768211456\"" == .ok (some 340282366920938463463374607431768211456)
#guard ["\"\"", "\"01\"", "\"+1\"", "\"-1\"", "\" 1\"", "\"1.0\"", "\"1e3\"", "1200", "\"١\"", "null"].all fun a =>
  (decodeErr (amountDoc a)).startsWith "actions.a.consent_if_cost_over.amount: "

#guard decodeErr "{\"writ\":\"0.1\",\"limits\":{\"max_steps_per_turn\":-1}}" == "limits.max_steps_per_turn: expected a non-negative integer"
#guard decodeErr "{\"writ\":\"0.1\",\"approver_roles\":[\"a\",1]}" == "approver_roles[1]: expected a string"
#guard decodeErr "{\"writ\":\"0.1\",\"mode\":\"loud\"}" == "mode: unknown value \"loud\", expected one of enforce, log_only"
#guard decodeErr "{\"actions\":{}}" == "writ: missing field"
#guard decodeErr "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"consent\":{\"quorum\":1,\"extra\":2}}}}" == "actions.a.consent.extra: unknown field"
#guard decodeErr "[]" == "expected an object"
#guard (decodeErr "{\"writ\":\"0.1\",\"$schema\":\"x\",\"actions\":{\"a\":{\"review\":{},\"messages\":{}}}}") == ""
def msgDoc (m : String) : String := "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"messages\":" ++ m ++ "}}}"
#guard decodeErr (msgDoc "{\"guard_false\":{\"model\":\"m\",\"user\":\"u\"},\"meter_exceeded\":{}}") == ""
#guard decodeErr (msgDoc "{\"guard_flase\":{}}") == "actions.a.messages.guard_flase: unknown reason code"
#guard decodeErr (msgDoc "{\"guard_false\":{\"model\":1}}") == "actions.a.messages.guard_false.model: expected a string"
#guard decodeErr (msgDoc "{\"guard_false\":{\"extra\":\"x\"}}") == "actions.a.messages.guard_false.extra: unknown field"
#guard decodeErr (msgDoc "{\"guard_false\":\"x\"}") == "actions.a.messages.guard_false: expected an object"
#guard decodeErr (msgDoc "[]") == "actions.a.messages: expected an object"
#guard ((Policy.parseDoc (msgDoc "{\"guard_false\":{}}")).map (·.1)) == .ok { actions := [("a", {})] }

def nines (n : Nat) : String := "\"" ++ String.ofList (List.replicate n '9') ++ "\""
#guard (amountOf (nines 78)).map (·.isSome) == .ok true
#guard decodeErr (amountDoc (nines 79)) == "actions.a.consent_if_cost_over.amount: amount has more than 78 digits"
#guard decodeErr (amountDoc (nines 200000)) == "actions.a.consent_if_cost_over.amount: amount has more than 78 digits"
#guard decodeErr "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"review\":1}}}" == "actions.a.review: expected an object"

def hex64 : String := String.ofList (List.replicate 64 'a')
def srcDoc (src : String) : String := "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"source\":" ++ src ++ "}}}"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64 ++ "\"}")) == ""
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64 ++ "\",\"server\":\"files\",\"tool\":\"files.read\"," ++
  "\"annotations\":{\"readOnlyHint\":true,\"riskLevel\":\"low\"}}")) == ""
#guard decodeErr (srcDoc "{\"server\":\"files\"}") == "actions.a.source.tool_digest: missing field"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64.toUpper ++ "\"}"))
  == "actions.a.source.tool_digest: expected \"sha256:\" followed by 64 lowercase hex digits"
#guard decodeErr (srcDoc "{\"tool_digest\":\"sha256:abc\"}")
  == "actions.a.source.tool_digest: expected \"sha256:\" followed by 64 lowercase hex digits"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha512:" ++ hex64 ++ "\"}"))
  == "actions.a.source.tool_digest: expected \"sha256:\" followed by 64 lowercase hex digits"
#guard decodeErr (srcDoc "{\"tool_digest\":7}") == "actions.a.source.tool_digest: expected a string"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64 ++ "\",\"digest\":\"x\"}"))
  == "actions.a.source.digest: unknown field"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64 ++ "\",\"annotations\":[]}"))
  == "actions.a.source.annotations: expected an object"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64 ++ "\",\"tool\":\"" ++
  String.ofList (List.replicate 257 'é') ++ "\"}")) == "actions.a.source.tool: longer than 512 bytes"
#guard decodeErr (srcDoc ("{\"tool_digest\":\"sha256:" ++ hex64 ++ "\",\"server\":\"" ++
  String.ofList (List.replicate 512 'a') ++ "\"}")) == ""
#guard decodeErr (srcDoc "\"sha256:x\"") == "actions.a.source: expected an object"

def consentErrs (c : String) : List Problem :=
  match Policy.parseDoc ("{\"writ\":\"0.1\",\"approver_roles\":[\"o\"],\"actions\":{\"a\":{\"consent\":" ++ c ++ "}}}") with
  | .ok (p, _) => p.check
  | .error _ => []
#guard consentErrs "{\"all\":[]}" == [.emptyConsentGroup "a"]
#guard consentErrs "{\"groups\":[{\"all\":[]}]}" == [.emptyConsentGroup "a"]
#guard consentErrs "{\"all\":[],\"distinct\":true}" == [.emptyConsentGroup "a"]
#guard consentErrs "{\"groups\":[]}" == []
#guard consentErrs "\"per_call\"" == []

def roundTrips (p : Policy) : Bool :=
  decode (toJson p) == (.ok p : Except DecodeError Policy) &&
    (Json.parse (toJson p).compact).bind (fun j => (decode j : Except DecodeError Policy).mapError (·.render)) == .ok p

#guard (List.range 300).all fun i => roundTrips (WritTests.Fuzz.genTrace i 0).policy
#guard (Policy.parseDoc specExample).toOption.all fun (p, _) => roundTrips p

#guard (toJson (Policy.mk .enforce [] none [] {} [("a", {})] true false)).compact == "{\"writ\":\"0.1\",\"actions\":{\"a\":{}}}"
#guard (toJson Consent.perCall).compact == "\"per_call\""
#guard (toJson (Consent.allOf [⟨2, some ["f"], true, true⟩, ⟨1, none, false, false⟩] true)).compact
  == "{\"all\":[{\"quorum\":2,\"roles\":[\"f\"],\"exclude_requester\":true},{\"quorum\":1,\"human_only\":false}],\"distinct\":true}"

#guard decodeErr "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"escalate\":{\"x\":{}}}}}" == "actions.a.escalate.x.consent: missing field"
#guard (toJson ({ consent := .none } : Escalator)).compact == "{\"consent\":\"none\"}"
#guard (Policy.parseDoc "{\"writ\":\"0.1\",\"actions\":{\"a\":{\"escalate\":{\"x\":{\"consent\":\"none\"}}}}}").toOption.all (roundTrips ·.1)

def rolesPolicy (r : Option (List String)) : Policy :=
  { approverRoles := ["o"], actions := [("a", { consent := .quorum 1 r true false })] }
#guard roundTrips (rolesPolicy (some [])) && roundTrips (rolesPolicy none)
#guard (toJson (rolesPolicy (some []))).compact.contains '[' && (toJson (rolesPolicy none)).compact != (toJson (rolesPolicy (some []))).compact

#guard (List.range 300).all fun i => (WritTests.Fuzz.genTrace i 0).policy.check.isEmpty

#guard (Policy.parseDoc minimal).map (·.2.digest) == .ok "sha256:f9ad0f2f39b7ae25b19d773a4bac2b95d92fd6dfaaf365b40b1d976e4c0842af"


def reasonsJson : String := include_str "../schema/reasons.json"

def reasonPairs : Json → Option (List (String × String))
  | .arr xs => xs.toList.mapM fun
    | .obj #[("code", .str c), ("retry", .str r)] => some (c, r)
    | _ => none
  | _ => none

#guard ((Json.parse reasonsJson).toOption.bind reasonPairs) == some (Reason.all.map fun r => (r.code, r.retry.code))
#guard Reason.all.all fun r => Reason.ofCode? r.code == some r
#guard (Reason.all.map Reason.code).eraseDups.length == 52
#guard Reason.ofCode? "nope" == none && Reason.ofCode? "stale_seq" == some .staleSeq
#guard (Reason.all.map Reason.retry).all fun c => [("fix_request", RetryClass.fixRequest), ("never", .never),
  ("after_user_action", .afterUserAction), ("next_turn", .nextTurn), ("after_escalation", .afterEscalation)].any
    fun (s, k) => c.code == s && k == c
#guard Reason.all.all fun r => r.modelMessage != "" && r.userMessage != "" &&
  ![r.modelMessage, r.userMessage].any fun m => m.contains '—' || m.contains '–'
#guard (Reason.all.map Reason.modelMessage).eraseDups.length == 52 && (Reason.all.map Reason.userMessage).eraseDups.length == 52
def hasWord (m w : String) : Bool := (m.toLower.splitOn w.toLower).length > 1
#guard Reason.all.all fun r => ["kernel", "epoch", "digest", "tally", "sorry", "apolog"].all fun w =>
  !hasWord r.userMessage w && !hasWord r.modelMessage w
#guard (Reason.previouslyRejected.modelMessage ==
  "The user rejected this exact call. Do not propose it again until the user sends a new message; ask the user what they want instead.")
  && Reason.previouslyRejected.userMessage == "You rejected this earlier in the conversation."
#guard (Reason.all.filter (·.retry == .never)).all fun r => hasWord r.modelMessage "do not"
def hostProtocol : List Reason := [.notStarted, .alreadyStarted, .staleSeq, .timeDecreasing,
  .stateVersionMismatch, .policyDigestMismatch, .duplicateCall, .unknownApprover, .approverChanged,
  .attemptOrder, .idempotencyKeyMismatch, .turnState]
#guard hostProtocol.all fun r => ["seq", "sequence", "state version", "renumber", "reload", "resend",
  "policy", "approver id", "attempt", "idempotency", "ledger"].all (!hasWord r.modelMessage ·)
#guard hostProtocol.all fun r => hasWord r.modelMessage "do not"
#guard Reason.all.all fun r => r.modelMessage.length ≤ 240 && r.userMessage.length ≤ 120 &&
  r.modelMessage.endsWith "." && r.userMessage.endsWith "."
#guard Reason.all.all fun r => (r.modelMessage.splitOn ". ").length ≤ 2 && (r.userMessage.splitOn ". ").length ≤ 2 &&
  !r.modelMessage.contains '_' && !r.userMessage.contains '_'
#guard [Reason.duplicateGrant, .unknownGrant, .grantNotAllowed].all fun r =>
  hasWord r.modelMessage "do not" && ["resend", "retry", "new grant id", "check the"].all (!hasWord r.modelMessage ·)
#guard kernelVersion == "0.1.0"

#guard ((Verdict.ok (.needsApproval ⟨"s1", "c1", 0⟩) none).toJsonWith 2).compact ==
  "{\"verdict\":\"accepted\",\"state_version\":2,\"decision\":\"needs_approval\",\"request_id\":{\"session\":\"s1\",\"call\":\"c1\",\"generation\":0}}"
#guard ((Verdict.rejected .staleSeq).toJsonWith 4).compact ==
  "{\"verdict\":\"rejected\",\"state_version\":4,\"reason\":\"stale_seq\",\"retry\":\"fix_request\",\"message\":\"The system that runs tool calls hit an internal error (it delivered events out of order). Your request was not the cause; do not change or repeat it on your own, and tell the user if this keeps happening.\"}"
#guard (toJson (Verdict.ok .none none)).compact == "{\"verdict\":\"accepted\"}"
#guard ((Verdict.ok .allowed (some (.wouldDeny .guardFalse))).toJsonWith 1).compact ==
  "{\"verdict\":\"accepted\",\"state_version\":1,\"decision\":\"allowed\",\"would_deny\":\"guard_false\"}"
#guard ((Verdict.ok (.existing (.denied .killed)) (some .wouldNeedApproval)).toJsonWith 1).compact.startsWith
  "{\"verdict\":\"accepted\",\"state_version\":1,\"decision\":\"existing\",\"status\":{\"status\":\"denied\",\"reason\":\"killed\"},\"would_need_approval\":true,\"retry\":\"never\",\"message\":"
#guard (toJson (Verdict.ok (.denied .meterExceeded) none)).compact.contains 'r' &&
  (toJson (Verdict.ok (.dispatchDenied .guardFalse) none)).compact ==
  s!"\{\"verdict\":\"accepted\",\"decision\":\"dispatch_denied\",\"reason\":\"guard_false\",\"retry\":\"after_user_action\",\"message\":\"{Reason.guardFalse.modelMessage}\"}"
#guard (toJson (Decision.allowedByGrant "g1")).compact == "{\"decision\":\"allowed_by_grant\",\"grant\":\"g1\"}"
#guard (toJson Decision.none).compact == "{}"
#guard (toJson (CallStatus.awaiting)).compact == "\"awaiting\""
#guard ((Verdict.ok (.overrun ["m"]) none).toJsonWith 7).compact ==
  "{\"verdict\":\"accepted\",\"state_version\":7,\"decision\":\"overrun\",\"meters\":[\"m\"]}"

def decodeAs (α : Type) [FromJson α] (s : String) : Except String α :=
  (Json.parse s).bind fun j => (decode j : Except DecodeError α).mapError (·.render)

def allDecisions : List Decision :=
  [.none, .pending, .authorized, .allowed, .allowedByGrant "g", .needsApproval ⟨"s", "c", 3⟩,
   .denied .killed, .dispatchClaimed, .dispatchDenied .grantInvalid, .existing .awaiting,
   .existing (.denied .escalated), .existing (.deniedAtDispatch .guardFalse), .existing .cancelled,
   .existing .succeeded, .existing .unknown, .overrun ["m"], .overrun ["usd_day", "usd_month"]]
def allShadows : List (Option Shadow) := [none, some (.wouldDeny .meterExceeded), some .wouldNeedApproval]

def verdictRoundTrips (v : Verdict) : Bool :=
  decodeAs Verdict (toJson v).compact == .ok v && decodeAs Verdict (v.toJsonWith 9).compact == .ok v

#guard allDecisions.all fun d => decodeAs Decision (toJson d).compact == .ok d
#guard allDecisions.all fun d => allShadows.all fun sh => verdictRoundTrips (.ok d sh)
#guard decodeAs Verdict "{\"verdict\":\"accepted\",\"state_version\":7,\"decision\":\"overrun\",\"meters\":[\"m\"]}"
  == .ok (.ok (.overrun ["m"]) none)
#guard (decodeAs Verdict "{\"verdict\":\"accepted\",\"decision\":\"overrun\",\"meters\":[]}").isOk == false
#guard decodeAs Verdict "{\"verdict\":\"accepted\",\"decision\":\"allowed\",\"meters\":[\"m\"]}"
  == .error "meters: unknown field"
#guard Reason.all.all fun r => verdictRoundTrips (.rejected r)
#guard [CallStatus.denied .killed, .awaiting, .authorized, .dispatched, .succeeded, .failed, .declined, .unknown,
  .rejected, .expired, .deniedAtDispatch .attemptLimit, .cancelled].all fun s =>
    decodeAs CallStatus (toJson s).compact == .ok s
#guard [Shadow.wouldDeny .stepLimit, .wouldNeedApproval].all fun s => decodeAs Shadow (toJson s).compact == .ok s

#guard (decodeAs Verdict "{\"verdict\":\"accepted\",\"decision\":\"allowed\",\"reason\":\"killed\"}") ==
  .error "reason: unknown field"
#guard (decodeAs Verdict "{\"verdict\":\"rejected\",\"decision\":\"allowed\",\"reason\":\"killed\"}") ==
  .error "decision: unknown field"
#guard (decodeAs Verdict "{\"verdict\":\"accepted\",\"decision\":\"denied\"}") == .error "reason: missing field"
#guard (decodeAs Verdict "{\"verdict\":\"accepted\",\"decision\":\"maybe\"}") == .error "decision: unknown value \"maybe\""
#guard (decodeAs Verdict "{\"verdict\":\"accepted\",\"bogus\":1}") == .error "bogus: unknown field"
#guard (decodeAs Verdict "{\"verdict\":\"rejected\",\"reason\":\"nope\"}").toOption.isNone

def sessionStartDoc : String := "{ \"type\": \"session_start\", \"seq\": 1, \"time\": 0, \"state_version\": 0, \"session_id\": \"s1\",
  \"requester\": \"u1\", \"permissions\": [\"payments\"], \"approvers\": {}, \"ledger\": {} }"
def proposeDoc : String := "{ \"type\": \"propose\", \"seq\": 2, \"time\": 1, \"state_version\": 1, \"call_id\": \"c1\", \"tool\": \"shop.buy\",
  \"call_digest\": \"d1\", \"cost\": { \"amount\": \"1200\", \"currency\": \"USD\" }, \"guards\": {}, \"escalators\": {} }"

def eventWith (d : Option String) (s : String) : Except String Event :=
  (Json.parse s).bind fun j => (Event.decodeWith d j).mapError (·.render)

#guard eventWith (some "d") sessionStartDoc == .ok
  ⟨1, 0, 0, none, .sessionStart "s1" "d" "u1" ["payments"] [] {}⟩
#guard eventWith (some "d") proposeDoc == .ok
  ⟨2, 1, 1, none, .propose "c1" "shop.buy" "d1" (some ⟨1200, "USD"⟩) [] []⟩
#guard eventWith none sessionStartDoc == .error "policy_digest: missing field"
#guard decodeAs Event sessionStartDoc == .error "policy_digest: missing field"
#guard (eventWith (some "d") sessionStartDoc).toOption.all fun e =>
  (toJson e).compact.contains 'd' && eventWith none (toJson e).compact == .ok e

#guard eventWith (some "d") (proposeDoc.replace "\"guards\": {}, " "") == .error "guards: missing field"
#guard eventWith (some "d") (proposeDoc.replace ", \"escalators\": {}" "") == .error "escalators: missing field"
#guard (eventWith none "{ \"type\": \"dispatch\", \"seq\": 1, \"time\": 0, \"state_version\": 0, \"call_id\": \"c\", \"attempt\": 1, \"call_digest\": \"d\", \"idempotency_key\": \"k\" }") == .error "guards: missing field"
#guard (decodeAs Event "{ \"type\": \"approve\", \"seq\": 1, \"time\": 0, \"state_version\": 0, \"call_id\": \"c\", \"request_id\": {\"session\":\"s\",\"call\":\"c\",\"generation\":0}, \"approver\": \"a\", \"reviewed_digest\": \"d\", \"edit\": {\"new_digest\": \"e\"} }") == .error "edit.escalators: missing field"
#guard (toJson (⟨"e", none, []⟩ : Edit)).compact == "{\"new_digest\":\"e\",\"escalators\":{}}"

def withAudit : String :=
  "{ \"type\": \"step_start\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"origin\": \"host\", \"audit\": {\"provider_call_id\": \"toolu_1\", \"on_behalf_of\": \"u7\"} }"
#guard decodeAs Event withAudit == .ok ⟨3, 5, 2, some "host", .stepStart⟩
#guard decodeAs Event "{ \"type\": \"step_start\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"audit\": 5 }" ==
  .error "audit: expected an object"
#guard decodeAs Event "{ \"type\": \"step_start\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"extra\": 1 }" ==
  .error "extra: unknown field"
#guard decodeAs Event "{ \"type\": \"step_start\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"call_id\": \"c\" }" ==
  .error "call_id: unknown field"
#guard decodeAs Event "{ \"type\": \"warp\", \"seq\": 3, \"time\": 5, \"state_version\": 2 }" ==
  .error ("type: unknown value \"warp\", expected one of " ++ ", ".intercalate (eventTypes.map (·.1)))
#guard decodeAs Event "{ \"seq\": 3 }" == .error "type: missing field"
#guard decodeAs Event "{ \"type\": \"kill\", \"seq\": -3, \"time\": 5, \"state_version\": 2 }" ==
  .error "seq: expected a non-negative integer"
#guard decodeAs Event "{ \"type\": \"result\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"call_id\": \"c\", \"outcome\": \"succeeded\", \"actual_cost\": 5 }" ==
  .error "actual_cost: expected a decimal string"
#guard ["\"\"", "\"01\"", "\"+1\"", "\"-1\"", "\" 1\"", "\"1.0\"", "\"1e3\"", "1200"].all fun a =>
  match decodeAs Event s!"\{ \"type\": \"result\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"call_id\": \"c\", \"outcome\": \"failed\", \"actual_cost\": {a} }" with
  | .error m => m.startsWith "actual_cost: "
  | .ok _ => false
#guard decodeAs Event "{ \"type\": \"result\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"call_id\": \"c\", \"outcome\": \"succeeded\", \"actual_cost\": \"340282366920938463463374607431768211456\" }" ==
  .ok ⟨3, 5, 2, none, .result "c" .succeeded (some 340282366920938463463374607431768211456) false⟩
#guard decodeAs Event "{ \"type\": \"approver_attest\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"approver\": \"a\", \"principal\": \"p\", \"kind\": \"human\", \"roles\": [\"owner\"] }" ==
  .ok ⟨3, 5, 2, none, .approverAttest "a" ⟨"p", .human, ["owner"]⟩⟩
#guard decodeAs Event "{ \"type\": \"session_start\", \"seq\": 1, \"time\": 0, \"state_version\": 0, \"session_id\": \"s\", \"policy_digest\": \"d\",
  \"requester\": \"u\", \"permissions\": [], \"approvers\": {\"a\": {\"principal\": \"p\", \"kind\": \"service\", \"roles\": []}}, \"ledger\": {} }" ==
  .error "approvers.a.kind: unknown value \"service\", expected one of human, automated"

def sampleBodies : List EventBody :=
  [.sessionStart "s" "d" "u" ["p", "q"] [("a", ⟨"x", .human, ["o"]⟩), ("b", ⟨"y", .automated, []⟩)]
     { version := 2, entries := [⟨"m", "s", "c", 4, 10, true, 3, 7⟩, ⟨"m", "s", "c2", 5, 0, false, 0, 0⟩], tombstone := true },
   .sessionEnd, .turnStart true, .turnEnd, .stepStart,
   .propose "c" "t" "d" none [("g", true), ("h", false)] [("e", false)],
   .approve "c" ⟨"s", "c", 1⟩ "a" "d" (some ⟨5, "USD"⟩) (some ⟨"d2", some ⟨6, "USD"⟩, [("e", true)]⟩),
   .approve "c" ⟨"s", "c", 1⟩ "a" "d" none (some ⟨"d2", none, []⟩),
   .reject "c" ⟨"s", "c", 0⟩ "a", .approvalExpire "c" ⟨"s", "c", 0⟩,
   .grantCreate "g" "a" "t" (some "d") .turn 3 (some ⟨9, "EUR"⟩) (some 1) (some 2) "rsd",
   .grantCreate "g" "a" "t" none .session 3 none none none "rsd",
   .grantRevoke "g", .approverAttest "a" ⟨"p", .automated, ["r"]⟩, .permissionAdd "p" "a", .permissionRevoke "p",
   .dispatch "c" 2 "d" (some ⟨0, "USD"⟩) [("g", true)] "k", .result "c" .declined (some 0) true,
   .result "c" .failed none false, .outcomeUnknown "c", .reconcile "c" .succeeded (some 7) false, .cancel "c",
   .escalationAck "a" 2, .ledgerSync {}, .reset, .kill]

#guard sampleBodies.all fun b => let e : Event := ⟨7, 8, 9, some "o", b⟩
  decodeAs Event (toJson e).compact == .ok e
#guard (sampleBodies.map fun b => b.typeName).eraseDups.length == 23
#guard (toJson (⟨1, 2, 3, none, .sessionStart "s" "d" "u" [] [] {}⟩ : Event)).compact ==
  "{\"type\":\"session_start\",\"seq\":1,\"time\":2,\"state_version\":3,\"session_id\":\"s\",\"policy_digest\":\"d\",\"requester\":\"u\",\"permissions\":[],\"approvers\":{},\"ledger\":{}}"

def keysUnique : Json → Bool
  | .obj kvs => (kvs.toList.map (·.1)).eraseDups.length == kvs.size
  | _ => true

def traceItems (i : Nat) : List (Event × Verdict) :=
  ((WritTests.Fuzz.replay (WritTests.Fuzz.genTrace i 40)).items.filterMap fun
    | .step ⟨_, _, e, v, _⟩ => some (e, v)
    | _ => none)

def traceRoundTrips (i : Nat) : Bool :=
  (traceItems i).all fun (e, v) =>
    decodeAs Event (toJson e).compact == .ok e && decode (toJson e) == (.ok e : Except DecodeError Event) &&
    verdictRoundTrips v && keysUnique (toJson e) && keysUnique (v.toJsonWith 3)

#guard (List.range 200).all traceRoundTrips
#guard (List.range 200).foldl (fun n i => n + (traceItems i).length) 0 > 1000
#guard ((List.range 200).flatMap fun i => (traceItems i).map fun (e, _) => e.body.typeName).eraseDups.length == 23

def stateRoundTrips (s : State) : Bool :=
  let j := toJson s
  (decode j : Except DecodeError State) == .ok s &&
    (Json.parse j.compact |>.bind fun j' =>
      (decode j' : Except DecodeError State).mapError (·.render)) == (.ok s : Except String State) &&
    keysUnique j

def laneItems (i : Nat) : List (State × Event × Verdict × State) :=
  let items := (WritTests.Fuzz.replay (WritTests.Fuzz.genTrace i 40)).items.filterMap fun
    | .step ⟨inst, b, e, v, a⟩ => some (inst, b, e, v, a)
    | _ => none
  match items.head? with
  | none => []
  | some (inst, _) => (items.filter (·.1 == inst)).map fun (_, b, e, v, a) => (b, e, v, a)

def resumes (i : Nat) : Bool :=
  let g := WritTests.Fuzz.genTrace i 40
  let items := laneItems i
  match items[items.length / 2]? with
  | none => true
  | some (mid, _, _, _) =>
    match (decode (toJson mid) : Except DecodeError State) with
    | .error _ => false
    | .ok loaded =>
      let rest := (items.drop (items.length / 2)).map (·.2.1)
      let run (s : State) := rest.foldl (fun (s, vs) e => let (s', v) := step g.policy s e; (s', vs ++ [v])) (s, [])
      let (sa, va) := run mid
      let (sb, vb) := run loaded
      sa == sb && va == vb

#guard (List.range 200).all resumes
#guard (List.range 100).all fun i => (laneItems i).all fun (b, _, _, a) => stateRoundTrips b && stateRoundTrips a
#guard (List.range 200).foldl (fun n i => n + (laneItems i).length) 0 > 1000
#guard stateRoundTrips (State.initial "d")

def stateDoc (kv : String) : String :=
  s!"\{ \"schema\": \"writ.state/1\", \"kernel_version\": \"{kv}\" }"

#guard decodeAs State (stateDoc "0.0.9") == .error "kernel_version: state was written by kernel 0.0.9, this is 0.1.0"
#guard decodeAs State (stateDoc "0.1.0") == .error "policy_digest: missing field"
#guard decodeAs State ((toJson (State.initial "d")).compact.replace "writ.state/1" "writ.state/2") ==
  .error "schema: state document is writ.state/2, this reader handles writ.state/1"
#guard decodeAs State ((toJson (State.initial "d")).compact.replace "\"epoch\":0" "\"epoch\":0,\"epcoh\":1") ==
  .error "epcoh: unknown field"

def longStr (n : Nat) (c : Char := 'a') : String := String.ofList (List.replicate n c)
def limitDoc (cid : String) (guard : String := "g") (origin : String := "o") : String :=
  s!"\{ \"type\": \"propose\", \"seq\": 1, \"time\": 0, \"state_version\": 0, \"origin\": \"{origin}\", \"call_id\": \"{cid}\", \"tool\": \"t\", \"call_digest\": \"d\", \"guards\": \{\"{guard}\": true}, \"escalators\": \{} }"
def eventErr (s : String) : String :=
  match decodeAs Event s with
  | .ok _ => ""
  | .error e => e

#guard eventErr (limitDoc (longStr 512)) == ""
#guard eventErr (limitDoc (longStr 513)) == "call_id: longer than 512 bytes"
#guard eventErr (limitDoc (longStr 256 'é')) == ""
#guard eventErr (limitDoc (longStr 257 'é')) == "call_id: longer than 512 bytes"
#guard eventErr (limitDoc "c" (guard := longStr 513)) == "guards: has a key longer than 512 bytes"
#guard eventErr (limitDoc "c" (origin := longStr 513)) == ""
#guard eventErr s!"\{ \"type\": \"approver_attest\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"approver\": \"a\", \"principal\": \"p\", \"kind\": \"human\", \"roles\": [\"o\", \"{longStr 513}\"] }"
  == "roles[1]: longer than 512 bytes"
#guard eventErr s!"\{ \"type\": \"reject\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"call_id\": \"c\", \"request_id\": \{\"session\":\"s\",\"call\":\"{longStr 513}\",\"generation\":0}, \"approver\": \"a\" }"
  == "request_id.call: longer than 512 bytes"
#guard eventErr s!"\{ \"type\": \"step_start\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"audit\": \{\"note\": \"{longStr 513}\"} }" == ""
#guard eventErr s!"\{ \"type\": \"ledger_sync\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"ledger\": \{\"entries\": [\{\"meter\": \"{longStr 513}\", \"session\": \"s\", \"call\": \"c\", \"time\": 0, \"amount\": \"1\", \"committed\": true}]} }" == ""
#guard eventErr s!"\{ \"type\": \"session_start\", \"seq\": 1, \"time\": 0, \"state_version\": 0, \"session_id\": \"s\", \"policy_digest\": \"d\", \"requester\": \"u\", \"permissions\": [], \"approvers\": \{\"{longStr 513}\": \{\"principal\": \"p\", \"kind\": \"human\", \"roles\": []}}, \"ledger\": \{} }"
  == "approvers: has a key longer than 512 bytes"
#guard eventErr s!"\{ \"type\": \"dispatch\", \"seq\": 3, \"time\": 5, \"state_version\": 2, \"call_id\": \"c\", \"attempt\": 1, \"call_digest\": \"d\", \"cost\": \{\"amount\": \"1\", \"currency\": \"{longStr 513}\"}, \"guards\": \{}, \"idempotency_key\": \"k\" }"
  == "cost.currency: longer than 512 bytes"
#guard eventErr (limitDoc "c" (guard := longStr 512)) == ""
def evDoc (ty fields : String) : String :=
  s!"\{ \"type\": \"{ty}\", \"seq\": 3, \"time\": 5, \"state_version\": 2, {fields} }"
def limitPropose (tool esc : String) : String :=
  evDoc "propose" s!"\"call_id\": \"c\", \"tool\": \"{tool}\", \"call_digest\": \"d\", \"guards\": \{}, \"escalators\": \{\"{esc}\": true}"
def editDoc (digest esc : String) : String :=
  evDoc "approve" s!"\"call_id\": \"c\", \"request_id\": \{\"session\":\"s\",\"call\":\"c\",\"generation\":0}, \"approver\": \"a\", \"reviewed_digest\": \"d\", \"edit\": \{\"new_digest\": \"{digest}\", \"escalators\": \{\"{esc}\": true}}"
def startDoc (sid req perm : String) : String :=
  evDoc "session_start" s!"\"session_id\": \"{sid}\", \"policy_digest\": \"d\", \"requester\": \"{req}\", \"permissions\": [\"{perm}\"], \"approvers\": \{}, \"ledger\": \{}"
#guard eventErr (limitPropose "t" (longStr 512)) == ""
#guard eventErr (limitPropose "t" (longStr 513)) == "escalators: has a key longer than 512 bytes"
#guard eventErr (limitPropose (longStr 513) "e") == "tool: longer than 512 bytes"
#guard eventErr (editDoc "d2" "e") == ""
#guard eventErr (editDoc "d2" (longStr 513)) == "edit.escalators: has a key longer than 512 bytes"
#guard eventErr (editDoc (longStr 513) "e") == "edit.new_digest: longer than 512 bytes"
#guard eventErr (startDoc "s" "u" "p") == ""
#guard eventErr (startDoc (longStr 513) "u" "p") == "session_id: longer than 512 bytes"
#guard eventErr (startDoc "s" (longStr 513) "p") == "requester: longer than 512 bytes"
#guard eventErr (startDoc "s" "u" (longStr 513)) == "permissions[0]: longer than 512 bytes"
#guard eventErr (evDoc "permission_add" s!"\"permission\": \"{longStr 513}\", \"approver\": \"a\"")
  == "permission: longer than 512 bytes"
#guard eventErr (evDoc "permission_revoke" s!"\"permission\": \"{longStr 513}\"")
  == "permission: longer than 512 bytes"
#guard eventErr (evDoc "grant_revoke" s!"\"grant_id\": \"{longStr 513}\"") == "grant_id: longer than 512 bytes"
#guard eventErr (evDoc "grant_revoke" s!"\"grant_id\": \"{longStr 512}\"") == ""
#guard eventErr (evDoc "dispatch" s!"\"call_id\": \"c\", \"attempt\": 1, \"call_digest\": \"d\", \"guards\": \{}, \"idempotency_key\": \"{longStr 513}\"")
  == "idempotency_key: longer than 512 bytes"

def goldenPolicy : Policy :=
  { approverRoles := ["owner"]
    meters := [("usd", { unit := .money "USD", cap := some 100 })]
    actions := [("pay", { consent := .perCall, meters := ["usd"] })] }

def goldenState : State :=
  let evs : List EventBody := [
    .sessionStart "s1" "pd" "u1" ["p"] [("a", ⟨"alice", .human, ["owner"]⟩)] {},
    .turnStart true, .stepStart,
    .propose "c1" "pay" "d1" (some ⟨5, "USD"⟩) [] [],
    .approve "c1" ⟨"s1", "c1", 0⟩ "a" "d1" (some ⟨5, "USD"⟩) none,
    .dispatch "c1" 1 "d1" (some ⟨5, "USD"⟩) [] "k1"]
  (evs.foldl (fun (s, n) b => ((step goldenPolicy s ⟨n, n, s.version, none, b⟩).1, n + 1))
    (State.initial "pd", 1)).1

#guard (toJson goldenState).compact == "{\"schema\":\"writ.state/1\",\"kernel_version\":\"0.1.0\",\"policy_digest\":\"pd\",\"session_id\":\"s1\",\"state_version\":6,\"last_seq\":6,\"last_time\":6,\"epoch\":0,\"started\":true,\"ended\":false,\"requester\":\"u1\",\"permissions\":[\"p\"],\"approvers\":{\"a\":{\"principal\":\"alice\",\"kind\":\"human\",\"roles\":[\"owner\"]}},\"turn_active\":true,\"turn_index\":1,\"steps_this_turn\":1,\"proposals_this_turn\":1,\"approvals_this_turn\":1,\"proposals_this_session\":1,\"approvals_this_session\":1,\"calls\":{\"c1\":{\"tool\":\"pay\",\"epoch\":0,\"proposed_digest\":\"d1\",\"proposed_cost\":{\"amount\":\"5\",\"currency\":\"USD\"},\"proposed_guards\":{},\"proposed_escalators\":{},\"decision\":{\"decision\":\"needs_approval\",\"request_id\":{\"session\":\"s1\",\"call\":\"c1\",\"generation\":0}},\"shadow\":null,\"consent\":\"per_call\",\"digest\":\"d1\",\"cost\":{\"amount\":\"5\",\"currency\":\"USD\"},\"status\":\"dispatched\",\"generation\":0,\"generations\":[{\"digest\":\"d1\",\"cost\":{\"amount\":\"5\",\"currency\":\"USD\"}}],\"tally\":[{\"principal\":\"alice\",\"approver\":\"a\"}],\"requested_at\":4,\"authorized_at\":5,\"grant\":null,\"attempts\":1,\"idempotency_key\":\"k1\",\"reconciled\":null}},\"grants\":{},\"session_meters\":[{\"meter\":\"usd\",\"session\":\"s1\",\"call\":\"c1\",\"time\":6,\"amount\":\"5\",\"committed\":false}],\"ledger\":{\"version\":1},\"killed\":false,\"escalated\":false,\"failures\":{},\"failures_this_session\":0,\"blocked_tools\":[],\"escalations\":0,\"rejected_memory\":[]}"
#guard stateRoundTrips goldenState

end WritTests.Codec
