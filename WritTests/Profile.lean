import Writ
import WritTests.ProfileVectors

open Writ
open Writ.Profile.McpToolApproval

namespace WritTests.Profile

def vectorsFile : String := include_str "../corpus/profiles/mcp-tool-approval-v1.jsonl"

#eval show IO Unit from do
  unless vectorsFile == WritTests.ProfileVectors.text do
    throw (IO.userError ("corpus/profiles/mcp-tool-approval-v1.jsonl differs from what the profile " ++
      "gives; regenerate it from WritTests.ProfileVectors.text"))

#guard Reason.all.length == 52

/-- Section 6's table, written out separately from `disposition`. -/
def expected : CallStatus → Option String
  | .succeeded => some "approved-executed"
  | .denied _ => some "denied-not-executed"
  | .rejected => some "denied-not-executed"
  | .expired => some "denied-not-executed"
  | .deniedAtDispatch _ => some "denied-not-executed"
  | .declined => some "denied-not-executed"
  | .failed => some "execution-error"
  | .unknown => some "outcome-unknown"
  | .cancelled => some "cancelled"
  | _ => none

open WritTests.ProfileVectors in
#guard statuses.all fun s => disposition s == expected s

open WritTests.ProfileVectors in
#guard statuses.all fun s => (disposition s).isSome == s.terminal

#guard [CallStatus.awaiting, .authorized, .dispatched].all (disposition · == none)

def keys : Json → List String
  | .obj kvs => kvs.toList.map (·.1)
  | _ => []

def member (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def isDenial (r : Reason) : Option Json → Bool
  | some j =>
    keys j == ["reason", "remediation", "code", "retry", "message"] &&
      member j "reason" == some (.str "insufficient_authorization") &&
      member j "remediation" == some (.str "unavailable") &&
      member j "code" == some (.str r.code) &&
      member j "retry" == some (.str r.retry.code) &&
      member j "message" == some (.str r.modelMessage)
  | none => false

#guard Reason.all.all fun r => isDenial r (envelope (.rejected r))
#guard Reason.all.all fun r => isDenial r (envelope (.ok (.denied r) none))
#guard Reason.all.all fun r => isDenial r (envelope (.ok (.dispatchDenied r) none))

#guard match envelope (.ok (.needsApproval ⟨"s1", "c1", 2⟩) none) with
  | some j =>
    keys j == ["reason", "remediation", "remediationHints", "requestId"] &&
      member j "remediation" == some (.str "available") &&
      (member j "requestId").map (·.compact) == some "{\"session\":\"s1\",\"call\":\"c1\",\"generation\":2}" &&
      (member j "remediationHints").map (·.compact) == some "[{\"type\":\"task\"}]"
  | none => false

#guard [Verdict.ok .allowed none, .ok .allowed (some (.wouldDeny .guardFalse)),
  .ok .allowed (some .wouldNeedApproval), .ok (.allowedByGrant "g") none, .ok .pending none,
  .ok .authorized none, .ok .dispatchClaimed none, .ok (.existing (.denied .killed)) none,
  .ok (.existing .unknown) none, .ok (.overrun ["m"]) none, .ok .none none].all (envelope · == none)

def act (name : String) (r : Requirements) : String × Requirements := (name, r)

def policy : Policy :=
  { actions := [act "plain" {}, act "retry" { idempotent := true, retryAfterUnknown := true, maxAttempts := 3 },
      act "tries" { maxAttempts := 2 }, act "once" { maxAttempts := 1 },
      act "retry1" { idempotent := true, retryAfterUnknown := true }] }

#guard problems policy == [.retryAfterUnknown "retry", .maxAttempts "tries", .retryAfterUnknown "retry1"]
#guard errors policy == [.retryAfterUnknown "retry", .retryAfterUnknown "retry1"]
#guard (problems policy).map (·.code) ==
  ["profile_retry_after_unknown", "profile_max_attempts", "profile_retry_after_unknown"]
#guard (problems policy).map (·.isError) == [true, false, true]
#guard (problems policy).map (·.action?) == [some "retry", some "tries", some "retry1"]
#guard problems { actions := [act "plain" {}, act "once" { maxAttempts := 1 }] } == []
#guard problems { policy with bindingMutable := false } == problems policy

def call (input : String) : String := Api.profile input

#guard call "{\"profile\":\"mcp-tool-approval\",\"status\":\"unknown\"}" ==
  "{\"disposition\":\"outcome-unknown\"}"
#guard call "{\"profile\":\"mcp-tool-approval\",\"status\":\"dispatched\"}" == "{}"
#guard call "{\"profile\":\"mcp-tool-approval\",\"verdict\":{\"verdict\":\"accepted\",\"decision\":\"allowed\"}}" == "{}"
#guard call "{\"profile\":\"mcp-tool-approval\",\"verdict\":{\"verdict\":\"rejected\",\"reason\":\"killed\"}}" ==
  (Json.obj #[("envelope", denial .killed)]).compact
#guard call "{\"profile\":\"writ/mcp-tool-approval\",\"status\":\"unknown\"}" ==
  "{\"error\":\"unknown profile \\\"writ/mcp-tool-approval\\\", expected mcp-tool-approval\",\"input\":\"profile\"}"
#guard call "{\"status\":\"unknown\"}" == "{\"error\":\"profile: missing field\",\"input\":\"profile\"}"
#guard call "{\"profile\":1,\"status\":\"unknown\"}" == "{\"error\":\"profile: expected a string\",\"input\":\"profile\"}"
#guard call "{\"profile\":\"mcp-tool-approval\"}" ==
  "{\"error\":\"expected exactly one of verdict and status\",\"input\":\"json\"}"
#guard call "{\"profile\":\"mcp-tool-approval\",\"status\":\"unknown\",\"verdict\":{\"verdict\":\"accepted\"}}" ==
  "{\"error\":\"expected exactly one of verdict and status\",\"input\":\"json\"}"
#guard call "{\"profile\":\"mcp-tool-approval\",\"status\":\"denied\"}" ==
  "{\"error\":\"status: \\\"denied\\\" needs a reason, write it as an object\",\"input\":\"json\"}"
#guard (call "{\"profile\":\"mcp-tool-approval\",\"verdict\":{\"verdict\":\"rejected\",\"reason\":\"nope\"}}").startsWith
  "{\"error\":\"verdict.reason: unknown value \\\"nope\\\", expected one of not_started,"
#guard call "{\"profile\":\"mcp-tool-approval\",\"status\":\"unknown\",\"extra\":1}" ==
  "{\"error\":\"extra: unknown field\",\"input\":\"json\"}"
#guard (call "{").startsWith "{\"error\":"
#guard (call "[]") == "{\"error\":\"expected an object\",\"input\":\"json\"}"

end WritTests.Profile
