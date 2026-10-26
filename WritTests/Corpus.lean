import Writ
import WritTests.JsonHelpers

open Writ

namespace WritTests.Corpus

def webChat : String := include_str "../corpus/examples/web-chat.jsonl"
def codingAgent : String := include_str "../corpus/examples/coding-agent.jsonl"
def langgraphResume : String := include_str "../corpus/examples/langgraph-resume.jsonl"
def mcpGateway : String := include_str "../corpus/examples/mcp-gateway.jsonl"
def mcpApproval : String := include_str "../corpus/examples/mcp-approval.jsonl"
def payments : String := include_str "../corpus/examples/payments.jsonl"
def deviceSplit : String := include_str "../corpus/examples/device-split.jsonl"

def attackCrossSession : String := include_str "../corpus/attacks/cross-session-escape.jsonl"
def attackRollback : String := include_str "../corpus/attacks/rollback.jsonl"
def attackQuorumEdit : String := include_str "../corpus/attacks/quorum-edit-laundering.jsonl"
def attackStaleDialog : String := include_str "../corpus/attacks/stale-dialog.jsonl"
def attackRejectionShopping : String := include_str "../corpus/attacks/rejection-shopping.jsonl"
def attackAsu : String := include_str "../corpus/attacks/asu.jsonl"

def assistantJson : String := include_str "../schema/examples/assistant.json"

def files : List (String × String) := [("web-chat", webChat), ("coding-agent", codingAgent),
  ("langgraph-resume", langgraphResume), ("mcp-gateway", mcpGateway), ("payments", payments),
  ("device-split", deviceSplit), ("mcp-approval", mcpApproval)]

def tracesOf (text : String) : List Trace := (parseTraces text).toOption.getD []

#guard (parseTraces webChat).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces codingAgent).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces langgraphResume).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces mcpGateway).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces payments).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces deviceSplit).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces mcpApproval).map (·.all (·.replay.ok)) == .ok true

#guard files.all fun (_, text) =>
  let ts := tracesOf text
  3 ≤ ts.length && ts.length ≤ 8 && ts.all fun t => t.policy.check.isEmpty && t.description.isSome

#guard files.all fun (name, text) => (tracesOf text).all (·.id.startsWith (name ++ "/"))
#guard ((files.flatMap fun (_, text) => (tracesOf text).map (·.id)).eraseDups.length ==
  (files.flatMap fun (_, text) => tracesOf text).length)

def keyOf (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

/-- Corpus discipline: each expect pins `verdict`, plus `decision`, `reason`, `request_id`,
`grant`, `status` and `meters` whenever the verdict carries them. -/
def pinsEnough (t : Trace) : Bool :=
  (t.steps.zip t.replay.steps).all fun (st, r) =>
    match st.expect with
    | none => false
    | some e =>
      let actual := r.verdict.toJsonWith 0
      ["verdict", "decision", "reason", "request_id", "grant", "status", "meters"].all fun k =>
        (keyOf actual k).isNone || (keyOf e k).isSome

#guard files.all fun (_, text) => (tracesOf text).all pinsEnough

#guard files.all fun (_, text) => (text.splitOn "\"policy_digest\":\"sha256:").length == 2
#guard files.all fun (_, text) => (tracesOf text).any fun t => t.steps.any fun st =>
  match st.event.body with
  | .sessionStart _ pd .. => pd == t.policyDoc.digest
  | _ => false

def pinsRetryAndVersion (t : Trace) (verdict : String) : Bool :=
  t.steps.any fun st =>
    match st.expect with
    | some e =>
      (keyOf e "retry").isSome && (keyOf e "state_version").isSome &&
        keyOf e "verdict" == some (.str verdict) &&
        (verdict != "accepted" || keyOf e "decision" == some (.str "denied"))
    | none => false

#guard files.all fun (_, text) => (tracesOf text).any (pinsRetryAndVersion · "rejected")
#guard files.all fun (_, text) => (tracesOf text).any (pinsRetryAndVersion · "accepted")

def roundTripsTrace (t : Trace) : Bool :=
  (decode (toJson t) : Except DecodeError Trace) == .ok t &&
    ((Json.parse (toJson t).compact).toOption.map fun j =>
      (decode j : Except DecodeError Trace) == .ok t) == some true

#guard files.all fun (_, text) => (tracesOf text).all roundTripsTrace

def runState (t : Trace) : State :=
  t.steps.foldl (fun s st => (step t.policy s st.event).1) (State.initial t.digest)

def syncedLedger (t : Trace) : Option Ledger :=
  t.steps.findSome? fun st => match st.event.body with
    | .ledgerSync l => some l
    | _ => none

#guard match tracesOf mcpGateway |>.filter (·.id.startsWith "mcp-gateway/double-spend") with
  | [a, b] => syncedLedger b == some (runState a).ledger && a.digest == b.digest
  | _ => false

def tinyPolicy : String := "{\"writ\":\"0.1\",\"actions\":{\"a\":{}}}"

def traceLine (events : String) : String :=
  "{\"schema\":\"writ.trace/1\",\"id\":\"t\",\"policy\":" ++ tinyPolicy ++ ",\"events\":[" ++ events ++ "]}"

def startEv : String :=
  "{\"event\":{\"type\":\"session_start\",\"seq\":1,\"time\":0,\"state_version\":0,\"session_id\":\"s1\",\"requester\":\"u1\",\"permissions\":[],\"approvers\":{},\"ledger\":{}},\"expect\":{\"verdict\":\"accepted\"}}"

def proposeEv (expect : String) : String :=
  "{\"event\":{\"type\":\"propose\",\"seq\":2,\"time\":1,\"state_version\":1,\"call_id\":\"c1\",\"tool\":\"a\",\"call_digest\":\"d1\",\"guards\":{},\"escalators\":{}},\"expect\":" ++ expect ++ "}"

def mismatches (events : String) : List String :=
  match parseTraces (traceLine events) with
  | .ok [t] => t.replay.steps.filterMap (·.mismatch)
  | .ok _ => ["wrong trace count"]
  | .error e => ["parse: " ++ e]

#guard mismatches (startEv ++ "," ++ proposeEv "{\"verdict\":\"accepted\",\"decision\":\"allowed\"}") == []
#guard mismatches (startEv ++ "," ++ proposeEv "{\"verdict\":\"accepted\"}") == []
#guard mismatches (startEv ++ "," ++ proposeEv "{\"decision\":\"needs_approval\"}") ==
  ["expected decision needs_approval, got allowed"]
#guard mismatches (startEv ++ "," ++ proposeEv "{\"verdict\":\"accepted\",\"reason\":\"killed\"}") ==
  ["expected reason killed, got no reason"]
#guard mismatches (startEv ++ "," ++ proposeEv "{\"state_version\":2,\"decision\":\"allowed\"}") == []
#guard mismatches (startEv ++ "," ++ proposeEv "{\"state_version\":1,\"verdict\":\"rejected\"}") ==
  ["expected state_version 1, got 2; expected verdict rejected, got accepted"]

#guard expectMismatch (.obj #[("request_id", .obj #[("generation", .num 0), ("session", .str "s1"), ("call", .str "c1")])])
  (Verdict.toJsonWith (.ok (.needsApproval ⟨"s1", "c1", 0⟩) none) 3) == none
#guard expectMismatch (.obj #[("request_id", .obj #[("session", .str "s1"), ("call", .str "c1")])])
  (Verdict.toJsonWith (.ok (.needsApproval ⟨"s1", "c1", 0⟩) none) 3) ==
  some "expected request_id {\"session\":\"s1\",\"call\":\"c1\"}, got {\"session\":\"s1\",\"call\":\"c1\",\"generation\":0}"

def attacks : List (String × String) := [("cross-session-escape", attackCrossSession),
  ("rollback", attackRollback), ("quorum-edit-laundering", attackQuorumEdit),
  ("stale-dialog", attackStaleDialog), ("rejection-shopping", attackRejectionShopping), ("asu", attackAsu)]

#guard (parseTraces attackCrossSession).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces attackRollback).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces attackQuorumEdit).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces attackStaleDialog).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces attackRejectionShopping).map (·.all (·.replay.ok)) == .ok true
#guard (parseTraces attackAsu).map (·.all (·.replay.ok)) == .ok true

#guard attacks.all fun (name, text) =>
  let ts := tracesOf text
  2 ≤ ts.length && ts.all fun t =>
    t.policy.check.isEmpty && t.description.isSome && t.id.startsWith (name ++ "/") &&
      ts.all (·.policyDoc == t.policyDoc)
#guard ((attacks.flatMap fun (_, text) => (tracesOf text).map (·.id)).eraseDups.length ==
  (attacks.flatMap fun (_, text) => tracesOf text).length)
#guard attacks.all fun (_, text) => (tracesOf text).all fun t => pinsEnough t && roundTripsTrace t
#guard attacks.all fun (_, text) => (tracesOf text).any (pinsRetryAndVersion · "rejected")
#guard attacks.all fun (_, text) => (text.splitOn "\"policy_digest\":\"sha256:").length == 2 &&
  ((tracesOf text).head?.map fun t => t.steps.any fun st =>
    match st.event.body with
    | .sessionStart _ pd .. => pd == t.policyDoc.digest
    | _ => false) == some true

#guard match tracesOf attackCrossSession |>.filter (·.id.startsWith "cross-session-escape/session-") with
  | [a, b] => syncedLedger b == some (runState a).ledger && a.digest == b.digest
  | _ => false

def badSecond : String := startEv ++ "," ++ proposeEv "{\"verdict\":\"rejected\"}"

#guard match parseTraces (traceLine (startEv ++ "," ++ proposeEv "{\"decision\":\"denied\"}" ++ ","
    ++ "{\"event\":{\"type\":\"propose\",\"seq\":3,\"time\":1,\"state_version\":2,\"call_id\":\"c2\",\"tool\":\"b\",\"call_digest\":\"d1\",\"guards\":{},\"escalators\":{}},\"expect\":{\"decision\":\"allowed\"}}")) with
  | .ok [t] => let r := t.replay
    !r.ok && r.steps.length == 3 && (r.steps.map (·.mismatch.isSome)) == [false, true, true] &&
      (r.steps.map (·.index)) == [0, 1, 2] && r.id == "t"
  | _ => false

#guard match parseTraces (traceLine startEv) with
  | .ok [t] => t.replay.ok && t.digest == ((Json.parse tinyPolicy).toOption.map Json.digest).getD ""
  | _ => false

def parseErr (text : String) : String :=
  match parseTraces text with
  | .ok _ => ""
  | .error e => e

#guard parseTraces "" == .ok []
#guard (parseTraces ("\n" ++ traceLine startEv ++ "\n\n" ++ traceLine startEv ++ "\n")).map (·.length) == .ok 2
#guard parseErr ("\n" ++ traceLine startEv ++ "\n" ++ traceLine (startEv ++ ",{\"event\":{\"type\":\"cancel\",\"seq\":2,\"time\":1,\"state_version\":1}}")) ==
  "line 3: events[1].event.call_id: missing field"
#guard parseErr (traceLine startEv ++ "\n{\"schema\":") == "line 2: unexpected end of input at column 11"
#guard parseErr ((traceLine startEv).replace "writ.trace/1" "writ.trace/2") ==
  "line 1: schema: unsupported schema \"writ.trace/2\", expected \"writ.trace/1\""
#guard parseErr ((traceLine startEv).replace "\"id\":\"t\"," "") == "line 1: id: missing field"
#guard parseErr ((traceLine startEv).replace "\"id\":\"t\"," "\"id\":\"t\",\"notes\":1,") == "line 1: notes: unknown field"
#guard parseErr ((traceLine startEv).replace "{\"verdict\":\"accepted\"}" "{\"decison\":\"allowed\"}") ==
  "line 1: events[0].expect.decison: unknown field"
#guard parseErr ((traceLine startEv).replace "{\"verdict\":\"accepted\"}" "[]") == "line 1: events[0].expect: expected an object"
#guard parseErr ((traceLine startEv).replace "\"expect\"" "\"expected\"") == "line 1: events[0].expected: unknown field"
#guard parseErr ((traceLine startEv).replace "{\"a\":{}}" "{\"a\":{\"consnet\":1}}") == "line 1: policy.actions.a.consnet: unknown field"

def withDigest (d : String) : String :=
  (traceLine startEv).replace "\"events\"" ("\"policy_digest\":\"" ++ d ++ "\",\"events\"")

#guard match parseTraces (withDigest "pd") with
  | .ok [t] => t.digest == "pd" && t.replay.ok &&
    (t.steps.head?.map fun st => st.event.body == .sessionStart "s1" "pd" "u1" [] [] {}) == some true
  | _ => false

#guard match parseTraces (withDigest "pd") with
  | .ok [t] => (toJson t).compact.startsWith
      "{\"schema\":\"writ.trace/1\",\"id\":\"t\",\"policy\":{\"writ\":\"0.1\",\"actions\":{\"a\":{}}},\"policy_digest\":\"pd\",\"events\":[{\"event\":{\"type\":\"session_start\""
  | _ => false

#guard match Policy.parseDoc assistantJson with
  | .ok (p, _) => p.check.isEmpty && p.warnings.isEmpty && p.actions.length == 13
  | .error _ => false

end WritTests.Corpus
