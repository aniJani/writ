import Writ
import WritTests.JsonHelpers

open Writ

namespace WritTests.Api

def shop : String := include_str "../tests/cli/policies/formats-shop.json"
def simple : String := include_str "../tests/cli/policies/simple.json"
def badPolicy : String := include_str "../tests/cli/policies/errors.json"
def events : String := include_str "../tests/cli/oracle-events.jsonl"
def oracleOut : String := include_str "../tests/cli/oracle-1.out"
def afterState : String := include_str "../tests/cli/states/after-1.json"
def payments : String := include_str "../corpus/examples/payments.jsonl"

def field (envelope key : String) : Option Json :=
  match Json.parse envelope with
  | .ok (.obj kvs) => kvs.find? (·.1 == key) |>.map (·.2)
  | _ => none

def strField (envelope key : String) : String :=
  match field envelope key with
  | some (.str s) => s
  | _ => ""

def boolField (envelope key : String) : Option Bool :=
  match field envelope key with
  | some (.bool b) => some b
  | _ => none

def isError (envelope : String) : Bool := (field envelope "error").isSome

def lines (text : String) : List String := (text.splitOn "\n").filter (· != "")

def initialState (policy : String) : String := strField (Api.initial policy none) "state"

def feed (policy : String) (start : String) (evs : List String) : String × List String :=
  evs.foldl (init := (start, [])) fun (st, outs) ev =>
    let r := Api.step policy st ev
    match field r "verdict" with
    | some v => (strField r "state", outs ++ [v.compact])
    | none => (st, outs ++ [(Json.obj #[("error", .str (strField r "error"))]).compact])

#guard Api.check shop ==
  "{\"ok\":true,\"errors\":[],\"warnings\":[],\"policy_digest\":\"sha256:866cd32f034a15421198ab518d1e23a34f4acfb4ba2fb20884f9af5fca97a6dd\"}"

#guard (feed simple (initialState simple) (lines events)).2 == lines oracleOut
#guard (feed simple (initialState simple) (lines events)).1 ++ "\n" == afterState

def afterTwo : String := (feed simple (initialState simple) ((lines events).take 2)).1
def repeated : String := Api.step simple afterTwo "{\"type\":\"turn_start\",\"seq\":2,\"time\":10,\"state_version\":1,\"user_initiated\":true}"

#guard strField repeated "state" == afterTwo
#guard boolField repeated "changed" == some false
#guard boolField repeated "ledger_changed" == some false
#guard strField (Api.step simple afterTwo "{\"type\":\"step_start\",\"seq\":3,\"time\":20,\"state_version\":2}") "state" != afterTwo
#guard boolField (Api.step simple afterTwo "{\"type\":\"step_start\",\"seq\":3,\"time\":20,\"state_version\":2}") "changed" == some true

#guard isError (Api.step simple afterTwo "{\"type\":")
#guard isError (Api.step simple afterTwo "{\"type\":\"nope\"}")
#guard (feed simple afterTwo ["", "{"]).1 == afterTwo

#guard (strField (Api.initial simple none) "state") == (feed simple (initialState simple) []).1
#guard Api.initial simple none == Api.initial simple (some ((Json.parse simple).toOption.getD .null).digest)
#guard field (Api.initial simple (some "sha256:x")) "input" == some (.str "digest")
#guard field (Api.initial simple none) "state_version" == some (.num 0)
#guard field (Api.initial simple none) "ledger_version" == some (.num 0)

def failsCheck : Bool :=
  (strField (Api.initial badPolicy none) "error").startsWith "policy fails check: "
  && (strField (Api.step badPolicy afterTwo "{}") "error").startsWith "policy fails check: "
#guard failsCheck

def payTrace : Trace :=
  match parseTraces payments with
  | .ok (t :: _) => t
  | _ => { id := "", policy := {}, policyDoc := .null, steps := [] }

def payPolicyText : String := payTrace.policyDoc.compact

def payEvents : List String := payTrace.steps.map fun s => (toJson s.event).compact

def payStates : List (String × String) :=
  payEvents.foldl (init := [(initialState payPolicyText, "")]) fun acc ev =>
    let (st, _) := acc.getLast!
    let r := Api.step payPolicyText st ev
    acc ++ [(strField r "state", r)]

#guard payEvents.length == 9
#guard (payStates.drop 1).all fun (_, r) => !isError r
#guard (payStates.getD 8 ("", "")).2.contains "dispatch_claimed"
#guard boolField (payStates.getD 8 ("", "")).2 "ledger_changed" == some true
#guard field (payStates.getD 8 ("", "")).2 "ledger_version" == some (.num 2)
#guard boolField (payStates.getD 7 ("", "")).2 "ledger_changed" == some false
#guard ((Api.replay payments).splitOn "\"ok\":true").length == 5
#guard !(Api.replay payments).contains "\"ok\":false"

def flip (line : String) : String :=
  line.replace "\"decision\":\"dispatch_claimed\"" "\"decision\":\"allowed\""

def flippedFirst : String := "\n".intercalate ((lines payments).take 1 |>.map flip)

#guard Api.replay flippedFirst ==
  "{\"traces\":[{\"id\":\"payments/manager-and-finance\",\"ok\":false,\"mismatches\":[{\"step\":7,\"message\":\"expected decision allowed, got dispatch_claimed\"}]}]}"

def flippedOne : String := "\n".intercalate (match lines payments with | l :: rest => flip l :: rest | [] => [])

#guard ((Api.replay flippedOne).splitOn "\"ok\":false").length == 2
#guard ((Api.replay flippedOne).splitOn "\"ok\":true").length == 4

#guard Api.digest "{\"b\":1,\"a\":\"é\"}" ==
  "{\"digest\":\"" ++ ((Json.parse "{\"a\":\"é\",\"b\":1}").toOption.getD .null).digest ++ "\"}"
#guard Api.canonical "{\"b\":1,\"a\":\"é\"}" == "{\"canonical\":\"{\\\"a\\\":\\\"é\\\",\\\"b\\\":1}\"}"

#guard isError (Api.check "{")
#guard isError (Api.digest "{")
#guard isError (Api.canonical "{")
#guard isError (Api.initial "{" none)
#guard isError (Api.step "{" "{" "{")
#guard isError (Api.step simple "{" "{")
#guard isError (Api.step simple afterTwo "{")
#guard isError (Api.replay "{")

def inputOf (envelope : String) : Option Json := field envelope "input"

#guard inputOf (Api.check "{") == some (.str "policy")
#guard inputOf (Api.digest "{") == some (.str "json")
#guard inputOf (Api.canonical "{") == some (.str "json")
#guard inputOf (Api.initial "{" none) == some (.str "policy")
#guard inputOf (Api.initial badPolicy none) == some (.str "policy")
#guard inputOf (Api.step "{" "{" "{") == some (.str "policy")
#guard inputOf (Api.step simple "{" "{") == some (.str "state")
#guard inputOf (Api.step simple afterTwo "{") == some (.str "event")
#guard inputOf (Api.replay "{") == some (.str "traces")
#guard inputOf (Api.tombstone "{" true) == some (.str "ledger")
#guard inputOf (Api.inspect simple "{" 0) == some (.str "state")

def shopDigest : String := ((Json.parse shop).toOption.getD .null).digest
def foreign : String := Api.step simple (initialState shop) "{\"type\":\"turn_end\",\"seq\":1,\"time\":0,\"state_version\":0}"

#guard inputOf foreign == some (.str "state")
#guard strField foreign "error" ==
  s!"state was made under policy {shopDigest}, not {((Json.parse simple).toOption.getD .null).digest}"

def fractional : String := Api.step simple afterTwo
  "{\"type\":\"result\",\"seq\":3,\"time\":20,\"state_version\":2,\"call_id\":\"c1\",\"outcome\":\"succeeded\",\"actual_cost\":\"6.00\"}"

#guard inputOf fractional == some (.str "event")

def tombstoned : String := Api.tombstone "" true

#guard field tombstoned "ledger_version" == some (.num 1)
#guard boolField tombstoned "changed" == some true
#guard strField tombstoned "ledger" == "{\"tombstone\":true,\"version\":1}"
#guard field (Api.tombstone (strField tombstoned "ledger") true) "ledger_version" == some (.num 1)
#guard boolField (Api.tombstone (strField tombstoned "ledger") true) "changed" == some false
#guard field (Api.tombstone (strField tombstoned "ledger") false) "ledger_version" == some (.num 2)
#guard boolField (Api.tombstone "" false) "changed" == some false

def formatsA : String := include_str "../tests/cli/formats-events-a.jsonl"
def shopAfterA : String := (feed shop (initialState shop) (lines formatsA)).1
def shopView : String := Api.inspect shop shopAfterA 1100

def callsOf (envelope : String) : List Json :=
  match field envelope "calls" with
  | some (.arr xs) => xs.toList
  | _ => []

def objField (j : Json) (key : String) : Option Json :=
  match j with
  | .obj kvs => kvs.find? (·.1 == key) |>.map (·.2)
  | _ => none

#guard (callsOf shopView).map (objField · "call_id") == [some (.str "c1")]
#guard (callsOf shopView).map (objField · "status") == [some (.str "awaiting")]
#guard (callsOf shopView).all fun c => (objField c "request_id").isSome
#guard field shopView "session_id" == some (.str "s1")
#guard field shopView "meters" == some (.arr #[.obj #[("meter", .str "spend"), ("scope", .str "principal"),
  ("used", .str "0"), ("cap", .str "5000"), ("remaining", .str "5000")]])
#guard inputOf (Api.inspect simple shopAfterA 0) == some (.str "state")

end WritTests.Api
