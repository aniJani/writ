import Writ
import WritTests.JsonHelpers
import WritTests.Corpus

open Writ

namespace WritTests.Layer2Codec

/-- The example of `docs/design.md` section 5, with the `"writ": "0.1"` every policy document carries. -/
def specLayer2 : String := "{
  \"writ\": \"0.1\",
  \"extends\": [\"org-baseline.json\"],
  \"labels\": { \"risk\": { \"order\": [\"read\", \"navigate\", \"device\", \"spend\", \"destructive\"] } },
  \"rules\": [
    { \"when\": { \"risk\": \">=device\" }, \"require\": { \"consent\": \"per_call\" } },
    { \"when\": { \"risk\": \">=destructive\" }, \"require\": { \"exposed\": false } }
  ],
  \"actions\": { \"vm.restart\": { \"labels\": { \"risk\": \"device\" }, \"permission\": \"vm.power\" } }
}"

def err2 (text : String) : String :=
  match Policy2.parseDoc text with
  | .ok _ => ""
  | .error e => e

def err1 (text : String) : String :=
  match Policy.parseDoc text with
  | .ok _ => ""
  | .error e => e

def parsed (text : String) : Policy2 := ((Policy2.parseDoc text).toOption.map (·.1)).getD {}

def doc (body : String) : String := "{\"writ\":\"0.1\"," ++ body ++ "}"

def ruleDoc (rule : String) : String := doc ("\"rules\":[" ++ rule ++ "]")

#guard (Policy2.parseDoc specLayer2).isOk
#guard (parsed specLayer2).«extends» == ["org-baseline.json"]
#guard (parsed specLayer2).labels == [("risk", ⟨["read", "navigate", "device", "spend", "destructive"]⟩)]
#guard (parsed specLayer2).rules ==
  [⟨[("risk", "device")], { consent := some .perCall }⟩, ⟨[("risk", "destructive")], { exposed := some false }⟩]
#guard (parsed specLayer2).actions.map (·.1) == ["vm.restart"]
#guard (parsed specLayer2).actions.map (·.2.labels) == [[("risk", "device")]]
#guard (parsed specLayer2).actions.map (·.2.req.permission) == [some "vm.power"]
#guard (parsed specLayer2).base == {}
#guard (Policy2.parseDoc specLayer2).map (isLayer2 ·.2) == .ok true

#guard err2 (ruleDoc "{\"when\":{\"risk\":\">=read\"},\"require\":{}},{\"when\":{\"risk\":\"device\"},\"require\":{}}")
  == "rules[1].when.risk: expected \">=value\""
#guard err2 (ruleDoc "{\"when\":{\"risk\":\">=\"},\"require\":{}}") == "rules[0].when.risk: expected \">=value\""
#guard err2 (ruleDoc "{\"when\":{\"risk\":3},\"require\":{}}") == "rules[0].when.risk: expected \">=value\""
#guard err2 (doc "\"labels\":{\"risk\":{\"order\":[\"read\",\"device\",\"read\"]}}")
  == "labels.risk.order: duplicate value \"read\""
#guard err2 (doc "\"labels\":{\"risk\":{\"order\":[]}}") == "labels.risk.order: expected at least one value"
#guard err2 (doc "\"labels\":{\"risk\":{\"ordr\":[\"read\"]}}") == "labels.risk.ordr: unknown field"
#guard err2 (doc "\"labels\":{\"risk\":{}}") == "labels.risk.order: missing field"
#guard err2 (ruleDoc "{\"when\":{},\"require\":{\"permission\":\"x\"}}")
  == "rules[0].require.permission: not a strictness-ordered field"
#guard ["permission", "consent_if_cost_over", "escalate", "max_attempts", "meters", "approval_ttl_ms",
    "authorized_ttl_ms", "review", "messages", "source"].all fun f =>
  err2 (ruleDoc ("{\"when\":{},\"require\":{\"" ++ f ++ "\":1}}"))
    == "rules[0].require." ++ f ++ ": not a strictness-ordered field"
#guard err2 (ruleDoc "{\"when\":{},\"require\":{\"labels\":{}}}") == "rules[0].require.labels: unknown field"
#guard err2 (ruleDoc "{\"when\":{},\"require\":{\"consnet\":\"per_call\"}}") == "rules[0].require.consnet: unknown field"
#guard err2 (ruleDoc "{\"require\":{}}") == "rules[0].when: missing field"
#guard err2 (ruleDoc "{\"when\":{}}") == "rules[0].require: missing field"
#guard err2 (ruleDoc "{\"when\":{},\"require\":{},\"name\":\"x\"}") == "rules[0].name: unknown field"
#guard err2 (doc "\"rules\":{}") == "rules: expected an array"
#guard err2 (doc "\"extends\":[\"a.json\",1]") == "extends[1]: expected a string"
#guard err2 (doc "\"extends\":[\"\"]") == "extends[0]: expected a non-empty path"
#guard err2 (doc "\"actions\":{\"a\":{\"labels\":{\"risk\":1}}}") == "actions.a.labels.risk: expected a string"
#guard err2 (doc "\"actions\":{\"a\":{\"labels\":{},\"consnet\":\"none\"}}") == "actions.a.consnet: unknown field"
#guard err2 (doc "\"rules\":[],\"actions\":{\"a\":{\"consent\":\"always\"}}")
  == "actions.a.consent: unknown value, expected \"none\", \"per_call\" or an object"
#guard err2 "{\"rules\":[]}" == "writ: missing field"
#guard err2 (doc "\"rules\":[],\"lables\":{}") == "lables: unknown field"
#guard err2 "[]" == "expected an object"

#guard (parsed (ruleDoc "{\"when\":{},\"require\":{\"grantable\":null}}")).rules.map (·.require.grantable)
  == [some .forbid]
#guard (parsed (ruleDoc "{\"when\":{},\"require\":{\"grantable\":{\"max_uses\":5,\"scope\":\"turn\"}}}")).rules.map
    (·.require.grantable)
  == [some (.cap (some .turn) (some 5) none none)]
#guard err2 (ruleDoc "{\"when\":{},\"require\":{\"grantable\":{\"allow_any_args_metered\":true}}}")
  == "rules[0].require.grantable.allow_any_args_metered: unknown field"
#guard err2 (ruleDoc "{\"when\":{},\"require\":{\"grantable\":3}}") == "rules[0].require.grantable: expected null or an object"
#guard (parsed (ruleDoc ("{\"when\":{\"risk\":\">=spend\",\"data\":\">=private\"},\"require\":{\"consent\":{\"quorum\":2}," ++
    "\"exposed\":false,\"idempotent\":false,\"retry_after_unknown\":false,\"guards\":[\"g\"],\"flags\":[\"sends_external\"]," ++
    "\"mode\":\"enforce\"}}"))).rules ==
  [⟨[("risk", "spend"), ("data", "private")],
    { consent := some (.quorum 2 none true false), exposed := some false, idempotent := some false,
      retryAfterUnknown := some false, guards := ["g"], flags := [.sendsExternal], mode := some .enforce }⟩]

/-! Review Focus 5: a misspelled layer-2 key is not layer 2, and stays an unknown field. -/
def misspelled : String := doc "\"actions\":{\"a\":{\"label\":{\"risk\":\"read\"}}}"
#guard (Json.parse misspelled).map isLayer2 == .ok false
#guard err1 misspelled == "actions.a.label: unknown field"
#guard err2 misspelled == "actions.a.label: unknown field"

/-! The kernel's parser still refuses every layer-2 key. -/
#guard err1 specLayer2 == "extends: unknown field"
#guard err1 (doc "\"labels\":{}") == "labels: unknown field"
#guard err1 (doc "\"rules\":[]") == "rules: unknown field"
#guard err1 (doc "\"actions\":{\"a\":{\"labels\":{}}}") == "actions.a.labels: unknown field"
#guard [doc "\"labels\":{}", doc "\"rules\":[]", doc "\"extends\":[]", doc "\"actions\":{\"a\":{\"labels\":{}}}"].all
  fun t => (Json.parse t).map isLayer2 == .ok true
#guard [doc "\"actions\":{}", doc "\"actions\":{\"a\":{}}", "[]", doc "\"actions\":[]"].all
  fun t => (Json.parse t).map isLayer2 == .ok false

def layer1Docs : List Json :=
  ((Json.parse WritTests.Corpus.assistantJson).toOption.toList) ++
    WritTests.Corpus.files.flatMap fun (_, text) => (WritTests.Corpus.tracesOf text).map (·.policyDoc)

#guard layer1Docs.length > 20
#guard layer1Docs.all (!isLayer2 ·)

/-! A layer-1 document reads as layer 2 with the same policy-level fields and actions, and no labels. -/
#guard layer1Docs.all fun j =>
  match (decode j : Except DecodeError Policy), (decode j : Except DecodeError Policy2) with
  | .ok p, .ok q =>
    q.base == { p with actions := [] } && q.actions.map (·.1) == p.actions.map (·.1) &&
      q.actions.all (fun (n, a) => a.labels.isEmpty && p.action? n == some a.req) &&
      q.«extends».isEmpty && q.labels.isEmpty && q.rules.isEmpty
  | _, _ => false

#guard Policy.toJsonText { actions := [("a", { consent := .perCall })], approverRoles := ["owner"] } ==
  "{\"actions\":{\"a\":{\"consent\":\"per_call\"}},\"approver_roles\":[\"owner\"],\"writ\":\"0.1\"}"
#guard Policy.toJsonText {} == "{\"writ\":\"0.1\"}"
#guard layer1Docs.all fun j =>
  match (decode j : Except DecodeError Policy) with
  | .ok p =>
    (Policy.parseDoc (Policy.toJsonText p)).map (Policy.toJsonText ·.1) == .ok (Policy.toJsonText p) &&
      (decode (toJson p) : Except DecodeError Policy) == .ok p
  | .error _ => false

def roundTrips2 (q : Policy2) : Bool :=
  (decode (toJson q) : Except DecodeError Policy2) == .ok q &&
    (Policy2.parseDoc (toJson q).compact).map (·.1) == .ok q

#guard roundTrips2 (parsed specLayer2)
#guard roundTrips2 (parsed (ruleDoc ("{\"when\":{\"risk\":\">=spend\"},\"require\":{\"grantable\":null,\"exposed\":true}}," ++
  "{\"when\":{},\"require\":{\"grantable\":{\"scope\":\"session\",\"max_duration_ms\":10,\"any_args\":false}," ++
  "\"consent\":\"none\",\"flags\":[\"reads_private\"],\"mode\":\"log_only\"}}")))
#guard layer1Docs.all fun j => match (decode j : Except DecodeError Policy2) with
  | .ok q => roundTrips2 q
  | .error _ => false

end WritTests.Layer2Codec
