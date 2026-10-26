import Writ
import WritTests.JsonHelpers

open Writ

namespace WritTests.Tool

def vectorsText : String := include_str "../corpus/digests/tool-v1.jsonl"

def field (j : Json) (k : String) : Option String :=
  match j with
  | .obj kvs => match kvs.find? (·.1 == k) with
    | some (_, .str s) => some s
    | _ => none
  | _ => none

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The id of a vector Lean does not meet, with what it got. -/
def check (line : String) : Option String :=
  match Json.parse line with
  | .error e => some s!"unreadable vector line: {e}"
  | .ok j =>
    let id := (field j "id").getD "?"
    let got := Jcs.parse ((field j "tool_text").getD "") >>= Tool.listOf
    match field j "error_contains", got with
    | some want, .error e => if contains e want then none else some s!"{id}: error {e}"
    | some _, .ok _ => some s!"{id}: accepted"
    | none, .error e => some s!"{id}: refused: {e}"
    | none, .ok #[(_, tool)] =>
      if field j "canonical" != some (Tool.preimage tool) then some s!"{id}: canonical {Tool.preimage tool}"
      else if field j "digest" != some (Tool.digest tool) then some s!"{id}: digest {Tool.digest tool}"
      else none
    | none, .ok ts => some s!"{id}: {ts.size} tools"

def lines : List String := (vectorsText.splitOn "\n").filter (· != "")

#guard lines.length ≥ 40
#guard lines.filterMap check == []

def toolsOf (text : String) : Except String (Array (String × JcsValue)) := Jcs.parse text >>= Tool.listOf

#guard (toolsOf "[{\"name\":\"b\"},{\"name\":\"a\"}]").map (·.map (·.1)) == .ok #["b", "a"]
#guard (toolsOf "{\"tools\":[]}").map (·.size) == .ok 0
#guard toolsOf "{\"tools\":[],\"nextCursor\":1}" == .error "nextCursor: expected a string or null"
#guard (toolsOf "{\"tools\":[{\"name\":\"a\"}],\"nextCursor\":null}").map (·.size) == .ok 1
#guard (toolsOf "{\"tools\":[{\"name\":\"a\"}],\"nextCursor\":\"p2\"}").map (·.size) == .ok 1
#guard toolsOf "{\"tools\":{}}" == .error "tools: expected an array"
#guard (toolsOf "{\"tools\":[{\"name\":\"a\"}],\"_meta\":[],\"x\":{\"y\":1e999}}").map (·.size) == .error
  "x.y: number is outside 1e-300 to 1e300 in magnitude at line 1, column 45"
#guard (toolsOf "{\"tools\":[{\"name\":\"a\"}],\"_meta\":[],\"x\":{\"y\":1}}").map (·.size) == .ok 1
#guard toolsOf "[1]" == .error "[0]: expected a tool object"
#guard toolsOf "\"x\"" == .error "expected an MCP tools/list result or an array of tools"
#guard toolsOf "{\"tools\":[{\"name\":\"a\"},{\"name\":\"a\"}]}" == .error "tools[1].name: duplicate tool name \"a\""

def annotationsOf (text : String) : List (String × JcsValue) :=
  match toolsOf text with
  | .ok #[(_, t)] => Tool.annotations t
  | _ => [("unparsed", .null)]

#guard annotationsOf "[{\"name\":\"a\",\"annotations\":{\"readOnlyHint\":true,\"riskLevel\":\"high\"}}]"
  == [("readOnlyHint", .bool true), ("riskLevel", .str "high")]
#guard annotationsOf "[{\"name\":\"a\"}]" == []
#guard annotationsOf "[{\"name\":\"a\",\"annotations\":[]}]" == []

def num (text : String) : Except String String :=
  match Jcs.parse text with
  | .ok (.num t) => .ok t
  | .ok v => .error s!"not a number: {v.canonical}"
  | .error e => .error e

#guard num "0.5" == .ok "0.5"
#guard num "1.5e3" == .ok "1500"
#guard num "-0" == .ok "0"
#guard num "-0.0e-5" == .ok "0"
#guard num "1E-7" == .ok "1e-7"
#guard num "1e-6" == .ok "0.000001"
#guard num "100" == .ok "100"
#guard num "2.0" == .ok "2"
#guard num "1e21" == .ok "1e+21"
#guard num "123456789012345678900" == .error "number has more than 15 significant digits at line 1, column 1"
#guard num "100000000000000000000" == .ok "100000000000000000000"
#guard num "-1.5E+2" == .ok "-150"
#guard num "0.00001234" == .ok "0.00001234"
#guard num "1.234e-7" == .ok "1.234e-7"
#guard num "9.99999999999999e299" == .ok "9.99999999999999e+299"
#guard num "1e300" == .ok "1e+300"
#guard num "1.00000000000001e300" == .error "number is outside 1e-300 to 1e300 in magnitude at line 1, column 1"
#guard num "1e-300" == .ok "1e-300"
#guard num "0.1e-299" == .ok "1e-300"
#guard num "9.99999999999999e-301" == .error "number is outside 1e-300 to 1e300 in magnitude at line 1, column 1"
#guard num ("0." ++ String.ofList (List.replicate 1000 '0') ++ "1") == .error "number is outside 1e-300 to 1e300 in magnitude at line 1, column 1"
#guard num ("1" ++ String.ofList (List.replicate 100 '0') ++ ".000") == .ok "1e+100"
#guard (num "01").isOk == false
#guard (num "1.").isOk == false
#guard (num "1e").isOk == false
#guard (num "+1").isOk == false
#guard (num ".5").isOk == false

#guard Jcs.parse "{\"a\":[1,{\"b\":1e999}]}" == .error "a[1].b: number is outside 1e-300 to 1e300 in magnitude at line 1, column 14"
#guard Jcs.parse "{\"a\":{\"b\":1,\"b\":2}}" == .error "a.b: duplicate key \"b\" at line 1, column 13"
#guard Jcs.parse "{\"a\":[\"\\ud800\"]}" == .error "a[0]: lone surrogate at line 1, column 8"
#guard Jcs.parse "\uFEFF{}" == .error "byte order mark at start of input is not allowed"
#guard (Jcs.parse "{} x").isOk == false
#guard (Jcs.parse (String.ofList (List.replicate 128 '[') ++ String.ofList (List.replicate 128 ']'))).isOk
#guard (Jcs.parse (String.ofList (List.replicate 129 '[') ++ String.ofList (List.replicate 129 ']'))).isOk == false

/-- On integer-only JSON, `Jcs` agrees with the policy parser and printer. -/
def agrees (text : String) : Bool :=
  match Jcs.parse text, Json.parse text with
  | .ok v, .ok j => v.canonical == j.canonical
  | _, _ => false

#guard agrees "{\"\\uffff\":1,\"\\ud83d\\ude00\":[-2,{\"z\":\"\\u001f\",\"é\":null}],\"a\":true}"
#guard agrees "[\"\\u007f\\u2028/\\\"\\\\\\b\\f\\n\\r\\t\"]"

end WritTests.Tool
