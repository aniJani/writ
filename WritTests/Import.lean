import Writ
import WritCli.Import

open Writ WritCli

namespace WritTests.Import

def annotationsPreset : String := include_str "../schema/presets/mcp-annotations.json"
def riskMetadataPreset : String := include_str "../schema/presets/mcp-risk-metadata.json"

/-- Each dimension of the preset file with the last value of its order. -/
def strictestOf (text : String) : List (String × String) :=
  match Policy2.parseDoc text with
  | .ok (p, _) => p.labels.map fun (d, o) => (d, o.order.getLast?.getD "")
  | .error _ => []

def table (p : McpPreset) : List (String × String) := p.dims.map fun d => (d.label, d.strictest)

-- The hard-coded strictest values cannot drift from the preset files.
#guard (strictestOf annotationsPreset).length == 4
#guard table mcpAnnotations == strictestOf annotationsPreset
#guard table mcpRiskMetadata == strictestOf riskMetadataPreset
#guard [mcpAnnotations, mcpRiskMetadata].all fun p =>
  p.dims.all fun d => d.claim == .bool (d.strictest == "true") || d.claim == .str d.strictest

def toolsOf (text : String) : Array (String × JcsValue) :=
  (Jcs.parse text >>= Tool.listOf).toOption.getD #[]

def draftOf (text : String) : Json × Array String := draft (toolsOf text) none "presets"

def parses (text : String) : Bool := (Policy2.parseDoc text).isOk

def nested (n : Nat) : String := String.ofList (List.replicate n '[') ++ String.ofList (List.replicate n ']')

/-- A tools/list result whose one tool has an annotation `deep` nested `n` arrays deep. -/
def deepTool (n : Nat) : String :=
  "{\"tools\":[{\"name\":\"t\",\"annotations\":{\"deep\":" ++ nested n ++ "}}]}"

#guard (toolsOf (deepTool 124)).size == 1
#guard (draftOf (deepTool 123)).2 == #[]
#guard parses (pretty (draftOf (deepTool 123)).1)
#guard (draftOf (deepTool 124)).2 ==
  #["t: source.annotations leaves out deep: it nests more than 123 levels, too deep for a policy"]
#guard parses (pretty (draftOf (deepTool 124)).1)

def numbersOut : String := include_str "../tests/cli/import-numbers.out"

#guard parses numbersOut

-- maxPolicyInt is the policy parser's own limit.
#guard (Json.parse (toString maxPolicyInt)).isOk
#guard (Json.parse ("-" ++ toString maxPolicyInt)).isOk
#guard (Json.parse (toString (maxPolicyInt + 1))).isOk == false
#guard (Json.parse ("-" ++ toString (maxPolicyInt + 1))).isOk == false

def pj (v : JcsValue) : String :=
  match policyJson "a" v with
  | .ok j => j.compact
  | .error (p, t) => s!"{p} is {t}"

#guard pj (.num "-0") == "0"
#guard pj (.num "-999999999999999") == "-999999999999999"
#guard pj (.num "9007199254740991") == "9007199254740991"
#guard pj (.num "9007199254740992") == "a is 9007199254740992"
#guard pj (.num "1e+21") == "a is 1e+21"
#guard pj (.arr #[.num "1", .obj #[("b", .num "0.5")]]) == "a[1].b is 0.5"
#guard pj (.obj #[("b\nc", .num "0.5")]) == "a.b\\nc is 0.5"

-- Claims that agree with the strictest value are applied silently; the rest are named.
#guard (draftOf "[{\"name\":\"t\",\"annotations\":{\"readOnlyHint\":false,\"destructiveHint\":true}}]").2 == #[]
#guard (draftOf "[{\"name\":\"t\",\"annotations\":{\"openWorldHint\":null}}]").2 ==
  #["t: the server says openWorldHint null; open_world left \"true\" (lower it after review)"]

#guard (draftOf ("[{\"name\":\"t\",\"annotations\":{\"readOnlyHint\":\"" ++ String.ofList (List.replicate 300 'x') ++ "\"}}]")).2 ==
  #["t: the server says readOnlyHint \"" ++ String.ofList (List.replicate 199 'x') ++ "...; read_only left \"false\" (lower it after review)"]

-- Without a SEP-2793 field anywhere, the draft extends only mcp-annotations.
#guard (draftPresets (toolsOf "[{\"name\":\"t\",\"annotations\":{\"readOnlyHint\":true}}]")).map (·.file)
  == ["mcp-annotations.json"]
#guard (draftPresets (toolsOf "[{\"name\":\"a\"},{\"name\":\"b\",\"annotations\":{\"riskLevel\":\"low\"}}]")).map
  (·.file) == ["mcp-annotations.json", "mcp-risk-metadata.json"]

#guard pretty (.obj #[]) == "{}"
#guard pretty (.obj #[("a", .arr #[]), ("b", .arr #[.num 1, .str "x\n"])]) ==
  "{\n  \"a\": [],\n  \"b\": [\n    1,\n    \"x\\n\"\n  ]\n}"

end WritTests.Import
