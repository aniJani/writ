import Std.Data.HashSet
import Writ.Json.Jcs
import Writ.Json.Sha256

namespace Writ
namespace Tool

private def member? (kvs : Array (String × JcsValue)) (k : String) : Option JcsValue :=
  (kvs.find? (·.1 == k)).map (·.2)

private def child (base seg : String) : String :=
  if base.isEmpty || seg.startsWith "[" then base ++ seg else base ++ "." ++ seg

/-- The tools of a tools.json document, an MCP `tools/list` result or a bare array of tools, as
(name, tool) pairs in order. Each tool must be an object with a string `name`, unique in the list.
A result's members other than `tools` are ignored, except that `nextCursor` must be a string or
null, null counting as absent. -/
def listOf (doc : JcsValue) : Except String (Array (String × JcsValue)) := do
  let (pre, tools) ← match doc with
    | .arr xs => pure ("", xs)
    | .obj kvs => do
      let xs ← match member? kvs "tools" with
        | some (.arr xs) => pure xs
        | some _ => throw "tools: expected an array"
        | none => throw "tools: missing field"
      if let some c := member? kvs "nextCursor" then
        unless c matches .str _ || c matches .null do throw "nextCursor: expected a string or null"
      pure ("tools", xs)
    | _ => throw "expected an MCP tools/list result or an array of tools"
  let mut out : Array (String × JcsValue) := #[]
  let mut seen : Std.HashSet String := {}
  for h : i in [0:tools.size] do
    let p := child pre s!"[{i}]"
    let tool := tools[i]
    let .obj kvs := tool | throw s!"{p}: expected a tool object"
    let name ← match member? kvs "name" with
      | some (.str n) => pure n
      | some _ => throw s!"{child p "name"}: expected a string"
      | none => throw s!"{child p "name"}: missing field"
    if seen.contains name then throw s!"{child p "name"}: duplicate tool name {Json.quote name}"
    seen := seen.insert name
    out := out.push (name, tool)
  return out

/-- The canonical `writ.tool.v1` preimage of a tool, every member of the tool included. -/
def preimage (tool : JcsValue) : String :=
  (JcsValue.obj #[("t", .str "writ.tool.v1"), ("tool", tool)]).canonical

/-- `writ-tool-v1`: `"sha256:"` plus the lowercase hex SHA-256 of `preimage`. -/
def digest (tool : JcsValue) : String := "sha256:" ++ sha256Hex (preimage tool).toUTF8

/-- The members of the tool's `annotations` object, as the server wrote them; none when it is
absent or not an object. -/
def annotations : JcsValue → List (String × JcsValue)
  | .obj kvs =>
    match member? kvs "annotations" with
    | some (.obj a) => a.toList
    | _ => []
  | _ => []

end Tool
end Writ
