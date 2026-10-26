import WritCli.Common

namespace WritCli

open Writ

def importUsage : String :=
  "usage: writ import mcp <tools.json> [--server <name>] [--preset-dir <dir>] [--out <file>]\n\n" ++
  "Draft a layer-2 policy from an MCP tools/list result or an array of tools. Each tool becomes\n" ++
  "an action that extends the mcp-annotations preset (and mcp-risk-metadata when a tool carries\n" ++
  "SEP-2793 fields) and is labeled at every dimension's strictest value. Annotations are the\n" ++
  "server's untrusted claims: they are copied into source.annotations, never applied, and each\n" ++
  "claim not applied is named on stderr.\n" ++
  "  --server <name>     record this server name in each action's source\n" ++
  "  --preset-dir <dir>  the directory the draft's extends names for the presets (default: presets)\n" ++
  "  --out <file>        write the draft to this file instead of stdout\n\n" ++
  "Exit 0 when the draft is written, 2 for a usage or input error (a file that cannot be read or\n" ++
  "parsed, no tools, a duplicate tool name or a number the digest refuses)."

/-- A preset dimension read from a tool annotation. `claim` is the annotation value that agrees
with `strictest`, the last value of the dimension's order in the preset. -/
structure McpDimension where
  member : String
  label : String
  strictest : String
  claim : JcsValue

structure McpPreset where
  file : String
  dims : List McpDimension

def mcpAnnotations : McpPreset := ⟨"mcp-annotations.json", [
  ⟨"readOnlyHint", "read_only", "false", .bool false⟩,
  ⟨"destructiveHint", "destructive", "true", .bool true⟩,
  ⟨"idempotentHint", "idempotent", "false", .bool false⟩,
  ⟨"openWorldHint", "open_world", "true", .bool true⟩]⟩

def mcpRiskMetadata : McpPreset := ⟨"mcp-risk-metadata.json", [
  ⟨"riskLevel", "risk_level", "critical", .str "critical"⟩,
  ⟨"blastRadius", "blast_radius", "public", .str "public"⟩,
  ⟨"reversibility", "reversibility", "irreversible", .str "irreversible"⟩,
  ⟨"approvalRecommendation", "approval_recommendation", "multi", .str "multi"⟩]⟩

/-- The largest magnitude of a policy integer, as `Json.parse` accepts it. -/
def maxPolicyInt : Nat := 9007199254740991

/-- A member of `source.annotations` sits inside five containers of the draft (the policy,
`actions`, the action, `source`, `annotations`), and a policy nests at most 128. -/
def maxAnnotationDepth : Nat := Json.nestingLimit - 5

private def child (base seg : String) : String :=
  if seg.startsWith "[" then base ++ seg else base ++ "." ++ seg

private def policyInt? (t : String) : Option Int :=
  let (neg, ds) := if t.startsWith "-" then (true, t.drop 1) else (false, t)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else
    let n := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if n > maxPolicyInt then none else some (if neg then -(Int.ofNat n) else Int.ofNat n)

partial def policyJson (path : String) : JcsValue → Except (String × String) Json
  | .null => pure .null
  | .bool b => pure (.bool b)
  | .str s => pure (.str s)
  | .num t => match policyInt? t with
    | some n => pure (.num n)
    | none => throw (path, t)
  | .arr xs => do
    let mut out := #[]
    for h : i in [0:xs.size] do out := out.push (← policyJson (child path s!"[{i}]") xs[i])
    pure (.arr out)
  | .obj kvs => .obj <$> kvs.mapM fun (k, v) => do pure (k, ← policyJson (child path (oneLine k)) v)

/-- The number of containers from `j` down to its deepest leaf, `j` included. -/
partial def depth : Json → Nat
  | .arr xs => 1 + xs.foldl (fun m x => max m (depth x)) 0
  | .obj kvs => 1 + kvs.foldl (fun m kv => max m (depth kv.2)) 0
  | _ => 0

/-- JSON as `JSON.stringify(j, null, 2)` writes it, with canonical string escapes. -/
partial def pretty (j : Json) (indent : String := "") : String :=
  let inner := indent ++ "  "
  let block (open_ close : String) (items : List String) :=
    if items.isEmpty then open_ ++ close
    else open_ ++ "\n" ++ ",\n".intercalate (items.map (inner ++ ·)) ++ "\n" ++ indent ++ close
  match j with
  | .arr xs => block "[" "]" (xs.toList.map (pretty · inner))
  | .obj kvs => block "{" "}" (kvs.toList.map fun (k, v) => Json.quote k ++ ": " ++ pretty v inner)
  | j => j.compact

/-- The most characters of a claim's value a stderr line echoes. -/
def maxEchoChars : Nat := 200

private def clip (s : String) : String :=
  if s.length > maxEchoChars then (s.take maxEchoChars).toString ++ "..." else s

private def member? (kvs : Array (String × JcsValue)) (k : String) : Option JcsValue :=
  (kvs.find? (·.1 == k)).map (·.2)

structure DraftAction where
  json : Json
  /-- One line per server claim the draft does not apply and per annotation member it leaves out. -/
  notes : Array String

/-- The draft action for one tool: every dimension of `presets` at its strictest value, and the
tool's digest and annotations (those a policy can hold) in `source`. -/
def draftAction (presets : List McpPreset) (server? : Option String) (name : String)
    (tool : JcsValue) : DraftAction := Id.run do
  let shown := oneLine name
  let kvs := match tool with
    | .obj kvs => kvs
    | _ => #[]
  let mut notes : Array String := #[]
  let mut annotations? : Option (Array (String × Json)) := none
  match member? kvs "annotations" with
  | none => pure ()
  | some (.obj anns) =>
    let mut kept := #[]
    for (k, v) in anns do
      match policyJson (oneLine k) v with
      | .error (p, t) =>
        notes := notes.push <| s!"{shown}: source.annotations leaves out {oneLine k}: {p} is {t}, " ++
          "which a policy cannot hold (integers within plus or minus (2^53 - 1) only)"
      | .ok j =>
        if depth j > maxAnnotationDepth then
          notes := notes.push <| s!"{shown}: source.annotations leaves out {oneLine k}: " ++
            s!"it nests more than {maxAnnotationDepth} levels, too deep for a policy"
        else kept := kept.push (k, j)
    annotations? := some kept
  | some _ =>
    notes := notes.push s!"{shown}: annotations is not an object, so source.annotations is left out"
  let claims := Tool.annotations tool
  let mut labels : Array (String × Json) := #[]
  for p in presets do
    for d in p.dims do
      labels := labels.push (d.label, .str d.strictest)
      if let some v := claims.lookup d.member then
        if v != d.claim then
          notes := notes.push <| s!"{shown}: the server says {d.member} {clip v.canonical}; " ++
            s!"{d.label} left \"{d.strictest}\" (lower it after review)"
  let source : Array (String × Json) := #[("tool_digest", .str (Tool.digest tool))] ++
    (server?.map fun s => #[("server", .str s)]).getD #[] ++
    (annotations?.map fun a => #[("annotations", .obj a)]).getD #[]
  pure ⟨.obj #[("labels", .obj labels), ("source", .obj source)], notes⟩

/-- The presets a draft extends: `mcp-annotations`, and `mcp-risk-metadata` when some tool's
annotations carry a SEP-2793 field. -/
def draftPresets (tools : Array (String × JcsValue)) : List McpPreset :=
  let risk := tools.any fun (_, t) =>
    (Tool.annotations t).any fun (k, _) => mcpRiskMetadata.dims.any (·.member == k)
  if risk then [mcpAnnotations, mcpRiskMetadata] else [mcpAnnotations]

def draft (tools : Array (String × JcsValue)) (server? : Option String) (presetDir : String) :
    Json × Array String :=
  let presets := draftPresets tools
  let sep (d : String) := if d.endsWith "/" then d else d ++ "/"
  let acts := tools.map fun (n, t) => (n, draftAction presets server? n t)
  let doc := Json.obj #[
    ("writ", .str "0.1"),
    ("extends", .arr (presets.map fun p => Json.str (sep presetDir ++ p.file)).toArray),
    ("approver_roles", .arr #[.str "owner"]),
    ("actions", .obj (acts.map fun (n, a) => (n, a.json)))]
  (doc, acts.flatMap (·.2.notes))

def importCmd (args : List String) : Cli UInt32 := do
  let a ← parseArgs ["--server", "--preset-dir", "--out"] args
  let path ← match a.pos.toList with
    | ["mcp", path] => pure path
    | "mcp" :: _ => usageError "expected exactly one tools.json file"
    | [] => usageError "expected a source: mcp"
    | s :: _ => usageError s!"unknown source {s}, expected mcp"
  let server? := a.opt? "--server"
  checkServerOpt server?
  let dir := (a.opt? "--preset-dir").getD "presets"
  if dir.isEmpty then usageError "--preset-dir needs a non-empty directory"
  let tools ← readTools path
  let (policy, notes) := draft tools server? dir
  let text := pretty policy ++ "\n"
  match a.opt? "--out" with
  | some out => liftIO (IO.FS.writeFile out text) s!"{out}: cannot write the file"
  | none => do
    let o ← IO.getStdout
    o.putStr text
    o.flush
  for n in notes do IO.eprintln n
  pure 0

end WritCli
