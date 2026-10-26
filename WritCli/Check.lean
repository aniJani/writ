import WritCli.Expand
import Writ.Profile.McpToolApproval

namespace WritCli

open Writ

def checkUsage : String :=
  "usage: writ check <policy.json> [--json] [--tools <tools.json> [--server <name>]] [--profile <id>]\n\n" ++
  "Parse and decode a policy, then report its problems and warnings.\n" ++
  "  --json                print one JSON object instead of text\n" ++
  "  --tools <tools.json>  compare each action's source.tool_digest with this MCP tool list:\n" ++
  "                        a changed tool is an error (tool_changed); a tool not listed, listed\n" ++
  "                        but pinned by no compared source, or named by no action is a warning\n" ++
  "                        (tool_missing, tool_unpinned, tool_unlisted)\n" ++
  "  --server <name>       with --tools, compare only actions whose source.server is this name\n" ++
  "  --profile <id>        also report the settings a standards profile forbids; the one profile is\n" ++
  "                        mcp-tool-approval (MCP SEP-2848): retry_after_unknown is an error\n" ++
  "                        (profile_retry_after_unknown), max_attempts above 1 a warning\n" ++
  "                        (profile_max_attempts)\n\n" ++
  "Exit 0 when there are no errors, 1 when there are errors, 2 when a file cannot be read, parsed or decoded."

def digestUsage : String :=
  "usage: writ digest <policy.json>\n\nPrint the policy digest (sha256 of the canonical JSON as written)."

private def str? : Option Json → Option String
  | some (.str s) => some s
  | _ => none

/-- The tool an action is for: `source.tool`, else the action name, with the `source` that pins
it, if any. -/
structure ActionTool where
  action : String
  tool : String
  server? : Option String := none
  digest? : Option String := none

/-- Each action of a decoded policy document, in document order. -/
def actionTools (doc : Json) : List ActionTool :=
  match field? doc "actions" with
  | some (.obj acts) => acts.toList.map fun (n, a) =>
    match field? a "source" with
    | some s =>
      { action := n, tool := (str? (field? s "tool")).getD n, server? := str? (field? s "server"),
        digest? := str? (field? s "tool_digest") }
    | none => { action := n, tool := n }
  | _ => []

/-- The `writ check --tools` findings, errors then warnings: each compared action's tool missing
from `tools` or with another digest, then each tool of `tools` that no compared action pins,
unpinned when some other action allows it and unlisted otherwise. -/
def toolFindings (tools : Array (String × JcsValue)) (server? : Option String) (doc : Json) :
    List (String × Json) × List (String × Json) := Id.run do
  let all := actionTools doc
  let compared := all.filter fun a => a.digest?.isSome && server?.all (a.server? == some ·)
  let mut errors := #[]
  let mut warnings := #[]
  for a in compared do
    match tools.find? (·.1 == a.tool) with
    | none =>
      warnings := warnings.push <|
        finding "warning" "tool_missing" s!"tool \"{a.tool}\" is not in the tool list" (some a.action)
    | some (_, t) =>
      let now := Tool.digest t
      let old := a.digest?.getD ""
      if now != old then
        errors := errors.push <| finding "error" "tool_changed"
          (s!"tool \"{a.tool}\" changed: source.tool_digest is {old}, " ++
            s!"the tool list has {now}") (some a.action)
  for (n, _) in tools do
    if compared.any (·.tool == n) then continue
    -- The kernel matches a call's tool against action names and ignores source, so an action
    -- named n allows tool n even when its source.tool names another tool.
    let allowing := all.filter fun a => a.tool == n || a.action == n
    if allowing.isEmpty then
      warnings := warnings.push <| finding "warning" "tool_unlisted"
        (s!"tool \"{n}\" is in the tool list but no action names it (by name or source.tool), " ++
          "so default deny refuses it") none
    for a in allowing do
      let why := if a.tool != n then s!"its source pins tool \"{a.tool}\"" else
        match a.digest?, server? with
        | some _, some sv =>
          s!"its source is not for server \"{sv}\", so this check cannot detect changes to the tool"
        | _, _ => "records no source.tool_digest, so writ cannot detect changes to the tool"
      warnings := warnings.push <|
        finding "warning" "tool_unpinned" s!"it allows tool \"{n}\" but {why}" (some a.action)
  (errors.toList, warnings.toList)

def checkLayer1 (path : String) (doc : Json) : Cli CheckResult := do
  let policy : Policy ← decodeFile path doc
  pure {
    errors := policy.check.map fun p => finding "error" p.code p.message p.action?
    warnings := (policy.warnings ++ messageWarnings doc).map fun w =>
      finding "warning" w.code w.message w.action?
    digest? := some doc.digest
    doc? := some doc }

/-- The profile findings for the policy the kernel runs (`doc`, decoded), errors then warnings. -/
def profileFindings (doc : Json) : List (String × Json) × List (String × Json) :=
  match (decode doc : Except DecodeError Policy) with
  | .error _ => ([], [])
  | .ok policy =>
    let ps := Profile.McpToolApproval.problems policy
    let f (kind : String) (q : Profile.McpToolApproval.Problem) := finding kind q.code q.message q.action?
    ((ps.filter (·.isError)).map (f "error"), (ps.filter (!·.isError)).map (f "warning"))

def checkProfile (id : String) : Cli Unit :=
  unless id == Profile.McpToolApproval.id do
    usageError s!"unknown profile \"{id}\", expected {Profile.McpToolApproval.id}"

def report (r : CheckResult) (json : Bool) : IO UInt32 := do
  if json then
    let fields : Array (String × Json) := #[("ok", Json.bool r.errors.isEmpty),
      ("errors", Json.arr (r.errors.map (·.2)).toArray),
      ("warnings", Json.arr (r.warnings.map (·.2)).toArray)]
    rawLine (Json.obj (fields ++ (r.digest?.map fun d => #[("policy_digest", Json.str d)]).getD #[])).compact
  else
    for (t, _) in r.errors ++ r.warnings do stdoutLine t
    stdoutLine <|
      if r.errors.isEmpty && r.warnings.isEmpty then "ok"
      else s!"{plural r.errors.length "error" "errors"}, {plural r.warnings.length "warning" "warnings"}"
  pure (if r.errors.isEmpty then 0 else 1)

def check (args : List String) : Cli UInt32 := do
  let json := args.contains "--json"
  let a ← parseArgs ["--tools", "--server", "--profile"] (args.filter (· != "--json"))
  let [path] := a.pos.toList | usageError "expected exactly one policy file"
  let server? := a.opt? "--server"
  let tools? := a.opt? "--tools"
  if server?.isSome && tools?.isNone then usageError "--server needs --tools"
  checkServerOpt server?
  let profile? := a.opt? "--profile"
  if let some id := profile? then checkProfile id
  let doc ← parseJsonFile path (← readText path)
  let r ← if isLayer2 doc then checkLayer2 path doc else checkLayer1 path doc
  let r ← match tools? with
    | none => pure r
    | some tp => do
      let tools ← readTools tp
      let (es, ws) := (r.doc?.map (toolFindings tools server?)).getD ([], [])
      pure { r with errors := r.errors ++ es, warnings := r.warnings ++ ws }
  let r := match profile?, r.doc? with
    | some _, some d =>
      let (es, ws) := profileFindings d
      { r with errors := r.errors ++ es, warnings := r.warnings ++ ws }
    | _, _ => r
  report r json

def digest (args : List String) : Cli UInt32 := do
  let a ← parseArgs [] args
  let [path] := a.pos.toList | usageError "expected exactly one policy file"
  let { doc, .. } ← loadPolicy path
  stdoutLine doc.digest
  pure 0

end WritCli
