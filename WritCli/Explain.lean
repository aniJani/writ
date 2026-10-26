import WritCli.Common
import WritCli.Replay
import Writ.Profile.McpToolApproval

namespace WritCli

open Writ

def explainUsage : String :=
  "usage: writ explain <traces.jsonl> [--id <id>] [--profile <id>]\n\n" ++
  "Replay the traces and print one line per step: the event, then the verdict, decision,\n" ++
  "reason code, retry class and the user-facing message when there is a reason.\n" ++
  "  --id <id>        only the trace with this id\n" ++
  "  --profile <id>   under each step, the standards profile's view: for mcp-tool-approval\n" ++
  "                   (MCP SEP-2848), the SEP disposition of each call the step made terminal\n" ++
  "                   and the SEP-2643 envelope of the verdict when it has one\n\n" ++
  "Exit 0, or 2 when the file cannot be read or parsed or no trace has the given id."

private def eventFields (ev : Event) : Array (String × Json) :=
  match toJson ev with | .obj kvs => kvs | _ => #[]

private def eventSummary (ev : Event) : String :=
  let fields := eventFields ev
  let keys := ["call_id", "tool", "approver", "outcome"]
  let shown := keys.filterMap fun k =>
    (fields.find? (·.1 == k)).bind fun (_, v) =>
      match v with | .str s => some s!"{k}={s}" | _ => none
  " ".intercalate (ev.body.typeName :: shown)

private def verdictSummary (v : Verdict) : String :=
  let reason? := match v with
    | .ok d _ => d.reason?
    | .rejected r => some r
  let head := match v with
    | .ok d _ => s!"accepted {d.code.getD "none"}"
    | .rejected _ => "rejected"
  match reason? with
  | some r => s!"{head} (reason {r.code}, retry {r.retry.code}): {r.userMessage}"
  | none => head

/-- The profile lines under a step: the disposition of every call whose status became terminal in
the step, a call ended by `kill`, `reset` or `session_end` included, then the verdict's envelope. -/
private def profileLines (before after : State) (v : Verdict) : List String :=
  let ended := after.calls.toList.filterMap fun (k, r) =>
    if r.status.terminal && (before.calls[k]?.map (·.status)) != some r.status then
      (Profile.McpToolApproval.disposition r.status).map fun d => s!"      disposition call_id={k} {d}"
    else none
  let envelope := match Profile.McpToolApproval.envelope v with
    | some e => [s!"      envelope {e.compact}"]
    | none => []
  ended ++ envelope

def explain (args : List String) : Cli UInt32 := do
  let a ← parseArgs ["--id", "--profile"] args
  let [path] := a.pos.toList | usageError "expected exactly one trace file"
  let profile := (a.opt? "--profile").isSome
  if let some id := a.opt? "--profile" then
    unless id == Profile.McpToolApproval.id do
      usageError s!"unknown profile \"{id}\", expected {Profile.McpToolApproval.id}"
  let all ← loadTraces path
  let traces := match a.opt? "--id" with
    | some id => all.filter fun (t : Trace) => t.id == id
    | none => all
  if traces.isEmpty then
    failWith s!"{path}: no trace{(a.opt? "--id").map (s!" with id {·}") |>.getD ""}"
  for t in traces do
    stdoutLine <| match t.description with
      | some d => s!"trace {t.id}: {d}"
      | none => s!"trace {t.id}"
    let mut s := State.initial t.digest
    let mut i := 0
    for st in t.steps do
      let (s', v) := step t.policy s st.event
      stdoutLine s!"  {i} {eventSummary st.event} -> {verdictSummary v}"
      if profile then
        for l in profileLines s s' v do stdoutLine l
      s := s'
      i := i + 1
  pure 0

end WritCli
