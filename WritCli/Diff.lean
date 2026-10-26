import WritCli.Expand

namespace WritCli

open Writ

def diffUsage : String :=
  "usage: writ diff <old.json> <new.json> <events.jsonl> [--json]\n\n" ++
  "Replay recorded events (one JSON object per line) under both policies and print each event\n" ++
  "whose verdict changed, state_version aside, then a count, noting the events both policies\n" ++
  "rejected. The file holds one session: it starts with a session_start and holds no other.\n" ++
  "Each policy may be layer 1 or 2. Each run starts from a fresh state under its own policy\n" ++
  "digest, and diff sets every event's state_version, and a session_start's policy_digest\n" ++
  "(which may be left out), to that run's, so one changed verdict does not turn every later\n" ++
  "event into a mismatch.\n" ++
  "  --json   print one JSON object per changed event instead, and no count\n\n" ++
  "Exit 0 when no verdict changed, 1 when one did, 2 for a usage, IO or policy error, an event\n" ++
  "line that is empty or does not parse or decode, or a file that does not start with a\n" ++
  "session_start or holds a second one."

private structure Run where
  policy : Policy
  digest : String

private def loadRun (path : String) : Cli (Option Run) := do
  let some r ← loadResolved path | pure none
  pure (some { policy := r.policy, digest := r.doc.digest })

private structure Recorded where
  line : Nat
  json : Json
  event : Event

private def readEvents (path : String) : Cli (Array Recorded) := do
  let text ← readText path
  if text.all (fun c => c == '\n' || c == '\r') then return #[]
  let lines := text.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  let mut out := #[]
  let mut n := 0
  for l in lines do
    n := n + 1
    if l.all Char.isWhitespace then failWith s!"{path}: line {n}: empty line"
    let j ← match Json.parse l with
      | .ok j => pure j
      | .error e => failWith s!"{path}: line {n}: {e}"
    match Event.decodeWith (some "") j with
    | .ok event => out := out.push { line := n, json := j, event }
    | .error e => failWith s!"{path}: line {n}: {e.render}"
  pure out

/-- Events carry no session id, so a second session cannot be told apart from the first: its
events would run in the first session's state under both policies and compare equal. -/
private def checkOneSession (path : String) (events : Array Recorded) : Cli Unit := do
  for e in events do
    let start := e.event.body.typeName == "session_start"
    if e.line == 1 && !start then
      failWith (s!"{path}: line 1: the first event must be a session_start, not {e.event.body.typeName}; " ++
        "diff replays one session per events file")
    if e.line > 1 && start then
      failWith s!"{path}: line {e.line}: a second session_start; diff replays one session per events file"

/-- The event as one run sees it: its `state_version`, and a `session_start`'s `policy_digest`,
written or not, are the run's. -/
private def rewrite (j : Json) (version : Nat) (digest : String) : Json :=
  match j with
  | .obj kvs =>
    let start := kvs.contains ("type", .str "session_start")
    let kvs := kvs.map fun (k, v) =>
      if k == "state_version" then (k, .num version)
      else if start && k == "policy_digest" then (k, .str digest)
      else (k, v)
    .obj (if start && !kvs.any (·.1 == "policy_digest") then kvs.push ("policy_digest", .str digest)
      else kvs)
  | j => j

private def without (keys : List String) : Json → Json
  | .obj kvs => .obj (kvs.filter fun (k, _) => !keys.contains k)
  | j => j

private def stepRun (r : Run) (s : State) (e : Recorded) (path : String) : Cli (State × Json) :=
  match Api.stepEvent r.policy s (rewrite e.json s.version r.digest).compact with
  | .ok (s', v) => pure (s', without ["state_version"] v)
  -- Not reached: the line decoded, and the rewrite sets only a version and a policy digest.
  | .error msg => failWith s!"{path}: line {e.line}: {msg}"

def diffCmd (args : List String) : Cli UInt32 := do
  let json := args.contains "--json"
  let a ← parseArgs [] (args.filter (· != "--json"))
  let [oldPath, newPath, eventsPath] := a.pos.toList
    | usageError "expected an old policy, a new policy and an events file"
  let some old ← loadRun oldPath | return 2
  let some new ← loadRun newPath | return 2
  let events ← readEvents eventsPath
  checkOneSession eventsPath events
  let mut so := State.initial old.digest
  let mut sn := State.initial new.digest
  let mut out : Array String := #[]
  let mut bothRejected := 0
  for e in events do
    let (so', vo) ← stepRun old so e eventsPath
    let (sn', vn) ← stepRun new sn e eventsPath
    so := so'
    sn := sn'
    if field? vo "verdict" == some (.str "rejected") && field? vn "verdict" == some (.str "rejected") then
      bothRejected := bothRejected + 1
    if vo == vn then continue
    let callId? := match field? e.json "call_id" with
      | some (.str c) => some c
      | _ => none
    let ty := e.event.body.typeName
    out := out.push <| if json then
        (Json.obj (#[("line", .num e.line), ("seq", .num e.event.seq), ("type", .str ty)] ++
          (callId?.map fun c => #[("call_id", Json.str c)]).getD #[] ++
          #[("old", vo), ("new", vn)])).compact
      else
        let brief := fun v => (without ["retry", "message"] v).compact
        s!"line {e.line} seq {e.event.seq} {ty}{(callId?.map (" " ++ oneLine ·)).getD ""}: " ++
          s!"{brief vo} -> {brief vn}{if out.isEmpty then " (first divergence)" else ""}"
  for l in out do rawLine l
  unless json do
    stdoutLine (s!"{out.size} of {events.size} events changed" ++
      if bothRejected > 0 then s!", {bothRejected} rejected under both policies" else "")
  pure (if out.isEmpty then 0 else 1)

end WritCli
