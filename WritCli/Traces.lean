import WritCli.Expand

namespace WritCli

open Writ

def tracesUsage : String :=
  "usage: writ traces <policy.json> [--depth N] [--max-states M] [--out <dir>]\n\n" ++
  "Explore the policy breadth-first over a small alphabet of events and print, one JSON trace per\n" ++
  "line, the shortest trace for every transition between abstract states, plus the first rejected\n" ++
  "event found for each event type and reason. The policy may be layer 1 or 2; each trace carries\n" ++
  "the layer-1 policy (for layer 2, what writ expand prints). The same input gives the same bytes.\n" ++
  "  --depth N        events after session_start (default 4)\n" ++
  "  --max-states M   stop after M abstract states (default 20000)\n" ++
  "  --out <dir>      write <dir>/<name>.jsonl instead, <name> being the policy file name without .json\n\n" ++
  "stderr gets states S, traces T (accepted A, rejected R), depth N, with \", truncated\" when\n" ++
  "--max-states stopped the search, after one line for each action left out because its name,\n" ++
  "a guard name or an escalator name is longer than an event string may be.\n\n" ++
  "Exit 0, or 2 for a usage, IO or policy error (a policy with check errors prints them)."

private def natOpt (name : String) (v : Option String) (dflt : Nat) : Cli Nat :=
  match v with
  | none => pure dflt
  | some s =>
    if s.isEmpty || !s.all Char.isDigit || s.length > 9 then
      usageError s!"{name} needs a whole number below 10^9, not {s}"
    else pure s.toNat!

/-- The policy file name without its directory and without `.json`. -/
def policyStem (path : String) : String :=
  let base := (path.splitOn "/").getLast?.getD path
  if base.endsWith ".json" && base.length > 5 then (base.dropEnd 5).toString else base

def tracesCmd (args : List String) : Cli UInt32 := do
  let a ← parseArgs ["--depth", "--max-states", "--out"] args
  let [path] := a.pos.toList | usageError "expected exactly one policy file"
  let depth ← natOpt "--depth" (a.opt? "--depth") (({} : Explore.Config).depth)
  let maxStates ← natOpt "--max-states" (a.opt? "--max-states") (({} : Explore.Config).maxStates)
  if maxStates == 0 then usageError "--max-states must be at least 1"
  let some pol ← loadResolved path | return 2
  let stem := policyStem path
  for n in Explore.unnameable pol.policy do
    IO.eprintln (oneLine (s!"skipped action {n}: its name, a guard name or an escalator name is " ++
      s!"longer than {maxEventStringBytes} UTF-8 bytes, which an event cannot hold"))
  let r := Explore.run stem pol.policy { depth, maxStates } pol.doc
  let text := String.join (r.traces.toList.map fun t => (toJson t).compact ++ "\n")
  match a.opt? "--out" with
  | some dir =>
    liftIO (IO.FS.createDirAll dir) s!"{dir}: cannot create the directory"
    let out := if dir.endsWith "/" then dir ++ stem ++ ".jsonl" else dir ++ "/" ++ stem ++ ".jsonl"
    liftIO (IO.FS.writeFile out text) s!"{out}: cannot write the file"
  | none =>
    let stdout ← IO.getStdout
    stdout.putStr text
    stdout.flush
  let acceptedCount := (r.traces.filter (·.id.startsWith s!"{stem}/a/")).size
  IO.eprintln (s!"states {r.states}, traces {r.traces.size} (accepted {acceptedCount}, " ++
    s!"rejected {r.traces.size - acceptedCount}), depth {depth}{if r.truncated then ", truncated" else ""}")
  pure 0

end WritCli
