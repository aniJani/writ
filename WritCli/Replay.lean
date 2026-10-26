import WritCli.Common

namespace WritCli

open Writ

def replayUsage : String :=
  "usage: writ replay <traces.jsonl>... [--coverage]\n\n" ++
  "Replay every trace and compare each step with its expected fields.\n" ++
  "Prints ok <id> or FAIL <id> step <i>: <mismatch>, then a summary line.\n" ++
  "  --coverage   add a last line {\"reasons\":[...],\"decisions\":[...]}: every reason code and\n" ++
  "               decision in the verdicts the replay gave, sorted, each once (reasons include\n" ++
  "               rejections, denied and dispatch_denied decisions, existing statuses and would_deny)\n\n" ++
  "Exit 0 when all traces match, 1 when any fails, 2 when a file cannot be read or parsed."

def loadTraces (path : String) : Cli (List Trace) :=
  do
    match parseTraces (← readText path) with
    | .ok ts => pure ts
    | .error e => failWith s!"{path}: {e}"

def verdictCodes : Verdict → List String × List String
  | .rejected r => ([r.code], [])
  | .ok d sh =>
    let shadow := match sh with | some (.wouldDeny r) => [r.code] | _ => []
    ((d.reason?.map (·.code)).toList ++ shadow, d.code.toList)

def coverageJson (reasons decisions : Std.HashSet String) : Json :=
  let sorted (s : Std.HashSet String) := Encode.strings (s.toList.mergeSort (· ≤ ·))
  .obj #[("reasons", sorted reasons), ("decisions", sorted decisions)]

def replay (args : List String) : Cli UInt32 := do
  let coverage := args.contains "--coverage"
  let a ← parseArgs [] (args.filter (· != "--coverage"))
  if a.pos.isEmpty then usageError "expected at least one trace file"
  let mut traces := #[]
  for path in a.pos do
    traces := traces ++ (← loadTraces path).toArray
  let mut failed := 0
  let mut reasons : Std.HashSet String := {}
  let mut decisions : Std.HashSet String := {}
  for t in traces do
    let r := t.replay
    if coverage then
      for s in r.steps do
        let (rs, ds) := verdictCodes s.verdict
        reasons := reasons.insertMany rs
        decisions := decisions.insertMany ds
    if r.ok then stdoutLine s!"ok {r.id}"
    else
      failed := failed + 1
      for s in r.steps do
        if let some m := s.mismatch then stdoutLine s!"FAIL {r.id} step {s.index}: {m}"
  stdoutLine s!"{plural traces.size "trace" "traces"}, {failed} failed"
  if coverage then rawLine (coverageJson reasons decisions).compact
  pure (if failed == 0 then 0 else 1)

end WritCli
