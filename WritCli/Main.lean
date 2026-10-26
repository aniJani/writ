import WritCli.Check
import WritCli.Replay
import WritCli.Oracle
import WritCli.Explain
import WritCli.Import
import WritCli.Diff
import WritCli.Traces

open WritCli Writ

def version : String :=
  s!"writ {cliVersion} (kernel {kernelVersion}, trace {traceSchema}, state {stateSchema})"

def usage : String :=
  "usage: writ <command> [args]\n\n" ++
  "commands:\n" ++
  "  check <policy.json> [...]      check a policy for errors and warnings, and changed tools\n" ++
  "  expand <policy.json> [--out f] print a layer-2 policy as the layer-1 policy it expands to\n" ++
  "  digest <policy.json>           print the policy digest\n" ++
  "  import mcp <tools.json> [...]  draft a layer-2 policy from an MCP tool list\n" ++
  "  replay <traces.jsonl>...       replay traces against their expectations\n" ++
  "  oracle <policy.json> [...]     step the kernel over events read from stdin\n" ++
  "  explain <traces.jsonl> [...]   describe each step of a trace\n" ++
  "  diff <old> <new> <jsonl> [...] replay events under two policies and list changed verdicts\n" ++
  "  traces <policy.json> [...]     emit the shortest trace for every abstract transition\n\n" ++
  "options:\n" ++
  "  --help      show this help (also: writ <command> --help)\n" ++
  "  --version   show the version"

def commands : List (String × (String × (List String → Cli UInt32))) := [
  ("check", (checkUsage, check)), ("expand", (expandUsage, expandCmd)),
  ("digest", (digestUsage, digest)), ("import", (importUsage, importCmd)),
  ("replay", (replayUsage, replay)), ("oracle", (oracleUsage, oracle)),
  ("explain", (explainUsage, explain)), ("diff", (diffUsage, diffCmd)),
  ("traces", (tracesUsage, tracesCmd))]

def finish (u : String) (r : Except CliError UInt32) : IO UInt32 :=
  match r with
  | .ok c => pure c
  | .error (.fail msg) => do IO.eprintln s!"error: {msg}"; pure 2
  | .error (.usage msg) => do IO.eprintln s!"error: {msg}\n{u}"; pure 2

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => do IO.eprintln usage; pure 2
  | ["--help"] | ["-h"] => do IO.println usage; pure 0
  | ["--version"] => do IO.println version; pure 0
  | cmd :: rest =>
    match commands.lookup cmd with
    | none => do IO.eprintln s!"error: unknown command {cmd}\n{usage}"; pure 2
    | some (u, run) =>
      if rest.contains "--help" then do IO.println u; pure 0
      else do
        try finish u (← (run rest).run)
        catch e => do IO.eprintln s!"error: {oneLine ((toString e).splitOn "\n" |>.head!)}"; pure 2
