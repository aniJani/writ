import WritCli.Common

namespace WritCli

open Writ

def oracleUsage : String :=
  "usage: writ oracle <policy.json> [--state <state.json>] [--state-out <path>] [--digest <d>]\n\n" ++
  "Read one event JSON per line on stdin, step the kernel, and print one verdict JSON line per input line.\n" ++
  "A line that does not parse or decode (an empty line included) prints {\"error\": \"...\"} and leaves the state unchanged.\n" ++
  "  --state <file>      start from a saved state instead of State.initial\n" ++
  "  --state-out <path>  write the final state (canonical JSON) at end of input\n" ++
  "  --digest <d>        use this policy digest instead of the digest of the policy file\n\n" ++
  "Exit 0 at end of input, 2 for a usage, IO or policy error, or when --state does not match the digest."

private def errorLine (msg : String) : String :=
  (Json.obj #[("error", .str msg)]).compact

private def stepLine (policy : Policy) (s : State) (line : String) : State × String :=
  match Api.stepEvent policy s line with
  | .error e => (s, errorLine e)
  | .ok (s', v) => (s', v.compact)

private def handle (policy : Policy) (s : State) (raw : ByteArray) : IO State := do
  let (s', out) := match String.fromUTF8? raw with
    | none => (s, errorLine "line is not valid UTF-8")
    | some line => stepLine policy s line
  rawLine out
  pure s'

private partial def drain (policy : Policy) (s : State) (buf : ByteArray) (start : Nat) :
    IO (State × ByteArray) := do
  let mut i := start
  while i < buf.size && buf[i]! != 10 do i := i + 1
  if i >= buf.size then return (s, buf.extract start buf.size)
  drain policy (← handle policy s (buf.extract start i)) buf (i + 1)

private partial def loop (policy : Policy) (stdin : IO.FS.Stream) (s : State) (pending : ByteArray) :
    IO State := do
  let chunk ← stdin.read 65536
  if chunk.isEmpty then
    if pending.isEmpty then return s else handle policy s pending
  else
    let (s', rest) ← drain policy s (pending ++ chunk) 0
    loop policy stdin s' rest

def oracle (args : List String) : Cli UInt32 := do
  let a ← parseArgs ["--state", "--state-out", "--digest"] args
  let [path] := a.pos.toList | usageError "expected exactly one policy file"
  let { policy, doc } ← loadPolicy path
  let problems := policy.check
  unless problems.isEmpty do
    for p in problems do IO.eprintln (oneLine (finding "error" p.code p.message p.action?).1)
    return 2
  let digest := a.opt? "--digest" |>.getD doc.digest
  let start ← match a.opt? "--state" with
    | none => pure (State.initial digest)
    | some sp =>
      let st : State ← decodeFile sp (← parseJsonFile sp (← readText sp))
      if st.expectedPolicyDigest != digest then
        failWith s!"{sp}: state is for policy {st.expectedPolicyDigest}, not {digest}"
      pure st
  let final ← loop policy (← IO.getStdin) start ByteArray.empty
  if let some out := a.opt? "--state-out" then
    liftIO (IO.FS.writeFile out ((toJson final).canonical ++ "\n")) s!"{out}: cannot write the file"
  pure 0

end WritCli
