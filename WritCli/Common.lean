import Writ

namespace WritCli

open Writ

inductive CliError where
  | usage (msg : String)
  | fail (msg : String)

abbrev Cli := ExceptT CliError IO

private def hex4 (n : Nat) : String :=
  let d (k : Nat) := "0123456789abcdef".toList[k % 16]!
  String.ofList [d (n / 4096), d (n / 256), d (n / 16), d n]

/-- Escapes backslash and control characters as in a JSON string, so the text stays on one line and can be read back. -/
def oneLine (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | '\x08' => acc ++ "\\b"
    | '\x0c' => acc ++ "\\f"
    | _ => if c.toNat < 0x20 || c.toNat == 0x7f then acc ++ "\\u" ++ hex4 c.toNat else acc.push c) ""

def failWith (msg : String) : Cli α := throw (.fail (oneLine msg))

def usageError (msg : String) : Cli α := throw (.usage (oneLine msg))

structure Args where
  pos : Array String := #[]
  opts : List (String × String) := []

def Args.opt? (a : Args) (name : String) : Option String := a.opts.lookup name

def parseArgs (valued : List String) (args : List String) : Cli Args :=
  go args {}
where
  go : List String → Args → Cli Args
    | [], acc => pure acc
    | a :: rest, acc =>
      if valued.contains a then
        match rest with
        | v :: rest' =>
          if acc.opts.any (·.1 == a) then usageError s!"{a} given twice"
          else go rest' { acc with opts := acc.opts ++ [(a, v)] }
        | [] => usageError s!"{a} needs a value"
      else if a.startsWith "-" && a.length > 1 then usageError s!"unknown option {a}"
      else go rest { acc with pos := acc.pos.push a }

def liftIO (act : IO α) (what : String) : Cli α := do
  match ← (act.toBaseIO) with
  | .ok a => pure a
  | .error e => failWith s!"{what} ({(toString e).splitOn "\n" |>.head!})"

def readText (path : String) : Cli String := do
  let bytes ← liftIO (IO.FS.readBinFile path) s!"{path}: cannot read the file"
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => failWith s!"{path}: not valid UTF-8"

def parseJsonFile (path text : String) : Cli Json :=
  match Json.parse text with
  | .ok j => pure j
  | .error e => failWith s!"{path}: {e}"

def decodeFile [FromJson α] (path : String) (j : Json) : Cli α :=
  match decode j with
  | .ok a => pure a
  | .error e => failWith s!"{path}: {e.render}"

/-- The (name, tool) pairs of a tools.json file, in listing order; an input error when it lists
no tools. -/
def readTools (path : String) : Cli (Array (String × JcsValue)) := do
  let doc ← match Jcs.parse (← readText path) with
    | .ok d => pure d
    | .error e => failWith s!"{path}: {e}"
  let tools ← match Tool.listOf doc with
    | .ok ts => pure ts
    | .error e => failWith s!"{path}: {e}"
  if tools.isEmpty then failWith s!"{path}: no tools"
  pure tools

/-- A `--server` value, which names a `source.server` and so has its length limit. -/
def checkServerOpt (server? : Option String) : Cli Unit := do
  if let some s := server? then
    if s.utf8ByteSize > maxSourceStringBytes then
      usageError s!"--server is longer than {maxSourceStringBytes} bytes"

def field? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

structure LoadedPolicy where
  policy : Policy
  doc : Json

def loadPolicy (path : String) : Cli LoadedPolicy := do
  let doc ← parseJsonFile path (← readText path)
  if isLayer2 doc then
    failWith <| s!"{path}: a layer-2 policy (labels, rules or extends); " ++
      "use the layer-1 policy writ expand prints"
  pure { policy := ← decodeFile path doc, doc }

def plural (n : Nat) (one many : String) : String :=
  s!"{n} {if n == 1 then one else many}"

def rawLine (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (s ++ "\n")
  out.flush

def stdoutLine (s : String) : IO Unit := rawLine (oneLine s)

def finding (kind code message : String) (action? : Option String) : String × Json :=
  let text := match action? with
    | some a => s!"{kind}: {a}: {message}"
    | none => s!"{kind}: {message}"
  (text, Api.findingJson code message action?)

end WritCli
