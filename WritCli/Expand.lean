import WritCli.Common

namespace WritCli

open Writ

def expandUsage : String :=
  "usage: writ expand <policy.json> [--out <file>]\n\n" ++
  "Resolve extends, apply labels and rules, and print the layer-1 policy the kernel runs\n" ++
  "as canonical JSON on one line, with each action's review, messages and source.\n" ++
  "  --out <file>   write it to this file instead\n\n" ++
  "Exit 0 when the policy expands, 1 when it or the policy it expands to has errors (printed\n" ++
  "instead; warnings do not count), 2 when a file cannot be read, parsed or decoded."

/-- The most files an `extends` chain may pass through below the policy given on the command line. -/
def maxExtendsDepth : Nat := 8

/-- Folds `.` and `..` segments lexically, so one file reached by two spellings is one file. -/
def normalizePath (p : String) : String :=
  let abs := p.startsWith "/"
  let segs := (p.splitOn "/").foldl (fun acc s =>
    if s == "" || s == "." then acc
    else if s == ".." then
      match acc.getLast? with
      | some l => if l == ".." then acc ++ [s] else acc.dropLast
      | none => if abs then acc else acc ++ [s]
    else acc ++ [s]) []
  (if abs then "/" else "") ++ "/".intercalate segs

/-- `rel` joined to the directory of the file `base`, as written; the OS resolves it when read. -/
def joinPath (base rel : String) : String :=
  if rel.startsWith "/" then rel
  else
    match (base.splitOn "/").dropLast with
    | [] => rel
    | dir => "/".intercalate dir ++ "/" ++ rel

/-- The most distinct files `extends` may reach. -/
def maxExtendsFiles : Nat := 256

inductive ExtendsProblem where
  | cycle (chain : List String)
  | unreadable (chain : List String)
  | tooDeep (chain : List String)
  | tooMany (chain : List String)

def ExtendsProblem.code : ExtendsProblem → String
  | .cycle _ => "extends_cycle"
  | .unreadable _ => "extends_unreadable"
  | .tooDeep _ => "extends_too_deep"
  | .tooMany _ => "extends_too_many"

private def arrows (c : List String) : String := " -> ".intercalate c

def ExtendsProblem.message : ExtendsProblem → String
  | .cycle c => s!"extends forms a cycle: {arrows c}"
  | .unreadable c => s!"cannot read extended policy \"{c.getLast?.getD ""}\" (extends chain: {arrows c})"
  | .tooDeep c => s!"extends is nested more than {maxExtendsDepth} files deep (extends chain: {arrows c})"
  | .tooMany c => s!"extends reaches more than {maxExtendsFiles} files (extends chain: {arrows c})"

structure Loaded where
  file : File2
  doc : Json
  /-- The file's real path, which identifies it across spellings and symbolic links. -/
  key : String
  /-- The keys of the files its `extends` lists. -/
  refs : List String := []

abbrev Resolve := ExceptT ExtendsProblem Cli

def decodeFile2 (path : String) (doc : Json) (name : String) : Cli File2 := do
  let policy : Policy2 ← decodeFile path doc
  pure { policy, facts := DocFacts.ofJson doc, name }

/-- One file of the chain being walked: its real path, its path as joined, and its path as shown
in messages (joined and folded, so messages do not depend on the machine, unless folding would
name a different file, as `..` after a symbolic link can; then as joined). -/
private structure Frame where
  key : String
  raw : String
  shown : String

/-- A parent that cannot be read is a problem of the file that names it; one that reads but does
not parse or decode is an input error, as for the file given on the command line. -/
private def loadParent (f : Frame) (chain : List String) : Resolve Loaded := do
  let bytes ← match ← (IO.FS.readBinFile f.raw).toBaseIO with
    | .ok b => pure b
    | .error _ => throw (.unreadable chain)
  let some text := String.fromUTF8? bytes | failWith s!"{f.shown}: not valid UTF-8"
  let doc ← parseJsonFile f.shown text
  pure { file := ← decodeFile2 f.shown doc f.shown, doc, key := f.key }

/-- Depth-first, in `extends` order, each file listed once however often it is reached, with the
keys of `refs`. `stack` is the chain from the command-line file, innermost first; `fuel` bounds its
depth and `maxExtendsFiles` the number of files, so the walk ends whatever the links on disk. -/
private partial def walk (fuel : Nat) (stack : List Frame) (refs : List String) (acc : Array Loaded) :
    Resolve (Array Loaded × List String) := do
  let some top := stack.head? | return (acc, [])
  let mut acc := acc
  let mut keys := #[]
  for r in refs do
    let raw := joinPath top.raw r
    let real ← (IO.FS.realPath raw).toBaseIO
    let folded := normalizePath raw
    let foldedReal ← if folded == raw then pure real else (IO.FS.realPath folded).toBaseIO
    let shown := match real, foldedReal with
      | .ok a, .ok b => if a.toString == b.toString then folded else raw
      | .error _, .error _ => folded
      | _, _ => raw
    let names := stack.reverse.map (·.shown)
    let chain := names ++ [shown]
    let key ← match real with
      | .ok k => pure k.toString
      | .error _ => throw (.unreadable chain)
    if stack.any (·.key == key) then throw (.cycle chain)
    keys := keys.push key
    if acc.any (·.key == key) then continue
    match fuel with
    | 0 => throw (.tooDeep chain)
    | k + 1 =>
      if acc.size ≥ maxExtendsFiles then throw (.tooMany chain)
      let frame : Frame := { key, raw, shown }
      let p ← loadParent frame chain
      let (acc', kids) ← walk k (frame :: stack) p.file.policy.«extends» (acc.push p)
      acc := acc'.modify acc.size fun l => { l with refs := kids }
  pure (acc, keys.toList)

/-- The keys of the files reachable from `todo` through `refs`, each once. `fuel` is at least the
number of keys the walk can visit: `todo` and every file's `refs`. -/
def reachable (all : Array Loaded) : Nat → List String → List String → List String
  | 0, seen, _ | _, seen, [] => seen
  | n + 1, seen, k :: todo =>
    if seen.contains k then reachable all n seen todo
    else reachable all n (seen ++ [k]) (todo ++ ((all.find? (·.key == k)).map (·.refs)).getD [])

/-- Each file with the dimensions declared by the files it extends, directly or not. -/
def withInherited (all : Array Loaded) : List Loaded :=
  all.toList.map fun l =>
    let fuel := l.refs.length + all.foldl (· + ·.refs.length) 0 + 1
    let above := (reachable all fuel [] l.refs).flatMap fun k =>
      ((all.find? (·.key == k)).map (·.file.policy.labels)).getD []
    { l with file := { l.file with inherited := above } }

/-- The files `path` extends, flattened depth-first in `extends` order. -/
def resolveExtends (path : String) (leaf : Policy2) : Cli (Except ExtendsProblem (List Loaded)) :=
  ExceptT.run do
    let key ← match ← (IO.FS.realPath path).toBaseIO with
      | .ok k => pure k.toString
      | .error _ => pure (normalizePath path)
    let (parents, _) ← walk maxExtendsDepth [{ key, raw := path, shown := path }] leaf.«extends» #[]
    pure (withInherited parents)

/-- The policy's JSON with each action's `review`, `messages` and `source` put back from the first
document that writes them: the layer-1 policy does not store them, and the layer-2 check requires
every document that writes one to agree. -/
def splice (docs : List Json) (p : Policy) : Json :=
  let written (n k : String) : Option Json :=
    docs.findSome? fun d => (field? d "actions").bind (field? · n) |>.bind (field? · k)
  let action (n : String) : Json → Json
    | .obj kvs =>
      .obj (kvs ++ (["review", "messages", "source"].filterMap fun k => (written n k).map (k, ·)).toArray)
    | j => j
  match toJson p with
  | .obj kvs => .obj (kvs.map fun (k, v) =>
    if k == "actions" then
      (k, match v with
        | .obj acts => .obj (acts.map fun (n, a) => (n, action n a))
        | v => v)
    else (k, v))
  | j => j

structure Expansion where
  problems : List Problem2
  policy : Policy
  doc : Json
  /-- `Policy2.check` reports nothing: the layer-2 problems and the expanded policy's are none. -/
  accepted : Bool

/-- The layer-2 problems, the expanded policy and its document, or the `extends`
problem that stopped the expansion. -/
def expandFile (path : String) (doc : Json) : Cli (Except ExtendsProblem Expansion) := do
  let leaf : Policy2 ← decodeFile path doc
  match ← resolveExtends path leaf with
  | .error e => pure (.error e)
  | .ok parents =>
    let leafFile : File2 :=
      { policy := leaf, facts := DocFacts.ofJson doc, name := if parents.isEmpty then "" else path }
    let files := parents.map (·.file)
    let policy := expand (files.map (·.policy)) leaf
    pure (.ok {
      problems := Policy2.problems files leafFile
      policy
      doc := splice (doc :: parents.map (·.doc)) policy
      accepted := (Policy2.check files leafFile).isEmpty })

/-- What `Policy2.check` reports, with codes: the layer-2 problems, then the expanded policy's. -/
def Expansion.errors (x : Expansion) : List (String × Json) :=
  x.problems.map (fun (p : Problem2) => finding "error" p.code p.message p.action?) ++
    x.policy.check.map (fun (p : Problem) => finding "error" p.code p.message p.action?)

private def reportErrors (errors : List (String × Json)) : Cli UInt32 := do
  for (t, _) in errors do stdoutLine t
  stdoutLine (plural errors.length "error" "errors")
  pure 1

def expandCmd (args : List String) : Cli UInt32 := do
  let a ← parseArgs ["--out"] args
  let [path] := a.pos.toList | usageError "expected exactly one policy file"
  let doc ← parseJsonFile path (← readText path)
  match ← expandFile path doc with
  | .error e => reportErrors [finding "error" e.code e.message none]
  | .ok x =>
    unless x.accepted do return ← reportErrors x.errors
    let text := x.doc.canonical
    match a.opt? "--out" with
    | some out => liftIO (IO.FS.writeFile out (text ++ "\n")) s!"{out}: cannot write the file"
    | none => rawLine text
    pure 0

structure CheckResult where
  errors : List (String × Json)
  warnings : List (String × Json)
  digest? : Option String
  /-- The document whose actions carry `source`: the policy as written, or for layer 2 the
  `writ expand` output; none when an `extends` problem stopped the expansion. -/
  doc? : Option Json

/-- `writ check` on a layer-2 document: its `extends` or layer-2 problems, then the expanded
policy's problems and warnings. The digest is that of the `writ expand` output, the policy a
kernel runs, and is absent when there is none. -/
def checkLayer2 (path : String) (doc : Json) : Cli CheckResult := do
  match ← expandFile path doc with
  | .error e =>
    pure { errors := [finding "error" e.code e.message none], warnings := [], digest? := none,
           doc? := none }
  | .ok x => pure {
      errors := x.errors
      warnings := (x.policy.warnings ++ messageWarnings x.doc).map
        (fun (w : Warning) => finding "warning" w.code w.message w.action?)
      digest? := if x.problems.isEmpty then some x.doc.digest else none
      doc? := some x.doc }

/-- A policy the kernel runs and the document a trace of it carries: the policy as written, or for
layer 2 the `writ expand` output, whose digest the kernel runs under. -/
structure Resolved where
  policy : Policy
  doc : Json

private def refuse (path : String) (errors : List (String × Json)) : Cli (Option Resolved) := do
  for (t, _) in errors do
    IO.eprintln (oneLine s!"error: {path}: {toString (t.drop "error: ".length)}")
  pure none

/-- The policy at `path`, layer 1 or 2, or none after printing the errors `writ check` would report. -/
def loadResolved (path : String) : Cli (Option Resolved) := do
  let doc ← parseJsonFile path (← readText path)
  if isLayer2 doc then
    match ← expandFile path doc with
    | .error e => refuse path [finding "error" e.code e.message none]
    | .ok x =>
      -- Read back from its canonical text, so the document is byte for byte what `writ expand` prints.
      if x.accepted then pure (some { policy := x.policy, doc := (Json.parse x.doc.canonical).toOption.getD x.doc })
      else refuse path x.errors
  else
    let policy : Policy ← decodeFile path doc
    match policy.check with
    | [] => pure (some { policy, doc })
    | ps => refuse path (ps.map fun p => finding "error" p.code p.message p.action?)

end WritCli
