import Writ.Codec.Verdict
import Writ.Json.Sha256
import Writ.Kernel.Step

namespace Writ

open Decoder Encode

def traceSchema : String := "writ.trace/1"

structure TraceStep where
  event : Event
  expect : Option Json := none
  deriving BEq, Repr

structure Trace where
  id : String
  description : Option String := none
  policy : Policy
  policyDoc : Json
  policyDigest : Option String := none
  steps : List TraceStep
  deriving BEq, Repr

def Trace.digest (t : Trace) : String := t.policyDigest.getD t.policyDoc.digest

structure StepReport where
  index : Nat
  verdict : Verdict
  mismatch : Option String
  deriving BEq, Repr

structure ReplayReport where
  id : String
  steps : List StepReport
  ok : Bool
  deriving BEq, Repr

def verdictKeys : List String :=
  ["verdict", "state_version", "decision", "retry", "message", "would_deny", "would_need_approval"]
    ++ decisionKeys

/-- Strings render without quotes, everything else as compact JSON. -/
def renderExpectValue : Json → String
  | .str s => s
  | j => j.compact

/-- Objects compare as maps (key order ignored), so `expect` is compared by canonical form. -/
def expectMismatch (expect actual : Json) : Option String :=
  let actualKvs := match actual with | .obj kvs => kvs | _ => #[]
  let expectKvs := match expect with | .obj kvs => kvs | _ => #[]
  let problems := expectKvs.toList.filterMap fun (k, want) =>
    match actualKvs.find? (·.1 == k) with
    | none => some s!"expected {k} {renderExpectValue want}, got no {k}"
    | some (_, got) =>
      if want.canonical == got.canonical then none
      else some s!"expected {k} {renderExpectValue want}, got {renderExpectValue got}"
  if problems.isEmpty then none else some ("; ".intercalate problems)

def Trace.replay (t : Trace) : ReplayReport :=
  let (_, reports) := t.steps.foldl (init := (State.initial t.digest, #[])) fun (s, acc) st =>
    let (s', v) := step t.policy s st.event
    let mismatch := st.expect.bind (expectMismatch · (v.toJsonWith s'.version))
    (s', acc.push { index := acc.size, verdict := v, mismatch })
  { id := t.id, steps := reports.toList, ok := reports.all (·.mismatch.isNone) }

def decodeExpect (j : Json) : Decoder Json := do
  let _ ← object verdictKeys j
  pure j

def TraceStep.decoder (digest : String) (j : Json) : Decoder TraceStep := do
  let fs ← object ["event", "expect"] j
  pure ⟨← req fs "event" (Event.decoder (some digest)), ← opt fs "expect" decodeExpect⟩

instance : ToJson TraceStep where
  toJson st := obj [some ("event", toJson st.event), some' "expect" st.expect id]

instance : FromJson Trace where
  fromJson j := do
    let fs ← object ["schema", "id", "description", "policy", "policy_digest", "events"] j
    let schema ← req fs "schema" string
    unless schema == traceSchema do
      at' "schema" (fail s!"unsupported schema \"{schema}\", expected \"{traceSchema}\"")
    let id ← req fs "id" string
    let description ← opt fs "description" string
    let policy ← req fs "policy" FromJson.fromJson
    let policyDoc ← req fs "policy" pure
    let policyDigest ← opt fs "policy_digest" string
    let digest := policyDigest.getD policyDoc.digest
    let steps ← req fs "events" (array (TraceStep.decoder digest))
    pure { id, description, policy, policyDoc, policyDigest, steps }

instance : ToJson Trace where
  toJson t := obj [
    some ("schema", .str traceSchema), some ("id", .str t.id),
    some' "description" t.description Json.str, some ("policy", t.policyDoc),
    some' "policy_digest" t.policyDigest Json.str,
    some ("events", .arr (t.steps.map toJson).toArray)]

/-- Parse errors from `Json.parse` say "line 1" for a single line; the JSONL line number replaces it. -/
def parseTraces (text : String) : Except String (List Trace) := do
  let mut out := #[]
  let mut lineNo := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    if line.all Char.isWhitespace then continue
    let j ← match Json.parse line with
      | .ok j => pure j
      | .error e => throw s!"line {lineNo}: {e.replace " at line 1, column " " at column "}"
    match (decode j : Except DecodeError Trace) with
    | .ok t => out := out.push t
    | .error e => throw s!"line {lineNo}: {e.render}"
  pure out.toList

end Writ
