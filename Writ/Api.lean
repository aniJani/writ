import Writ.Author.Check
import Writ.Author.Warnings
import Writ.Codec.Trace
import Writ.Codec.State
import Writ.Json.Sha256
import Writ.Profile.McpToolApproval

namespace Writ.Api

/-- `input` names the argument at fault: `policy`, `state`, `event`, `ledger`, `traces`, `json`,
`digest`, `time` or `profile`. -/
def errorJson (input msg : String) : Json := .obj #[("error", .str msg), ("input", .str input)]

def fail (input msg : String) : String := (errorJson input msg).compact

abbrev Failure := String × String

def tag (input : String) (r : Except String α) : Except Failure α := r.mapError (input, ·)

def run (r : Except Failure Json) : String :=
  match r with
  | .ok j => j.compact
  | .error (input, msg) => fail input msg

def decodeText [FromJson α] (input text : String) : Except Failure α := tag input do
  let j ← Json.parse text
  (decode j : Except DecodeError α).mapError (·.render)

def findingJson (code message : String) (action? : Option String) : Json :=
  .obj (#[("code", .str code)] ++ (action?.map fun a => #[("action", Json.str a)]).getD #[]
    ++ #[("message", .str message)])

def checkJson (policy : Policy) (doc : Json) : Json :=
  let errors := policy.check.map fun p => findingJson p.code p.message p.action?
  let warnings := (policy.warnings ++ messageWarnings doc).map fun w => findingJson w.code w.message w.action?
  .obj #[("ok", .bool errors.isEmpty), ("errors", .arr errors.toArray),
    ("warnings", .arr warnings.toArray), ("policy_digest", .str doc.digest)]

def parsePolicy (text : String) : Except String (Policy × Json) := do
  let doc ← Json.parse text
  match (decode doc : Except DecodeError Policy) with
  | .ok p => pure (p, doc)
  | .error e => throw e.render

def checkedPolicy (text : String) : Except String (Policy × Json) := do
  let (policy, doc) ← parsePolicy text
  if let p :: _ := policy.check then
    throw s!"policy fails check: {p.code}: {p.message}"
  pure (policy, doc)

def check (policyText : String) : String :=
  match parsePolicy policyText with
  | .ok (p, doc) => (checkJson p doc).compact
  | .error e => fail "policy" e

def digest (jsonText : String) : String :=
  match Json.parse jsonText with
  | .ok j => (Json.obj #[("digest", .str j.digest)]).compact
  | .error e => fail "json" e

def canonical (jsonText : String) : String :=
  match Json.parse jsonText with
  | .ok j => (Json.obj #[("canonical", .str j.canonical)]).compact
  | .error e => fail "json" e

def stateText (s : State) : String := (toJson s).canonical

def initial (policyText : String) (digest? : Option String) : String := run do
  let (_, doc) ← tag "policy" (checkedPolicy policyText)
  let d := doc.digest
  if let some given := digest? then
    unless given == d do throw ("digest", s!"digest {given} is not the policy's digest {d}")
  let s := State.initial d
  pure (.obj #[("state", .str (stateText s)), ("state_version", .num s.version),
    ("ledger_version", .num s.ledger.version)])

/-- One event line against a state. This is what `writ oracle` runs per input line. -/
def stepEvent (policy : Policy) (s : State) (line : String) : Except String (State × Json) := do
  let j ← Json.parse line
  match (decode j : Except DecodeError Event) with
  | .error e => throw e.render
  | .ok ev =>
    let (s', v) := Writ.step policy s ev
    pure (s', v.toJsonWith s'.version)

/-- A checked policy and a state made under it. -/
def policyState (policyText stateText' : String) : Except Failure (Policy × State) := do
  let (policy, doc) ← tag "policy" (checkedPolicy policyText)
  let s : State ← decodeText "state" stateText'
  let d := doc.digest
  unless s.expectedPolicyDigest == d do
    throw ("state", s!"state was made under policy {s.expectedPolicyDigest}, not {d}")
  pure (policy, s)

def step (policyText stateText' eventText : String) : String := run do
  let (policy, s) ← policyState policyText stateText'
  let (s', v) ← tag "event" (stepEvent policy s eventText)
  let text := stateText s'
  pure (.obj #[("verdict", v), ("state", .str text),
    ("ledger", .str (toJson s'.ledger).canonical),
    ("changed", .bool (text != stateText s)), ("state_version", .num s'.version),
    ("ledger_version", .num s'.ledger.version),
    ("ledger_changed", .bool (s'.ledger.version != s.ledger.version))])

/-- An empty `ledgerText` is the empty ledger. -/
def tombstone (ledgerText : String) (set : Bool) : String := run do
  let l : Ledger ← if ledgerText.isEmpty then pure {} else decodeText "ledger" ledgerText
  let l' := l.setTombstone set
  pure (.obj #[("ledger", .str (toJson l').canonical), ("ledger_version", .num l'.version),
    ("changed", .bool (l'.version != l.version))])

def callView (s : State) (callId : String) (r : CallRec) : Json :=
  let requestId : RequestId := ⟨s.sessionId, callId, r.generation⟩
  .obj (#[("call_id", .str callId), ("tool", .str r.tool), ("status", toJson r.status),
    ("digest", .str r.digest), ("cost", costOpt r.cost), ("attempts", .num r.attempts),
    ("generation", .num r.generation), ("epoch", .num r.epoch)]
    ++ (if r.status == .awaiting then #[("request_id", toJson requestId)] else #[]))

def meterView (p : Policy) (s : State) (time : Nat) (name : String) (spec : MeterSpec) : Json :=
  let used := Meter.usage spec (s.meterEntries p name) name time
  let dec (n : Nat) : Json := .str (toString n)
  .obj #[("meter", .str name), ("scope", toJson spec.scope), ("used", dec used),
    ("cap", optJson spec.cap dec), ("remaining", optJson spec.cap fun c => dec (c - used))]

def inspect (policyText stateText' : String) (time : Nat) : String := run do
  let (p, s) ← policyState policyText stateText'
  pure (.obj #[("session_id", .str s.sessionId), ("state_version", .num s.version),
    ("ledger_version", .num s.ledger.version), ("started", .bool s.started),
    ("ended", .bool s.ended), ("killed", .bool s.killed), ("tombstone", .bool s.ledger.tombstone),
    ("escalated", .bool s.escalated), ("escalations", .num s.escalations),
    ("blocked_tools", Encode.strings s.blockedTools),
    ("calls", .arr (s.calls.toList.map fun (k, r) => callView s k r).toArray),
    ("meters", .arr (p.meters.map fun (n, spec) => meterView p s time n spec).toArray)])

def parseTime (text : String) : Except Failure Nat :=
  if text.isEmpty || !text.all Char.isDigit then throw ("time", "time is not a decimal string of digits")
  else pure (text.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

def replay (tracesText : String) : String :=
  match parseTraces tracesText with
  | .error e => fail "traces" e
  | .ok traces =>
    let item (t : Trace) : Json :=
      let r := t.replay
      let mismatches := r.steps.filterMap fun s => s.mismatch.map fun m =>
        Json.obj #[("step", .num s.index), ("message", .str m)]
      .obj #[("id", .str r.id), ("ok", .bool r.ok), ("mismatches", .arr mismatches.toArray)]
    (Json.obj #[("traces", .arr (traces.map item).toArray)]).compact

def decodeIn [FromJson α] (path : String) (j : Json) : Except Failure α :=
  tag "json" (((Decoder.at' path (FromJson.fromJson j)).run []).mapError (·.render))

def profileResult (j : Json) : Except Failure Json := do
  let fs : Array (String × Json) ←
    tag "json" (((Decoder.object ["profile", "verdict", "status"] j).run []).mapError (·.render))
  let field (k : String) : Option Json := (fs.find? (·.1 == k)).map (·.2)
  let id : String ← match field "profile" with
    | some (Json.str s) => pure s
    | some _ => throw ("profile", "profile: expected a string")
    | none => throw ("profile", "profile: missing field")
  unless id == Profile.McpToolApproval.id do
    throw ("profile", s!"unknown profile \"{id}\", expected {Profile.McpToolApproval.id}")
  match field "verdict", field "status" with
  | some v, none =>
    let verdict : Verdict ← decodeIn "verdict" v
    let fields : Array (String × Json) := match Profile.McpToolApproval.envelope verdict with
      | some e => #[("envelope", e)]
      | none => #[]
    pure (.obj fields)
  | none, some st =>
    let status : CallStatus ← decodeIn "status" st
    let fields : Array (String × Json) := match Profile.McpToolApproval.disposition status with
      | some d => #[("disposition", Json.str d)]
      | none => #[]
    pure (.obj fields)
  | _, _ => throw ("json", "expected exactly one of verdict and status")

/-- `{"profile": id, "verdict": v}` gives the verdict's envelope, `{"profile": id, "status": s}` the
status's disposition; each member is absent when the profile gives none. -/
def profile (inputText : String) : String := run do
  profileResult (← tag "json" (Json.parse inputText))

end Writ.Api
