import WritTests.Fuzz.Mutants

open Writ

namespace WritTests.Fuzz

structure Violation where
  trace : String
  step : Nat
  checker : String
  message : String
  deriving Repr

/-- Checker messages embed `reprStr` values, which wrap; a violation prints on one line. -/
def oneLine (s : String) : String :=
  (s.foldl (init := ("", false)) fun (acc, gap) ch =>
    if ch.isWhitespace then (acc, true)
    else ((if gap && !acc.isEmpty then acc.push ' ' else acc).push ch, false)).1

def Violation.render (v : Violation) : String := s!"{oneLine v.trace} step {v.step} {v.checker}: {oneLine v.message}"

/-- A corpus trace is one session's events applied to one state in order, as `Trace.replay` runs
them, so every step belongs to session instance 0 and its item index is its event index. The
stored ledger before the trace is the one its first accepted `session_start` brings; a rejected start
changes nothing (`frame`), so the first start of any kind is only the fallback. -/
def corpusChecksTrace (stepF : StepFn) (t : Trace) : Checks.Trace :=
  let (_, steps) := t.steps.foldl (init := (State.initial t.digest, (#[] : Array Checks.TStep))) fun (s, acc) st =>
    let (s', v) := stepF t.policy s st.event
    (s', acc.push ⟨0, s, st.event, v, s'⟩)
  let starts := steps.toList.filterMap fun st => match st.event.body with
    | .sessionStart _ _ _ _ _ l => some (l, (Checks.decisionOf st.verdict).isSome)
    | _ => none
  let initLedger := (((starts.find? (·.2)).orElse fun _ => starts.head?).map (·.1)).getD {}
  { policy := t.policy, initLedger, items := steps.toList.map .step }

def judgeTrace (stepF : StepFn) (t : Trace) : List Violation :=
  let vs := (Checks.check (corpusChecksTrace stepF t)).filterMap fun o =>
    o.firstBad.map fun (i, msg) => { trace := t.id, step := i, checker := o.name, message := msg }
  vs.mergeSort (·.step ≤ ·.step)

/-- A proposal after a kill. The recorded verdict is the one `proposeIgnoresKill` gives, `allowed`,
which the kill checkers must reject; the kernel denies it `killed`. -/
def killSample : String :=
  "{\"schema\":\"writ.trace/1\",\"id\":\"judge/propose-after-kill\",\"policy\":{\"writ\":\"0.1\",\"approver_roles\":[\"owner\"],\"actions\":{\"ping\":{\"consent\":\"none\"}}},\"events\":[" ++
  "{\"event\":{\"type\":\"session_start\",\"seq\":1,\"time\":0,\"state_version\":0,\"session_id\":\"s1\",\"requester\":\"u1\",\"permissions\":[],\"approvers\":{},\"ledger\":{}},\"expect\":{\"verdict\":\"accepted\"}}," ++
  "{\"event\":{\"type\":\"kill\",\"seq\":2,\"time\":1,\"state_version\":1},\"expect\":{\"verdict\":\"accepted\"}}," ++
  "{\"event\":{\"type\":\"propose\",\"seq\":3,\"time\":2,\"state_version\":2,\"call_id\":\"c1\",\"tool\":\"ping\",\"call_digest\":\"d1\",\"guards\":{},\"escalators\":{}},\"expect\":{\"verdict\":\"accepted\",\"decision\":\"allowed\"}}]}"

def judgeText (text : String) (stepF : StepFn) : List Violation :=
  match parseTraces text with
  | .ok ts => ts.flatMap (judgeTrace stepF)
  | .error e => [{ trace := "self-test", step := 0, checker := "decode", message := e }]

def proposeIgnoresKill : StepFn := fun p s e =>
  match e.body with
  | .propose .. =>
    reroute p s e (Checks.decisionOf · == some (.denied .killed)) p { s with killed := false } e ({ · with killed := s.killed })
  | _ => step p s e

/-- Another session's committed 4000 arrives through `ledger_sync`, so a 2000 proposal no longer fits
the 5000 principal cap and is denied `meter_exceeded`. -/
def syncSample : String :=
  "{\"schema\":\"writ.trace/1\",\"id\":\"judge/synced-foreign-spend\",\"policy\":{\"writ\":\"0.1\",\"meters\":{\"usd_day\":{\"currency\":\"USD\",\"cap\":5000,\"scope\":\"principal\",\"window_ms\":86400000}},\"actions\":{\"buy\":{\"consent\":\"none\",\"meters\":[\"usd_day\"]}}},\"events\":[" ++
  "{\"event\":{\"type\":\"session_start\",\"seq\":1,\"time\":0,\"state_version\":0,\"session_id\":\"s2\",\"requester\":\"u1\",\"permissions\":[],\"approvers\":{},\"ledger\":{}},\"expect\":{\"verdict\":\"accepted\"}}," ++
  "{\"event\":{\"type\":\"ledger_sync\",\"seq\":2,\"time\":1,\"state_version\":1,\"ledger\":{\"version\":1,\"entries\":[{\"meter\":\"usd_day\",\"session\":\"s1\",\"call\":\"c1\",\"time\":0,\"amount\":\"4000\",\"committed\":true}]}},\"expect\":{\"verdict\":\"accepted\"}}," ++
  "{\"event\":{\"type\":\"propose\",\"seq\":3,\"time\":2,\"state_version\":2,\"call_id\":\"c1\",\"tool\":\"buy\",\"call_digest\":\"d1\",\"cost\":{\"amount\":\"2000\",\"currency\":\"USD\"},\"guards\":{},\"escalators\":{}},\"expect\":{\"verdict\":\"accepted\",\"decision\":\"denied\",\"reason\":\"meter_exceeded\"}}]}"

/-- Counts only this session's entries at propose, as a kernel that dropped the synced ones would. -/
def proposeIgnoresSyncedEntries : StepFn := fun p s e =>
  match e.body with
  | .propose .. =>
    reroute p s e (Checks.decisionOf · == some (.denied .meterExceeded)) p
      { s with ledger := { s.ledger with entries := s.ledger.entries.filter (·.session == s.sessionId) } } e
      ({ · with ledger := s.ledger })
  | _ => step p s e

#guard (judgeText syncSample step).isEmpty
#guard (judgeText syncSample proposeIgnoresSyncedEntries).any fun v => v.step == 2 && v.checker == "proposeOrder"
#guard (match parseTraces syncSample with | .ok [t] => t.replay.ok | _ => false)

/-- The first start names the wrong policy digest and is rejected; the retry brings a fresh store
holding another session's 4000, so a 2000 proposal is denied `meter_exceeded`. -/
def retriedStartSample : String :=
  "{\"schema\":\"writ.trace/1\",\"id\":\"judge/retried-start\",\"policy\":{\"writ\":\"0.1\",\"meters\":{\"usd_day\":{\"currency\":\"USD\",\"cap\":5000,\"scope\":\"principal\",\"window_ms\":86400000}},\"actions\":{\"buy\":{\"consent\":\"none\",\"meters\":[\"usd_day\"]}}},\"events\":[" ++
  "{\"event\":{\"type\":\"session_start\",\"seq\":1,\"time\":0,\"state_version\":0,\"session_id\":\"s2\",\"policy_digest\":\"sha256:wrong\",\"requester\":\"u1\",\"permissions\":[],\"approvers\":{},\"ledger\":{}},\"expect\":{\"verdict\":\"rejected\",\"reason\":\"policy_digest_mismatch\"}}," ++
  "{\"event\":{\"type\":\"session_start\",\"seq\":2,\"time\":0,\"state_version\":0,\"session_id\":\"s2\",\"requester\":\"u1\",\"permissions\":[],\"approvers\":{},\"ledger\":{\"version\":1,\"entries\":[{\"meter\":\"usd_day\",\"session\":\"s0\",\"call\":\"c0\",\"time\":0,\"amount\":\"4000\",\"committed\":true}]}},\"expect\":{\"verdict\":\"accepted\"}}," ++
  "{\"event\":{\"type\":\"propose\",\"seq\":3,\"time\":1,\"state_version\":1,\"call_id\":\"c1\",\"tool\":\"buy\",\"call_digest\":\"d1\",\"cost\":{\"amount\":\"2000\",\"currency\":\"USD\"},\"guards\":{},\"escalators\":{}},\"expect\":{\"verdict\":\"accepted\",\"decision\":\"denied\",\"reason\":\"meter_exceeded\"}}]}"

def startDropsEntries : StepFn := fun p s e =>
  match e.body with
  | .sessionStart sid pd req perms apprs l => step p s { e with body := .sessionStart sid pd req perms apprs { l with entries := [] } }
  | _ => step p s e

#guard (judgeText retriedStartSample step).isEmpty
#guard (judgeText retriedStartSample startDropsEntries).any fun v => v.step == 1 && v.checker == "t8Accounting"
#guard (match parseTraces retriedStartSample with | .ok [t] => t.replay.ok | _ => false)

#guard (judgeText killSample step).isEmpty
#guard (judgeText killSample proposeIgnoresKill).any fun v => v.step == 2 && v.checker == "killGate"
#guard (match parseTraces killSample with | .ok [t] => t.replay.ok | _ => true) == false

end WritTests.Fuzz
