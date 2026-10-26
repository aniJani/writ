import WritTests.Fuzz.Judge

open Writ WritTests.Fuzz

structure Opts where
  seed : Nat := 1
  traces : Nat := 1000
  length : Nat := 60
  shrink : Bool := true
  reports : Nat := 1
  stop : Bool := false
  mutant : Option String := none
  allMutants : Bool := false
  bad : Nat := 0

partial def parse (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--no-shrink" :: rest => parse { o with shrink := false } rest
  | "--stop" :: rest => parse { o with stop := true } rest
  | "--mutants" :: rest => parse { o with allMutants := true } rest
  | "--mutant" :: m :: rest => parse { o with mutant := some m } rest
  | flag :: v :: rest =>
    match v.toNat? with
    | none => .error s!"expected a number after {flag}"
    | some n =>
      match flag with
      | "--seed" => parse { o with seed := n } rest
      | "--traces" => parse { o with traces := n } rest
      | "--length" => parse { o with length := n } rest
      | "--reports" => parse { o with reports := n } rest
      | "--bad" => parse { o with bad := n } rest
      | _ => .error s!"unknown flag {flag}"
  | [flag] => .error s!"unknown or incomplete flag {flag}"

structure Tally where
  violations : Nat := 0
  firstSeed : Option Nat := none
  firstTrace : Option Nat := none
  reported : Nat := 0
  premises : List (String × Nat) := []
  deriving Inhabited

def pad (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)

structure Run where
  tallies : Array Tally
  steps : Nat
  ms : Nat
  first : Option String
  /-- Traces on which at least one checker that the baseline step passes reported a violation. -/
  caught : Nat

def campaign (o : Opts) (stepF : StepFn) (verbose : Bool) (baseline : Option StepFn := none) : IO Run := do
  let t0 ← IO.monoMsNow
  let mut tallies : Array Tally := Checks.checkers.toArray.map fun c => { premises := c.premises.map (·, 0) }
  let mut steps := 0
  let mut shrinkMs := 0
  let mut first : Option String := none
  let mut caught := 0
  for i in [0:o.traces] do
    if o.stop && first.isSome then break
    let seed := o.seed + i
    let g := genTrace seed o.length
    steps := steps + g.length
    let outs := Checks.check (replayWith stepF g)
    -- A mutant is caught only by a checker that the real kernel passes on the same trace.
    let base := match baseline with
      | some b => (Checks.check (replayWith b g)).map (·.ok)
      | none => outs.map fun _ => true
    let mut hit := false
    for ((out, j), clean) in (outs.zip (List.range outs.length)).zip base do
      let t := tallies[j]!
      let premises := (t.premises.zip out.premises).map fun ((n, a), (_, b)) => (n, a + b)
      let mut t := { t with premises }
      if let some (idx, msg) := (if clean then out.firstBad else none) then
        hit := true
        if first.isNone then
          let now ← IO.monoMsNow
          first := some s!"first violation: {out.name} after {i + 1} traces, {steps} steps, {now - t0 - shrinkMs} ms"
        t := { t with violations := t.violations + 1, firstSeed := t.firstSeed <|> some seed
                      firstTrace := t.firstTrace <|> some (i + 1) }
        if verbose && t.reported < o.reports then
          t := { t with reported := t.reported + 1 }
          IO.println s!"VIOLATION {out.name} seed {seed} (length {o.length}) at item {idx}: {msg}"
          if o.shrink then
            let s0 ← IO.monoMsNow
            let small := shrink stepF out.name g
            let s1 ← IO.monoMsNow
            shrinkMs := shrinkMs + (s1 - s0)
            let fb := (Checks.runWith (Checks.checkers.filter (·.name == out.name)) (replayWith stepF small)).head?.bind (·.firstBad)
            IO.println s!"-- writ-fuzz --seed {seed} --length {o.length}: {out.name} fails at item {(fb.map (·.1)).getD 0} ({(fb.map (·.2)).getD ""}), shrunk {g.length} -> {small.length} steps in {s1 - s0} ms"
            IO.println (showTrace stepF out.name small)
            IO.println ""
      tallies := tallies.set! j t
    if hit then caught := caught + 1
  let t1 ← IO.monoMsNow
  return { tallies, steps, ms := t1 - t0 - shrinkMs, first, caught }

/-- A mutant caught in fewer traces than this fails the mutation run: a small generator change could
otherwise drop it to none unnoticed. -/
def mutantFloor : Nat := 5

def badPolicies (o : Opts) : IO Bool := do
  let mut counts : List (String × Nat × Nat) := defects.map (·, 0, 0)
  for i in [0:o.bad] do
    let (d, p) := genBadPolicy (o.seed + i)
    let rejected := plantedFound d p
    counts := counts.map fun (n, k, miss) => if n == d then (n, k + 1, miss + (if rejected then 0 else 1)) else (n, k, miss)
    if !rejected && o.reports > 0 then IO.println s!"CHECK MISSED planted problem {d} (seed {o.seed + i}): {fmt p}"
  IO.println s!"bad policies {o.bad}"
  let mut ok := true
  for (n, k, miss) in counts do
    IO.println s!"    {pad n 40} {k} generated, {miss} without the planted Policy.check problem"
    ok := ok && miss == 0
  return ok

def usage : String :=
  "usage: writ-fuzz [--seed N] [--traces N] [--length N] [--reports N] [--no-shrink] [--stop] [--mutant NAME | --mutants] [--bad N]\n       writ-fuzz --judge <traces.jsonl>..."

/-- Every file is read and decoded before any trace is judged, so an input error judges nothing. -/
def judge (files : List String) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln s!"--judge needs at least one trace file\n{usage}"
    return 2
  let mut traces : Array Trace := #[]
  for f in files do
    -- An IO error's text names the path again on a second line; the message names it once.
    let bytes ← try IO.FS.readBinFile f catch e =>
      IO.eprintln s!"error: {f}: cannot read the file ({((toString e).splitOn "\n").headD ""})"
      return 2
    let some text := String.fromUTF8? bytes | do
      IO.eprintln s!"error: {f}: not valid UTF-8"
      return 2
    match parseTraces text with
    | .ok ts => traces := traces ++ ts.toArray
    | .error e =>
      IO.eprintln s!"error: {f}: {e}"
      return 2
  let mut n := 0
  for t in traces do
    for v in judgeTrace step t do
      IO.println v.render
      n := n + 1
  IO.println s!"judged {traces.size} traces, {n} violations"
  return if n == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  if let "--judge" :: files := args then return ← judge files
  let o ← match parse {} args with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"{e}\n{usage}"
      return 2
  if o.bad > 0 then
    return if ← badPolicies o then 0 else 1
  if o.allMutants then
    let mut short := 0
    for (name, f) in mutants do
      let r ← campaign o f false (some step)
      let fired := (Checks.checkers.zip r.tallies.toList).filterMap fun (c, t) =>
        if t.violations > 0 then some s!"{c.name}({t.violations})" else none
      if r.caught < mutantFloor then short := short + 1
      let first := (r.tallies.toList.filterMap (·.firstTrace)).foldl min o.traces
      let independent := (Checks.checkers.zip r.tallies.toList).any fun (c, t) => c.name != "inv" && t.violations > 0
      let only := if independent then "" else " ONLY by inv"
      let below := if r.caught < mutantFloor then ", BELOW FLOOR" else ""
      let verdict := if r.caught == 0 then "NOT CAUGHT"
        else s!"caught{only} in {r.caught} traces, first at trace {first}{below}"
      IO.println s!"{pad name 40} {verdict} | {" ".intercalate fired}"
    IO.println s!"{mutants.length - short} of {mutants.length} mutants caught in at least {mutantFloor} traces"
    return if short == 0 then 0 else 1
  let stepF := match o.mutant with
    | some m => ((mutants.find? (·.1 == m)).map (·.2)).getD step
    | none => step
  let r ← campaign o stepF true
  IO.println s!"traces {o.traces}, steps {r.steps}, {r.ms} ms (excluding shrinking), {r.steps * 1000 / max r.ms 1} steps/s"
  if let some f := r.first then IO.println f
  let mut bad := false
  for (c, t) in Checks.checkers.zip r.tallies.toList do
    let status := if t.violations == 0 then "ok" else s!"FAIL {t.violations} traces, first seed {t.firstSeed.getD 0}"
    bad := bad || t.violations > 0
    IO.println s!"{pad c.name 18} {status}"
    for (n, k) in t.premises do
      IO.println s!"    {pad n 36} {k}"
  return if bad then 1 else 0
