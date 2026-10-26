import Std.Data.HashMap
import Std.Data.HashSet
import Writ.Codec.Trace
import Writ.Explore.Alphabet

namespace Writ.Explore

structure Config where
  /-- Events after the first `session_start`. -/
  depth : Nat := 4
  maxStates : Nat := 20000
  deriving Repr

structure Result where
  traces : Array Trace
  states : Nat
  /-- The search stopped at `maxStates` before exploring every state up to `depth`. -/
  truncated : Bool
  deriving BEq

def pad5 (n : Nat) : String :=
  let d := toString n
  String.ofList (List.replicate (5 - d.length) '0') ++ d

/-- The same state up to the envelope fields `step` always moves, so its key is the same. -/
private def unchanged (s s' : State) : Bool :=
  s'.lastTime == s.lastTime && { s' with lastSeq := s.lastSeq, version := s.version } == s

/-- Breadth-first from `State.initial` over the alphabet, deduplicating states on `key`. Emits the
shortest trace for each accepted transition with a distinct (pre key, post key) pair, then the
first rejected transition found for each (event type, reason). `doc` is the layer-1 policy document
the traces carry, whose digest the session runs under. HashMap and HashSet serve lookups only, so
their order never reaches the output. -/
def run (stem : String) (p : Policy) (cfg : Config) (doc : Json := toJson p) : Result := Id.run do
  let digest := doc.digest
  let a := Alphabet.build p digest
  let s0 := State.initial digest
  let mut visited : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity.insert (key s0) 0
  -- Each state's shortest path, newest step first, so paths share their prefixes.
  let mut paths : Array (List TraceStep) := #[[]]
  let mut frontier : Array (Nat × State) := #[(0, s0)]
  let mut pairs : Std.HashSet (Nat × Nat) := {}
  let mut sampled : Std.HashSet String := {}
  let mut accepted : Array (Nat × TraceStep) := #[]
  let mut rejected : Array (String × Nat × TraceStep) := #[]
  let mut truncated := false
  for level in [0:cfg.depth + 1] do
    if truncated then break
    let mut next : Array (Nat × State) := #[]
    for (idx, s) in frontier do
      if truncated then break
      for c in a.events s do
        let kind := c.event.body.typeName
        if let some r := c.probe then
          if sampled.contains (kind ++ "/" ++ r.code) then continue
        let (s', v) := step p s c.event
        let st : TraceStep := ⟨c.event, some (v.toJsonWith s'.version)⟩
        match v with
        | .rejected r =>
          let k := kind ++ "/" ++ r.code
          unless sampled.contains k do
            sampled := sampled.insert k
            rejected := rejected.push (k, idx, st)
        | .ok _ _ =>
          let mut post := idx
          unless unchanged s s' do
            let k := key s'
            match visited.get? k with
            | some j => post := j
            | none =>
              if visited.size ≥ cfg.maxStates then
                truncated := true
                break
              post := paths.size
              visited := visited.insert k post
              paths := paths.push (st :: paths[idx]!)
              if level < cfg.depth then next := next.push (post, s')
          unless pairs.contains (idx, post) do
            pairs := pairs.insert (idx, post)
            accepted := accepted.push (idx, st)
    frontier := next
  let trace (id : String) (pre : Nat) (st : TraceStep) : Trace :=
    { id, policy := p, policyDoc := doc, steps := (st :: paths[pre]!).reverse }
  let traces := accepted.mapIdx (fun i (pre, st) => trace s!"{stem}/a/{pad5 i}" pre st) ++
    rejected.map fun (k, pre, st) => trace s!"{stem}/r/{k}" pre st
  pure { traces, states := visited.size, truncated }

end Writ.Explore
