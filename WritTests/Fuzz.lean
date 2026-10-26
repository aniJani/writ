import WritTests.Fuzz.Gen

open Writ

namespace WritTests.Fuzz

def outcomes (seed len : Nat) : List Checks.Outcome := Checks.check (replay (genTrace seed len))

def batch (first count len : Nat) : List (List Checks.Outcome) :=
  (List.range count).map fun i => outcomes (first + i) len

def premiseTotal (os : List (List Checks.Outcome)) (checker premise : String) : Nat :=
  os.foldl (init := 0) fun acc o =>
    acc + ((o.find? (·.name == checker)).bind (·.premises.lookup premise)).getD 0

#guard (List.range 200).all fun i => (genTrace i 0).policy.check.isEmpty

#guard (List.range 200).all fun i => let (d, p) := genBadPolicy i; plantedFound d p

def fixed : List (List Checks.Outcome) := batch 1 400 40

#guard fixed.all (·.all (·.ok))

-- Every premise of every checker must occur at least this often in the batch, so a generator change
-- cannot make the guard above pass vacuously.
def minimums : List (String × String × Nat) :=
  Checks.checkers.flatMap fun c => c.premises.map (c.name, ·, 5)

#guard minimums.all fun (c, p, n) => premiseTotal fixed c p ≥ n

end WritTests.Fuzz
