import Writ
import WritSpec

open Writ

def script (p : Policy) (steps : List (Nat × EventBody)) (digest : String := "pd") :
    State × List Verdict :=
  let rec go (s : State) (seq : Nat) (acc : List Verdict) : List (Nat × EventBody) → State × List Verdict
    | [] => (s, acc.reverse)
    | (t, b) :: rest =>
      let (s', v) := step p s ⟨seq, t, s.version, none, b⟩
      go s' (seq + 1) (v :: acc) rest
  go (State.initial digest) 1 [] steps

def checkedScript (p : Policy) (steps : List (Nat × EventBody)) (digest : String := "pd") :
    State × List Verdict × Bool :=
  let rec go (s : State) (seq : Nat) (acc : List Verdict) (ok : Bool) :
      List (Nat × EventBody) → State × List Verdict × Bool
    | [] => (s, acc.reverse, ok)
    | (t, b) :: rest =>
      let (s', v) := step p s ⟨seq, t, s.version, none, b⟩
      go s' (seq + 1) (v :: acc) (ok && Inv.check p s') rest
  let s₀ := State.initial digest
  go s₀ 1 [] (Inv.check p s₀) steps

def last (r : State × List Verdict) : Verdict :=
  r.2.getLast?.getD (.rejected .notStarted)

def lastChecked (r : State × List Verdict × Bool) : Verdict := last (r.1, r.2.1)
