import Writ.Codec.State

namespace Writ.Explore

/-- The identifier classes the key renames. Approver ids stay: only principals are renamed. Grant
ids stay too: `State.findGrant` takes the first valid grant in id order, so renaming them could
merge states that pick different grants. -/
inductive Cls where | call | digest | principal
  deriving BEq

/-- Objects whose keys are identifiers or names rather than field names, as reversed paths. -/
private def mapPaths : List (List String) := [["calls"], ["grants"], ["approvers"], ["failures"]]

/-- The class of a map key under the map at `path` (reversed). -/
private def keyClass : List String → Option Cls
  | ["calls"] => some .call
  | _ => none

/-- The class of a string value at `path` (reversed, map entries and array elements as `*`). -/
private def valueClass : List String → Option Cls
  | ["principal", "*", "approvers"] => some .principal
  | ["proposed_digest", "*", "calls"] | ["digest", "*", "calls"]
  | ["digest", "*", "generations", "*", "calls"] => some .digest
  | ["principal", "*", "tally", "*", "calls"] => some .principal
  | ["call", "request_id", "decision", "*", "calls"] => some .call
  | ["principal", "*", "grants"] => some .principal
  | ["call_digest", "*", "grants"] => some .digest
  | ["call", "*", "session_meters"] | ["call", "*", "entries", "ledger"] => some .call
  | ["digest", "*", "rejected_memory"] => some .digest
  | _ => none

private def idemPath : List String := ["idempotency_key", "*", "calls"]

/-- The idempotency key the alphabet sends for a call; the key renames it with its call. -/
def idemPrefix : String := "k-"

/-- The principal eligibility never admits; kept literal, like the requester. -/
def reservedPrincipal : String := "agent"

structure Names where
  calls : Array String := #[]
  digests : Array String := #[]
  principals : Array String := #[]

private def Names.get (n : Names) : Cls → Array String
  | .call => n.calls | .digest => n.digests | .principal => n.principals

private def Names.note (n : Names) (requester : String) (c : Cls) (s : String) : Names :=
  if c == .principal && (s == requester || s == reservedPrincipal) then n
  else if (n.get c).contains s then n
  else match c with
    | .call => { n with calls := n.calls.push s }
    | .digest => { n with digests := n.digests.push s }
    | .principal => { n with principals := n.principals.push s }

private def prefixOf : Cls → String
  | .call => "#c" | .digest => "#d" | .principal => "#p"

private def Names.rename (n : Names) (c : Cls) (s : String) : String :=
  match (n.get c).findIdx? (· == s) with
  | some i => prefixOf c ++ toString i
  | none => s

private def sortedKvs (kvs : Array (String × Json)) : Array (String × Json) :=
  kvs.qsort fun a b => Json.keyLt a.1 b.1

/-- First occurrences, walking the JSON in canonical order. -/
private partial def collect (requester : String) (path : List String) (n : Names) : Json → Names
  | .str s => match valueClass path with
    | some c => n.note requester c s
    | none => n
  | .arr xs => xs.foldl (collect requester ("*" :: path)) n
  | .obj kvs =>
    let isMap := mapPaths.contains path
    (sortedKvs kvs).foldl (init := n) fun n (k, v) =>
      if isMap then
        let n := match keyClass path with
          | some c => n.note requester c k
          | none => n
        collect requester ("*" :: path) n v
      else collect requester (k :: path) n v
  | _ => n

private partial def rename (n : Names) (path : List String) : Json → Json
  | .str s =>
    match valueClass path with
    | some c => .str (n.rename c s)
    | none =>
      if path == idemPath && s.startsWith idemPrefix then
        .str (idemPrefix ++ n.rename .call (toString (s.drop idemPrefix.length)))
      else .str s
  | .arr xs => .arr (xs.map (rename n ("*" :: path)))
  | .obj kvs =>
    let isMap := mapPaths.contains path
    .obj (kvs.map fun (k, v) =>
      if isMap then
        let k' := match keyClass path with
          | some c => n.rename c k
          | none => k
        (k', rename n ("*" :: path) v)
      else (k, rename n (k :: path) v))
  | j => j

/-- The abstract key of a state: its canonical JSON without `state_version` and `last_seq`, with
call ids, digests and approver principals other than the requester and `agent` renamed by first
occurrence in that JSON. Renaming is a bijection on each class, so equal keys mean states equal up
to renaming; states that are renamings of each other can still get different keys. -/
def key (s : State) : String :=
  let j := match toJson s with
    | .obj kvs => Json.obj (kvs.filter fun (k, _) => k != "state_version" && k != "last_seq")
    | j => j
  let names := collect s.requester [] {} j
  (rename names [] j).canonical

end Writ.Explore
