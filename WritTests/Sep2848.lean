import Writ
import WritTests.Corpus

open Writ

namespace WritTests.Sep2848

def mapping : String := include_str "../corpus/sep-2848.json"
def axiomsText : String := include_str "../WritProofs/Axioms.lean"

def traceIds : List String :=
  WritTests.Corpus.files.flatMap fun (_, text) => (WritTests.Corpus.tracesOf text).map (·.id)

def pinned (axioms name : String) : Bool :=
  (axioms.splitOn ("#print axioms Writ.Proofs." ++ name ++ "\n")).length ≥ 2

def strings : Json → Option (List String)
  | .arr xs => xs.toList.mapM fun | .str s => some s | _ => none
  | _ => none

def rowFields : List String := ["n", "text", "traces", "theorems", "host", "excluded"]

def rowProblems (ids : List String) (axioms : String) (row : Json) : List String :=
  let key := WritTests.Corpus.keyOf row
  let label := match key "n" with
    | some (.num n) => s!"statement {n}"
    | _ => "a statement"
  let unknown := match row with
    | .obj kvs => kvs.toList.filterMap fun (k, _) =>
        if rowFields.contains k then none else some s!"{label}: unknown field {k}"
    | _ => [s!"{label}: not an object"]
  let text := match key "text" with
    | some (.str s) => if s.isEmpty then [s!"{label}: empty text"] else []
    | _ => [s!"{label}: text missing"]
  let body := match key "traces", key "theorems", key "excluded" with
    | none, none, some (.str r) => if r.isEmpty then [s!"{label}: empty excluded reason"] else []
    | some ts, some hs, none =>
      match strings ts, strings hs with
      | some (t :: ts), some (h :: hs) =>
        ((t :: ts).filter (!ids.contains ·)).map (s!"{label}: no corpus trace has id {·}") ++
          ((h :: hs).filter (!pinned axioms ·)).map (s!"{label}: {·} is not pinned in WritProofs/Axioms.lean")
      | _, _ => [s!"{label}: traces and theorems must be non-empty lists of strings"]
    | _, _, _ => [s!"{label}: needs traces and theorems, or an excluded reason, not both"]
  unknown ++ text ++ body

def problems (ids : List String) (axioms text : String) : List String :=
  match Json.parse text with
  | .error e => ["parse: " ++ e]
  | .ok j =>
    let key := WritTests.Corpus.keyOf j
    let sep := if key "sep" == some (.num 2848) then [] else ["sep must be 2848"]
    let url := match key "spec_url" with
      | some (.str _) => []
      | _ => ["spec_url missing"]
    match key "statements" with
    | some (.arr rows) =>
      let ns := rows.toList.filterMap fun r => match WritTests.Corpus.keyOf r "n" with
        | some (.num n) => some n
        | _ => none
      let counts := (List.range 7).filterMap fun i =>
        let c := ns.count (Int.ofNat (i + 1))
        if c == 1 then none else some s!"statement {i + 1} appears {c} times"
      let extra := (ns.filter fun n => n < 1 ∨ 7 < n).map (s!"no statement {·} in SEP-2848")
      let unnumbered := if ns.length == rows.size then [] else ["a statement has no number"]
      sep ++ url ++ counts ++ extra ++ unnumbered ++ rows.toList.flatMap (rowProblems ids axioms)
    | _ => sep ++ url ++ ["statements missing"]

#eval show IO Unit from do
  let ps := problems traceIds axiomsText mapping
  unless ps.isEmpty do throw (IO.userError ("corpus/sep-2848.json: " ++ String.intercalate "; " ps))

def row (body : String) : String := "{\"n\":1,\"text\":\"t\"," ++ body ++ "}"

def doc (rows : List String) : String :=
  "{\"sep\":2848,\"spec_url\":\"u\",\"statements\":[" ++ String.intercalate "," rows ++ "]}"

def okRows : List String := (List.range 7).map fun i =>
  "{\"n\":" ++ toString (i + 1) ++ ",\"text\":\"t\",\"excluded\":\"r\"}"

def check (text : String) : List String :=
  problems ["a/x"] "#guard_msgs in #print axioms Writ.Proofs.kill_accepted_sets\n#print axioms Writ.Proofs.frame\n" text

#guard check (doc okRows) == []
#guard check (doc (row "\"traces\":[\"a/x\"],\"theorems\":[\"frame\"]" :: okRows.drop 1)) == []
#guard check (doc (okRows.drop 1)) == ["statement 1 appears 0 times"]
#guard check (doc (okRows ++ [okRows.head!])) == ["statement 1 appears 2 times"]
#guard check (doc (okRows ++ ["{\"n\":8,\"text\":\"t\",\"excluded\":\"r\"}"])) == ["no statement 8 in SEP-2848"]
#guard check (doc (row "\"traces\":[\"a/x\"],\"theorems\":[\"frame\"],\"excluded\":\"r\"" :: okRows.drop 1)) ==
  ["statement 1: needs traces and theorems, or an excluded reason, not both"]
#guard check (doc (row "\"traces\":[],\"theorems\":[\"frame\"]" :: okRows.drop 1)) ==
  ["statement 1: traces and theorems must be non-empty lists of strings"]
#guard check (doc (row "\"traces\":[\"a/y\"],\"theorems\":[\"frame\"]" :: okRows.drop 1)) ==
  ["statement 1: no corpus trace has id a/y"]
#guard check (doc (row "\"traces\":[\"a/x\"],\"theorems\":[\"kill\"]" :: okRows.drop 1)) ==
  ["statement 1: kill is not pinned in WritProofs/Axioms.lean"]
#guard check (doc (row "\"theorems\":[\"frame\"]" :: okRows.drop 1)) ==
  ["statement 1: needs traces and theorems, or an excluded reason, not both"]
#guard check (doc (row "\"excluded\":\"r\",\"theorem\":[]" :: okRows.drop 1)) == ["statement 1: unknown field theorem"]
#guard check ((doc okRows).replace "2848," "2484,") == ["sep must be 2848"]
#guard match check "{" with
  | [e] => e.startsWith "parse: "
  | _ => false

end WritTests.Sep2848
