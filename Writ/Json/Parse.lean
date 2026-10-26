import Std.Data.HashSet
import Writ.Json.Value
import Writ.Json.Print

namespace Writ
namespace Json

private def maxDepth : Nat := 128

-- 2^53 - 1 has 16 digits, so a longer digit run is out of range without building the Int.
private def maxDigits : Nat := 16

private def maxInt : Nat := 9007199254740991

private def posText (cs : Array Char) (pos : Nat) : String :=
  let upto := min pos cs.size
  let (line, col) := (List.range upto).foldl
    (fun (acc : Nat × Nat) i => if cs[i]! == '\n' then (acc.1 + 1, 1) else (acc.1, acc.2 + 1)) (1, 1)
  s!"line {line}, column {col}"

private def fail (cs : Array Char) (pos : Nat) (msg : String) : Except String α :=
  .error s!"{msg} at {posText cs pos}"

private def skipWs (cs : Array Char) (pos : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    match cs[pos]? with
    | some ' ' | some '\t' | some '\n' | some '\r' => skipWs cs (pos + 1) fuel
    | _ => pos

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hex4 (cs : Array Char) (pos : Nat) : Except String Nat := do
  let mut n := 0
  for i in [0:4] do
    match cs[pos + i]? >>= hexVal? with
    | some d => n := n * 16 + d
    | none => fail cs (pos + i) "invalid \\u escape"
  return n

private def lit (cs : Array Char) (pos : Nat) (word : String) (v : Json) : Except String (Json × Nat) :=
  let w := word.toList
  if (List.range w.length).all (fun i => cs[pos + i]? == w[i]?) then .ok (v, pos + w.length)
  else fail cs pos "invalid literal"

private def digitsEnd (cs : Array Char) (pos : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    match cs[pos]? with
    | some c => if '0' ≤ c ∧ c ≤ '9' then digitsEnd cs (pos + 1) fuel else pos
    | none => pos

private def number (cs : Array Char) (pos : Nat) : Except String (Json × Nat) := do
  let neg := cs[pos]? == some '-'
  let start := if neg then pos + 1 else pos
  let stop := digitsEnd cs start (maxDigits + 1)
  if stop == start then fail cs start "expected digit"
  if stop - start > maxDigits then fail cs start "integer out of range"
  if cs[start]? == some '0' && stop - start > 1 then fail cs start "leading zero"
  match cs[stop]? with
  | some '.' | some 'e' | some 'E' => fail cs stop "only integers are allowed"
  | _ => pure ()
  let n := (List.range (stop - start)).foldl (fun acc i => acc * 10 + (cs[start + i]!.toNat - '0'.toNat)) 0
  if n > maxInt then fail cs start "integer out of range"
  return (.num (if neg then -(Int.ofNat n) else Int.ofNat n), stop)

private def strBody (cs : Array Char) : Nat → Nat → String → Except String (String × Nat)
  | 0, pos, _ => fail cs pos "unterminated string"
  | fuel + 1, pos, acc =>
    match cs[pos]? with
    | none => fail cs pos "unterminated string"
    | some '"' => .ok (acc, pos + 1)
    | some '\\' =>
      match cs[pos + 1]? with
      | some '"' => strBody cs fuel (pos + 2) (acc.push '"')
      | some '\\' => strBody cs fuel (pos + 2) (acc.push '\\')
      | some '/' => strBody cs fuel (pos + 2) (acc.push '/')
      | some 'b' => strBody cs fuel (pos + 2) (acc.push '\x08')
      | some 'f' => strBody cs fuel (pos + 2) (acc.push '\x0c')
      | some 'n' => strBody cs fuel (pos + 2) (acc.push '\n')
      | some 'r' => strBody cs fuel (pos + 2) (acc.push '\r')
      | some 't' => strBody cs fuel (pos + 2) (acc.push '\t')
      | some 'u' =>
        match hex4 cs (pos + 2) with
        | .error e => .error e
        | .ok hi =>
          if 0xD800 ≤ hi ∧ hi < 0xDC00 then
            if cs[pos + 6]? == some '\\' && cs[pos + 7]? == some 'u' then
              match hex4 cs (pos + 8) with
              | .error e => .error e
              | .ok lo =>
                if 0xDC00 ≤ lo ∧ lo < 0xE000 then
                  let cp := 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)
                  strBody cs fuel (pos + 12) (acc.push (Char.ofNat cp))
                else fail cs pos "invalid surrogate pair"
            else fail cs pos "lone surrogate"
          else if 0xDC00 ≤ hi ∧ hi < 0xE000 then fail cs pos "lone surrogate"
          else strBody cs fuel (pos + 6) (acc.push (Char.ofNat hi))
      | _ => fail cs (pos + 1) "invalid escape"
    | some c =>
      if c.toNat < 0x20 then fail cs pos "unescaped control character"
      else strBody cs fuel (pos + 1) (acc.push c)

private def string (cs : Array Char) (pos : Nat) : Except String (String × Nat) :=
  strBody cs (cs.size + 2) (pos + 1) ""

mutual
private def value (cs : Array Char) (depth : Nat) : Nat → Nat → Except String (Json × Nat)
  | 0, pos => fail cs pos "input too deeply nested"
  | fuel + 1, pos =>
    let pos := skipWs cs pos cs.size
    match cs[pos]? with
    | none => fail cs pos "unexpected end of input"
    | some 'n' => lit cs pos "null" .null
    | some 't' => lit cs pos "true" (.bool true)
    | some 'f' => lit cs pos "false" (.bool false)
    | some '"' => do
      let (s, p) ← string cs pos
      return (.str s, p)
    | some '[' =>
      if depth ≥ maxDepth then fail cs pos "nesting deeper than 128 levels"
      else
        let p := skipWs cs (pos + 1) cs.size
        if cs[p]? == some ']' then .ok (.arr #[], p + 1)
        else elems cs (depth + 1) fuel p #[]
    | some '{' =>
      if depth ≥ maxDepth then fail cs pos "nesting deeper than 128 levels"
      else
        let p := skipWs cs (pos + 1) cs.size
        if cs[p]? == some '}' then .ok (.obj #[], p + 1)
        else members cs (depth + 1) fuel p #[] {}
    | some c => if c == '-' || ('0' ≤ c ∧ c ≤ '9') then number cs pos else fail cs pos "unexpected character"

private def elems (cs : Array Char) (depth : Nat) : Nat → Nat → Array Json → Except String (Json × Nat)
  | 0, pos, _ => fail cs pos "input too deeply nested"
  | fuel + 1, pos, acc => do
    let (v, p) ← value cs depth fuel pos
    let p := skipWs cs p cs.size
    match cs[p]? with
    | some ',' => elems cs depth fuel (p + 1) (acc.push v)
    | some ']' => return (.arr (acc.push v), p + 1)
    | _ => fail cs p "expected ',' or ']'"

private def members (cs : Array Char) (depth : Nat) : Nat → Nat → Array (String × Json) → Std.HashSet String → Except String (Json × Nat)
  | 0, pos, _, _ => fail cs pos "input too deeply nested"
  | fuel + 1, pos, acc, seen => do
    let pos := skipWs cs pos cs.size
    if cs[pos]? != some '"' then fail cs pos "expected object key"
    let (k, p) ← string cs pos
    if seen.contains k then fail cs pos s!"duplicate key {(Json.str k).compact}"
    let p := skipWs cs p cs.size
    if cs[p]? != some ':' then fail cs p "expected ':'"
    let (v, p) ← value cs depth fuel (p + 1)
    let p := skipWs cs p cs.size
    match cs[p]? with
    | some ',' => members cs depth fuel (p + 1) (acc.push (k, v)) (seen.insert k)
    | some '}' => return (.obj (acc.push (k, v)), p + 1)
    | _ => fail cs p "expected ',' or '}'"
end

def parse (s : String) : Except String Json := do
  if s.startsWith "\uFEFF" then throw "byte order mark at start of input is not allowed"
  let cs := s.toList.toArray
  let (v, p) ← value cs 0 (cs.size + 2) 0
  let p := skipWs cs p cs.size
  if p < cs.size then fail cs p "unexpected trailing data"
  return v

/-! The string, whitespace, depth and position rules, shared with `Jcs`, which reads numbers as
text but must agree with this parser on everything else. -/

def nestingLimit : Nat := maxDepth

def scanWs (cs : Array Char) (pos : Nat) : Nat := skipWs cs pos cs.size

def scanString (cs : Array Char) (pos : Nat) : Except String (String × Nat) := string cs pos

def positionText (cs : Array Char) (pos : Nat) : String := posText cs pos

end Json
end Writ
