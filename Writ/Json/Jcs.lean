import Std.Data.HashSet
import Writ.Json.Parse

namespace Writ

/-- JSON whose numbers are kept as the canonical text RFC 8785 prints for them, for digesting
documents Writ does not author, such as MCP tool definitions. -/
inductive JcsValue where
  | null | bool (b : Bool) | num (canonical : String) | str (s : String)
  | arr (xs : Array JcsValue) | obj (kvs : Array (String × JcsValue))
  deriving Repr, BEq, Inhabited

namespace Jcs

/-- Up to 15 significant digits every decimal round-trips through a double, so the shortest form
ECMAScript prints for the nearest double is the literal's own digits. -/
def maxSignificantDigits : Nat := 15

/-- Well inside the normal doubles, where the 15-digit round trip holds. -/
def maxExponent : Int := 300

def pathText (path : Array String) : String :=
  path.foldl (fun acc seg =>
    if acc.isEmpty then seg
    else if seg.startsWith "[" then acc ++ seg
    else acc ++ "." ++ seg) ""

private def fail (cs : Array Char) (pos : Nat) (path : Array String) (msg : String) : Except String α :=
  let p := pathText path
  .error s!"{if p.isEmpty then "" else p ++ ": "}{msg} at {Json.positionText cs pos}"

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def digitsEnd (cs : Array Char) (pos : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 => if (cs[pos]?.map isDigit).getD false then digitsEnd cs (pos + 1) fuel else pos

private def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- ECMAScript Number::toString of `0.d₁d₂…dₖ × 10^n`, for digits `ds` without leading or
trailing zeros. -/
def esString (ds : List Char) (n : Int) : String :=
  let k : Int := ds.length
  let s := String.ofList ds
  if k ≤ n ∧ n ≤ 21 then s ++ zeros (n - k).toNat
  else if 0 < n ∧ n ≤ 21 then String.ofList (ds.take n.toNat) ++ "." ++ String.ofList (ds.drop n.toNat)
  else if -6 < n ∧ n ≤ 0 then "0." ++ zeros (-n).toNat ++ s
  else
    let e := n - 1
    let exp := (if e ≥ 0 then "+" else "-") ++ toString e.natAbs
    match ds with
    | [d] => String.singleton d ++ "e" ++ exp
    | d :: rest => String.singleton d ++ "." ++ String.ofList rest ++ "e" ++ exp
    | [] => "0"

private def numberText (cs : Array Char) (pos : Nat) (path : Array String) :
    Except String (String × Nat) := do
  let neg := cs[pos]? == some '-'
  let intStart := if neg then pos + 1 else pos
  let intEnd := digitsEnd cs intStart cs.size
  if intEnd == intStart then fail cs intStart path "expected digit"
  if cs[intStart]? == some '0' && intEnd - intStart > 1 then fail cs intStart path "leading zero"
  let (fracStart, fracEnd) ←
    if cs[intEnd]? == some '.' then do
      let e := digitsEnd cs (intEnd + 1) cs.size
      if e == intEnd + 1 then fail cs e path "expected digit after '.'"
      pure (intEnd + 1, e)
    else pure (intEnd, intEnd)
  let (exp, stop) ←
    if cs[fracEnd]? == some 'e' || cs[fracEnd]? == some 'E' then do
      let sgn := cs[fracEnd + 1]?
      let s := if sgn == some '+' || sgn == some '-' then fracEnd + 2 else fracEnd + 1
      let e := digitsEnd cs s cs.size
      if e == s then fail cs e path "expected digit in exponent"
      let n := (List.range (e - s)).foldl (fun acc i => acc * 10 + (cs[s + i]!.toNat - '0'.toNat)) 0
      pure ((if sgn == some '-' then -(Int.ofNat n) else Int.ofNat n), e)
    else pure (0, fracEnd)
  let digits := (List.range (intEnd - intStart)).map (fun i => cs[intStart + i]!) ++
    (List.range (fracEnd - fracStart)).map (fun i => cs[fracStart + i]!)
  let lead := digits.dropWhile (· == '0')
  let sig := (lead.reverse.dropWhile (· == '0')).reverse
  if sig.isEmpty then return ("0", stop)
  if sig.length > maxSignificantDigits then
    fail cs pos path s!"number has more than {maxSignificantDigits} significant digits"
  -- The value is 0.sig × 10^n, so its decimal exponent is n - 1.
  let n : Int := exp + (lead.length : Int) - (fracEnd - fracStart : Nat)
  if n - 1 > maxExponent || (n - 1 == maxExponent && sig != ['1']) || n - 1 < -maxExponent then
    fail cs pos path s!"number is outside 1e-{maxExponent} to 1e{maxExponent} in magnitude"
  return ((if neg then "-" else "") ++ esString sig n, stop)

private def lit (cs : Array Char) (pos : Nat) (path : Array String) (word : String) (v : JcsValue) :
    Except String (JcsValue × Nat) :=
  let w := word.toList
  if (List.range w.length).all (fun i => cs[pos + i]? == w[i]?) then .ok (v, pos + w.length)
  else fail cs pos path "invalid literal"

private def string (cs : Array Char) (pos : Nat) (path : Array String) : Except String (String × Nat) :=
  match Json.scanString cs pos with
  | .ok r => .ok r
  | .error e =>
    let p := pathText path
    .error (if p.isEmpty then e else p ++ ": " ++ e)

mutual
private def value (cs : Array Char) (depth : Nat) (path : Array String) :
    Nat → Nat → Except String (JcsValue × Nat)
  | 0, pos => fail cs pos path "input too deeply nested"
  | fuel + 1, pos =>
    let pos := Json.scanWs cs pos
    match cs[pos]? with
    | none => fail cs pos path "unexpected end of input"
    | some 'n' => lit cs pos path "null" .null
    | some 't' => lit cs pos path "true" (.bool true)
    | some 'f' => lit cs pos path "false" (.bool false)
    | some '"' => do
      let (s, p) ← string cs pos path
      return (.str s, p)
    | some '[' =>
      if depth ≥ Json.nestingLimit then
        fail cs pos path s!"nesting deeper than {Json.nestingLimit} levels"
      else
        let p := Json.scanWs cs (pos + 1)
        if cs[p]? == some ']' then .ok (.arr #[], p + 1)
        else elems cs (depth + 1) path fuel p #[]
    | some '{' =>
      if depth ≥ Json.nestingLimit then
        fail cs pos path s!"nesting deeper than {Json.nestingLimit} levels"
      else
        let p := Json.scanWs cs (pos + 1)
        if cs[p]? == some '}' then .ok (.obj #[], p + 1)
        else members cs (depth + 1) path fuel p #[] {}
    | some c =>
      if c == '-' || isDigit c then do
        let (t, p) ← numberText cs pos path
        return (.num t, p)
      else fail cs pos path "unexpected character"

private def elems (cs : Array Char) (depth : Nat) (path : Array String) :
    Nat → Nat → Array JcsValue → Except String (JcsValue × Nat)
  | 0, pos, _ => fail cs pos path "input too deeply nested"
  | fuel + 1, pos, acc => do
    let (v, p) ← value cs depth (path.push s!"[{acc.size}]") fuel pos
    let p := Json.scanWs cs p
    match cs[p]? with
    | some ',' => elems cs depth path fuel (p + 1) (acc.push v)
    | some ']' => return (.arr (acc.push v), p + 1)
    | _ => fail cs p path "expected ',' or ']'"

private def members (cs : Array Char) (depth : Nat) (path : Array String) :
    Nat → Nat → Array (String × JcsValue) → Std.HashSet String → Except String (JcsValue × Nat)
  | 0, pos, _, _ => fail cs pos path "input too deeply nested"
  | fuel + 1, pos, acc, seen => do
    let pos := Json.scanWs cs pos
    if cs[pos]? != some '"' then fail cs pos path "expected object key"
    let (k, p) ← string cs pos path
    if seen.contains k then fail cs pos (path.push k) s!"duplicate key {Json.quote k}"
    let p := Json.scanWs cs p
    if cs[p]? != some ':' then fail cs p path "expected ':'"
    let (v, p) ← value cs depth (path.push k) fuel (p + 1)
    let p := Json.scanWs cs p
    match cs[p]? with
    | some ',' => members cs depth path fuel (p + 1) (acc.push (k, v)) (seen.insert k)
    | some '}' => return (.obj (acc.push (k, v)), p + 1)
    | _ => fail cs p path "expected ',' or '}'"
end

/-- Parses under the rules of `Json.parse` (no byte order mark, duplicate keys refused, nesting at
most 128 levels), but keeps numbers: one with at most 15 significant digits and a magnitude of 0
or within 1e-300 to 1e300 is stored as ECMAScript prints it; any other is refused. Errors name the
JSON path. -/
def parse (text : String) : Except String JcsValue := do
  if text.startsWith "﻿" then throw "byte order mark at start of input is not allowed"
  let cs := text.toList.toArray
  let (v, p) ← value cs 0 #[] (cs.size + 2) 0
  let p := Json.scanWs cs p
  if p < cs.size then fail cs p #[] "unexpected trailing data"
  return v

end Jcs

namespace JcsValue

private def render : JcsValue → String → String
  | .null, acc => acc ++ "null"
  | .bool true, acc => acc ++ "true"
  | .bool false, acc => acc ++ "false"
  | .num t, acc => acc ++ t
  | .str s, acc => acc ++ Json.quote s
  | .arr xs, acc =>
    let (acc, _) := xs.attach.foldl (init := (acc.push '[', true)) fun (acc, first) ⟨x, _⟩ =>
      (render x (if first then acc else acc.push ','), false)
    acc.push ']'
  | .obj kvs, acc =>
    let items := kvs.attach.qsort fun a b => Json.keyLt a.1.1 b.1.1
    let (acc, _) := items.foldl (init := (acc.push '{', true)) fun (acc, first) ⟨(k, v), _⟩ =>
      let acc := (if first then acc else acc.push ',') ++ Json.quote k
      (render v (acc.push ':'), false)
    acc.push '}'
termination_by j => sizeOf j
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_›; omega)
    | (have := Array.sizeOf_lt_of_mem ‹_›; simp at *; omega)

/-- RFC 8785 canonical JSON: keys sorted by UTF-16 code units, the escapes of `Json.canonical`,
and each number as `Jcs.parse` stored it. -/
def canonical (v : JcsValue) : String := render v ""

end JcsValue

end Writ
