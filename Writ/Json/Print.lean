import Writ.Json.Value

namespace Writ
namespace Json

private def hexDigit (n : Nat) : Char := Nat.digitChar n

private def escapeInto (acc : String) (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\x08' => acc ++ "\\b"
    | '\x0c' => acc ++ "\\f"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        (((acc ++ "\\u00").push (hexDigit (c.toNat / 16))).push (hexDigit (c.toNat % 16)))
      else acc.push c) (acc.push '"') |>.push '"'

private def utf16 (s : String) : Array Nat :=
  s.foldl (fun acc c =>
    let n := c.toNat
    if n < 0x10000 then acc.push n
    else (acc.push (0xD800 + (n - 0x10000) / 0x400)).push (0xDC00 + (n - 0x10000) % 0x400)) #[]

private def unitsLt (a b : Array Nat) : Bool :=
  let rec go (i : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      match a[i]?, b[i]? with
      | none, some _ => true
      | some x, some y => if x == y then go (i + 1) fuel else x < y
      | _, _ => false
  go 0 (a.size + 1)

private def render (canon : Bool) : Json → String → String
  | .null, acc => acc ++ "null"
  | .bool true, acc => acc ++ "true"
  | .bool false, acc => acc ++ "false"
  | .num n, acc => acc ++ toString n
  | .str s, acc => escapeInto acc s
  | .arr xs, acc =>
    let (acc, _) := xs.attach.foldl (init := (acc.push '[', true)) fun (acc, first) ⟨x, _⟩ =>
      (render canon x (if first then acc else acc.push ','), false)
    acc.push ']'
  | .obj kvs, acc =>
    let items : Array { x // x ∈ kvs } :=
      if canon then kvs.attach.qsort fun a b => unitsLt (utf16 a.1.1) (utf16 b.1.1) else kvs.attach
    let (acc, _) := items.foldl (init := (acc.push '{', true)) fun (acc, first) ⟨(k, v), _⟩ =>
      let acc := escapeInto (if first then acc else acc.push ',') k
      (render canon v (acc.push ':'), false)
    acc.push '}'
termination_by j => sizeOf j
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_›; omega)
    | (have := Array.sizeOf_lt_of_mem ‹_›; simp at *; omega)

def compact (j : Json) : String := render false j ""

/-- A string as canonical JSON writes it, quotes included. -/
def quote (s : String) : String := escapeInto "" s

/-- The canonical key order: by UTF-16 code units. -/
def keyLt (a b : String) : Bool := unitsLt (utf16 a) (utf16 b)

def canonical (j : Json) : String := render true j ""

end Json
end Writ
