import Writ.Json.Parse

namespace Writ

structure DecodeError where
  path : List String
  message : String
  deriving BEq, Repr

abbrev Decoder := ReaderT (List String) (Except DecodeError)

class FromJson (α : Type) where
  fromJson : Json → Decoder α

class ToJson (α : Type) where
  toJson : α → Json

def decode [FromJson α] (j : Json) : Except DecodeError α :=
  (FromJson.fromJson j).run []

export ToJson (toJson)

def DecodeError.render (e : DecodeError) : String :=
  let p := e.path.foldl (fun acc seg =>
    if acc.isEmpty then seg
    else if seg.startsWith "[" then acc ++ seg
    else acc ++ "." ++ seg) ""
  if p.isEmpty then e.message else p ++ ": " ++ e.message

namespace Decoder

def fail (message : String) : Decoder α := do
  throw { path := (← read), message }

def at' (seg : String) (d : Decoder α) : Decoder α :=
  withReader (· ++ [seg]) d

def string : Json → Decoder String
  | .str s => pure s
  | _ => fail "expected a string"

def bool : Json → Decoder Bool
  | .bool b => pure b
  | _ => fail "expected a boolean"

def int : Json → Decoder Int
  | .num n => pure n
  | _ => fail "expected an integer"

def nat : Json → Decoder Nat
  | .num n => if n < 0 then fail "expected a non-negative integer" else pure n.toNat
  | _ => fail "expected a non-negative integer"

def array (dec : Json → Decoder α) : Json → Decoder (List α)
  | .arr xs => do
    let mut out := #[]
    for h : i in [0:xs.size] do
      out := out.push (← at' s!"[{i}]" (dec xs[i]))
    pure out.toList
  | _ => fail "expected an array"

def strings : Json → Decoder (List String) := array string

/-- An object's members, after rejecting any key outside `allowed`. -/
def object (allowed : List String) : Json → Decoder (Array (String × Json))
  | .obj kvs => do
    for (k, _) in kvs do
      unless allowed.contains k do at' k (fail "unknown field")
    pure kvs
  | _ => fail "expected an object"

def map (dec : Json → Decoder α) : Json → Decoder (List (String × α))
  | .obj kvs => do
    let mut out := #[]
    for (k, v) in kvs do
      out := out.push (k, ← at' k (dec v))
    pure out.toList
  | _ => fail "expected an object"

def opt (fs : Array (String × Json)) (name : String) (dec : Json → Decoder α) :
    Decoder (Option α) :=
  match fs.find? (·.1 == name) with
  | some (_, v) => some <$> at' name (dec v)
  | none => pure none

def req (fs : Array (String × Json)) (name : String) (dec : Json → Decoder α) : Decoder α := do
  match ← opt fs name dec with
  | some a => pure a
  | none => at' name (fail "missing field")

def dflt (fs : Array (String × Json)) (name : String) (d : α) (dec : Json → Decoder α) :
    Decoder α := do
  pure ((← opt fs name dec).getD d)

end Decoder

namespace Encode

def obj (kvs : List (Option (String × Json))) : Json := .obj (kvs.filterMap id).toArray

def when (b : Bool) (name : String) (j : Json) : Option (String × Json) :=
  if b then some (name, j) else none

def some' (name : String) (o : Option α) (f : α → Json) : Option (String × Json) :=
  o.map fun a => (name, f a)

def strings (xs : List String) : Json := .arr (xs.map Json.str).toArray

def nat (n : Nat) : Json := .num n

end Encode

end Writ
