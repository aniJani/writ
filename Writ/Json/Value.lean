namespace Writ

inductive Json where
  | null | bool (b : Bool) | num (n : Int) | str (s : String)
  | arr (xs : Array Json) | obj (kvs : Array (String × Json))
  deriving Repr, BEq, Inhabited

end Writ
