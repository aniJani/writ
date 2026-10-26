import Writ.Json.Value
import Writ.Json.Parse
import Writ.Json.Print
import Writ.Json.Sha256
import WritTests.JsonHelpers

namespace Writ

#guard Json.parse "{\"b\":1,\"a\":[true,null,\"x\"]}" == .ok (.obj #[("b", .num 1), ("a", .arr #[.bool true, .null, .str "x"])])
#guard (Json.parse "{\"b\":1,\"a\":2}").map Json.canonical == .ok "{\"a\":2,\"b\":1}"
#guard (Json.parse "{\"b\":1,\"a\":2}").map Json.compact == .ok "{\"b\":1,\"a\":2}"

#guard (Json.parse "\"\\u00e9\"") == .ok (.str "é")
#guard (Json.parse "\"\\ud83d\\ude00\"") == .ok (.str "😀")
#guard (Json.parse "\"\\u0000\"").map Json.compact == .ok "\"\\u0000\""
#guard (Json.parse "\"\\ud800\"").isOk == false
#guard (Json.parse "\"a\tb\"").isOk == false
#guard (Json.parse "{\"z\":1,\"é\":2}").map Json.canonical == .ok "{\"z\":1,\"é\":2}"
#guard (Json.parse "{\"\\uffff\":1,\"\\ud83d\\ude00\":2}").map Json.canonical == .ok "{\"😀\":2,\"\uffff\":1}"

#guard (Json.parse "").isOk == false
#guard (Json.parse "{} {}").isOk == false
#guard (Json.parse "{\"a\":1,\"a\":2}").isOk == false
#guard (Json.parse "{\"a\\nb\":1,\"a\\nb\":2}") == .error "duplicate key \"a\\nb\" at line 1, column 11"
#guard (Json.parse (String.join (List.replicate 129 "[") ++ String.join (List.replicate 129 "]"))).isOk == false
#guard (Json.parse (String.join (List.replicate 128 "[") ++ String.join (List.replicate 128 "]"))).isOk
#guard (Json.parse "1.5").isOk == false
#guard (Json.parse "1e3").isOk == false
#guard (Json.parse "9007199254740992").isOk == false
#guard (Json.parse "9007199254740991").isOk
#guard (Json.parse "-9007199254740991").isOk
#guard (Json.parse (String.ofList (List.replicate 400 '9'))).isOk == false
#guard (Json.parse ("\"" ++ String.ofList (List.replicate 1000000 'x') ++ "\"")).isOk

#guard sha256Hex "".toUTF8 == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard sha256Hex "abc".toUTF8 == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard sha256Hex (String.ofList (List.replicate 1000000 'a')).toUTF8 == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
#guard (Json.num 1).digest == "sha256:" ++ sha256Hex "1".toUTF8

def nextSeed (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def pick (s : Nat) (n : Nat) : Nat := (s / 65536) % n

def genStr (s : Nat) : String :=
  let pool : Array String := #["a", "Z", "é", "😀", "\"", "\\", "\u0000", "\n", "\t", "\u001f", "/", " "]
  let n := pick s 6
  (List.range n).foldl (fun (acc : String × Nat) _ =>
    let s' := nextSeed acc.2
    (acc.1 ++ pool[pick s' pool.size]!, s')) ("", s) |>.1

def genInt (s : Nat) : Int :=
  let b : Int := 9007199254740991
  match pick s 6 with
  | 0 => b | 1 => -b | 2 => b - 1 | 3 => 0 | 4 => -(Int.ofNat (pick s 1000)) | _ => Int.ofNat (pick s 100000)

def genJson : Nat → Nat → Json × Nat
  | 0, s => ((if pick s 2 == 0 then .null else .bool (pick (nextSeed s) 2 == 0)), nextSeed (nextSeed s))
  | fuel + 1, s =>
    let s := nextSeed s
    match pick s 7 with
    | 0 => (.null, s)
    | 1 => (.bool (pick (nextSeed s) 2 == 0), nextSeed s)
    | 2 => (.num (genInt (nextSeed s)), nextSeed (nextSeed s))
    | 3 | 4 => (.str (genStr (nextSeed s)), nextSeed (nextSeed s))
    | 5 =>
      let n := pick (nextSeed s) 4
      let r := (List.range n).foldl (fun (acc : Array Json × Nat) _ =>
        let (v, s') := genJson fuel acc.2
        (acc.1.push v, s')) (#[], nextSeed s)
      (.arr r.1, r.2)
    | _ =>
      let n := pick (nextSeed s) 4
      let r := (List.range n).foldl (fun (acc : Array (String × Json) × Nat) i =>
        let (v, s') := genJson fuel acc.2
        (acc.1.push (toString i ++ genStr s', v), nextSeed s')) (#[], nextSeed s)
      (.obj r.1, r.2)

def genMany : Nat → Nat → List Json
  | 0, _ => []
  | n + 1, s => let (v, s') := genJson 4 s; v :: genMany n s'

def roundTrips (v : Json) : Bool :=
  Json.parse (Json.compact v) == .ok v &&
  match Json.parse (Json.canonical v) with
  | .ok w => w.canonical == v.canonical
  | .error _ => false

#guard (genMany 500 12345).length == 500
#guard (genMany 500 12345).all roundTrips
#guard ((genMany 500 12345).filter fun v => match v with | .obj _ | .arr _ => true | _ => false).length > 100

#guard Json.parse "\uFEFF{}" == .error "byte order mark at start of input is not allowed"
#guard !(Json.parse " \uFEFF{}").isOk
#guard Json.parse "{}" == .ok (.obj #[])

end Writ
