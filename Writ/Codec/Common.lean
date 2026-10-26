import Writ.Json.Decode
import Writ.Core.Policy

namespace Writ

/-- 2^256 has 78 digits. -/
def maxAmountDigits : Nat := 78

def decodeAmount : Json → Decoder Nat
  | .str s =>
    let digits := s.toList
    if digits.length > maxAmountDigits then
      Decoder.fail s!"amount has more than {maxAmountDigits} digits"
    else if digits.isEmpty || !digits.all (fun c => '0' ≤ c && c ≤ '9') then
      Decoder.fail "expected a decimal string of digits"
    else if digits.length > 1 && digits.head? == some '0' then
      Decoder.fail "expected no leading zero"
    else
      pure (digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  | _ => Decoder.fail "expected a decimal string"

def encodeAmount (n : Nat) : Json := .str (toString n)

/-- Decoding goes through the encoded names, so a new constructor cannot be forgotten. -/
def decodeEnum (all : List α) (code : α → String) : Json → Decoder α
  | .str s =>
    match all.find? (code · == s) with
    | some a => pure a
    | none =>
      Decoder.fail s!"unknown value \"{s}\", expected one of {", ".intercalate (all.map code)}"
  | _ => Decoder.fail "expected a string"

def encodeMap (enc : α → Json) (xs : List (String × α)) : Json :=
  let unique := xs.foldl (fun acc (k, v) => if acc.any (·.1 == k) then acc else acc ++ [(k, v)]) []
  .obj (unique.map fun (k, v) => (k, enc v)).toArray

def Mode.code : Mode → String | .enforce => "enforce" | .logOnly => "log_only"
def Flag.code : Flag → String
  | .readsPrivate => "reads_private" | .ingestsUntrusted => "ingests_untrusted"
  | .sendsExternal => "sends_external"
def GrantScope.code : GrantScope → String | .turn => "turn" | .session => "session"
def MeterScope.code : MeterScope → String | .session => "session" | .principal => "principal"
def EscalationScope.code : EscalationScope → String | .session => "session" | .tool => "tool"

instance : FromJson Mode := ⟨decodeEnum [.enforce, .logOnly] Mode.code⟩
instance : ToJson Mode := ⟨fun m => .str m.code⟩
instance : FromJson Flag := ⟨decodeEnum [.readsPrivate, .ingestsUntrusted, .sendsExternal] Flag.code⟩
instance : ToJson Flag := ⟨fun f => .str f.code⟩
instance : FromJson GrantScope := ⟨decodeEnum [.turn, .session] GrantScope.code⟩
instance : ToJson GrantScope := ⟨fun s => .str s.code⟩
instance : FromJson MeterScope := ⟨decodeEnum [.session, .principal] MeterScope.code⟩
instance : ToJson MeterScope := ⟨fun s => .str s.code⟩
instance : FromJson EscalationScope := ⟨decodeEnum [.session, .tool] EscalationScope.code⟩
instance : ToJson EscalationScope := ⟨fun s => .str s.code⟩

instance : FromJson Cost where
  fromJson j := do
    let fs ← Decoder.object ["amount", "currency"] j
    pure ⟨← Decoder.req fs "amount" decodeAmount, ← Decoder.req fs "currency" Decoder.string⟩

instance : ToJson Cost where
  toJson c := Encode.obj [some ("amount", encodeAmount c.amount), some ("currency", .str c.currency)]

end Writ
