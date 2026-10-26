import Writ.Codec.Policy
import Writ.Author.Layer2

namespace Writ

open Decoder Encode

def layer2Keys : List String := ["extends", "labels", "rules"]

/-- The fields a rule's `require` may set; every other action field is per-action only. -/
def strictFields : List String :=
  ["consent", "grantable", "exposed", "idempotent", "retry_after_unknown", "guards", "flags", "mode"]

private def member? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

/-- A document is layer 2 when it uses a layer-2 key; a misspelled one (`label`) leaves it layer 1,
so the layer-1 parser still reports it as an unknown field. -/
def isLayer2 (doc : Json) : Bool :=
  layer2Keys.any (member? doc · |>.isSome) ||
    match member? doc "actions" with
    | some (.obj acts) => acts.any fun (_, a) => (member? a "labels").isSome
    | _ => false

private def withoutKey (k : String) : Json → Json
  | .obj kvs => .obj (kvs.filter (·.1 != k))
  | j => j

/-- The document without its layer-2 keys, read by the layer-1 decoders at unchanged paths. -/
def layer1Part : Json → Json
  | .obj kvs => .obj (kvs.filterMap fun (k, v) =>
    if layer2Keys.contains k then none
    else if k == "actions" then
      some (k, match v with
        | .obj acts => .obj (acts.map fun (n, a) => (n, withoutKey "labels" a))
        | v => v)
    else some (k, v))
  | j => j

private def firstDup : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDup xs

instance : FromJson LabelDim where
  fromJson j := do
    let fs ← object ["order"] j
    let order ← req fs "order" strings
    at' "order" do
      if order.isEmpty then fail "expected at least one value"
      if let some v := firstDup order then fail s!"duplicate value \"{v}\""
    pure ⟨order⟩

instance : ToJson LabelDim where
  toJson d := obj [some ("order", strings d.order)]

def decodeExtendsPath : Json → Decoder String
  | .str "" => fail "expected a non-empty path"
  | j => string j

def decodeAtLeast : Json → Decoder String
  | .str s =>
    if s.startsWith ">=" && s.length > 2 then pure (String.ofList (s.toList.drop 2))
    else fail "expected \">=value\""
  | _ => fail "expected \">=value\""

def decodeGrantCap : Json → Decoder GrantCap
  | .null => pure .forbid
  | j@(.obj _) => do
    let fs ← object ["scope", "max_uses", "max_duration_ms", "any_args"] j
    pure (.cap (← opt fs "scope" FromJson.fromJson) (← opt fs "max_uses" nat)
      (← opt fs "max_duration_ms" nat) (← opt fs "any_args" bool))
  | _ => fail "expected null or an object"

def GrantCap.toJson : GrantCap → Json
  | .forbid => .null
  | .cap s u d a => obj [some' "scope" s Writ.toJson, some' "max_uses" u nat,
      some' "max_duration_ms" d nat, some' "any_args" a .bool]

def requireObject : Json → Decoder (Array (String × Json))
  | .obj kvs => do
    for (k, _) in kvs do
      unless strictFields.contains k do
        at' k <| fail <|
          if requirementFields.contains k then "not a strictness-ordered field" else "unknown field"
    pure kvs
  | _ => fail "expected an object"

instance : FromJson Require where
  fromJson j := do
    let fs ← requireObject j
    pure {
      consent := ← opt fs "consent" FromJson.fromJson
      grantable := ← opt fs "grantable" decodeGrantCap
      exposed := ← opt fs "exposed" bool
      idempotent := ← opt fs "idempotent" bool
      retryAfterUnknown := ← opt fs "retry_after_unknown" bool
      guards := ← dflt fs "guards" [] strings
      flags := ← dflt fs "flags" [] (array FromJson.fromJson)
      mode := ← opt fs "mode" FromJson.fromJson }

instance : ToJson Require where
  toJson r := obj [
    some' "consent" r.consent toJson,
    some' "grantable" r.grantable GrantCap.toJson,
    some' "exposed" r.exposed .bool,
    some' "idempotent" r.idempotent .bool,
    some' "retry_after_unknown" r.retryAfterUnknown .bool,
    when (!r.guards.isEmpty) "guards" (strings r.guards),
    when (!r.flags.isEmpty) "flags" (.arr (r.flags.map toJson).toArray),
    some' "mode" r.mode toJson]

instance : FromJson Rule where
  fromJson j := do
    let fs ← object ["when", "require"] j
    pure ⟨← req fs "when" (map decodeAtLeast), ← req fs "require" FromJson.fromJson⟩

instance : ToJson Rule where
  toJson r := obj [some ("when", encodeMap (fun v => .str (">=" ++ v)) r.when),
    some ("require", toJson r.require)]

private def actionLabels : Json → Decoder (List (String × String))
  | .obj kvs => dflt kvs "labels" [] (map string)
  | _ => pure []

/-- Layer-1 fields go through the layer-1 decoders first, so a document that is both a bad layer-1
policy and a bad layer-2 one reports the layer-1 error. -/
instance : FromJson Policy2 where
  fromJson j := do
    let base : Policy ← FromJson.fromJson (layer1Part j)
    let fs := match j with
      | .obj kvs => kvs
      | _ => #[]
    let «extends» ← dflt fs "extends" [] (array decodeExtendsPath)
    let labels ← dflt fs "labels" [] (map FromJson.fromJson)
    let rules ← dflt fs "rules" [] (array FromJson.fromJson)
    let labelsOf ← dflt fs "actions" [] (map actionLabels)
    pure {
      base := { base with actions := [] }
      «extends», labels, rules
      actions := base.actions.map fun (n, r) => (n, ⟨r, (labelsOf.lookup n).getD []⟩) }

instance : ToJson Policy2 where
  toJson p :=
    let base := match toJson { p.base with actions := [] } with
      | .obj kvs => kvs
      | _ => #[]
    let action (a : Action2) : Json := match toJson a.req with
      | .obj kvs => .obj (if a.labels.isEmpty then kvs else kvs.push ("labels", encodeMap .str a.labels))
      | j => j
    let rest := obj [
      when (!p.«extends».isEmpty) "extends" (strings p.«extends»),
      when (!p.labels.isEmpty) "labels" (encodeMap toJson p.labels),
      when (!p.rules.isEmpty) "rules" (.arr (p.rules.map toJson).toArray),
      when (!p.actions.isEmpty) "actions" (encodeMap action p.actions)]
    match rest with
    | .obj kvs => .obj (base ++ kvs)
    | _ => .obj base

def Policy2.parseDoc (text : String) : Except String (Policy2 × Json) := do
  let j ← Json.parse text
  match (decode j : Except DecodeError Policy2) with
  | .ok p => pure (p, j)
  | .error e => throw e.render

/-- Per-action fields rules may not set, joined across the files that name an action. -/
def fileJoinedFields : List String :=
  ["consent_if_cost_over", "escalate", "max_attempts", "approval_ttl_ms", "authorized_ttl_ms"]

/-- Per-action fields every file that writes them must agree on: neither a rule nor a join sets them. -/
def agreeFields : List String :=
  requirementFields.filter fun f => !strictFields.contains f && !fileJoinedFields.contains f

def DocFacts.ofJson (j : Json) : DocFacts where
  policyKeys := match j with
    | .obj kvs => kvs.toList.map (·.1)
    | _ => []
  actionFields := match member? j "actions" with
    | some (.obj acts) => acts.toList.map fun (n, a) => (n, match a with
      | .obj fs => fs.toList.filterMap fun (k, v) =>
        if agreeFields.contains k then some (k, v.canonical) else none
      | _ => [])
    | _ => []

def File2.parseDoc (text : String) (name : String := "") : Except String File2 := do
  let (policy, j) ← Policy2.parseDoc text
  pure { policy, facts := DocFacts.ofJson j, name }

/-- Canonical JSON of a layer-1 policy, through the layer-1 printer: like every re-encoding, it
drops `$schema`, `review`, `messages`, `source` and written defaults. -/
def Policy.toJsonText (p : Policy) : String := (toJson p).canonical

end Writ
