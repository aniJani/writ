import Writ.Codec.Policy
import Writ.Core.Event

namespace Writ

open Decoder Encode

def ApproverKind.code : ApproverKind → String | .human => "human" | .automated => "automated"
def Outcome.code : Outcome → String
  | .succeeded => "succeeded" | .failed => "failed" | .declined => "declined"

instance : FromJson ApproverKind := ⟨decodeEnum [.human, .automated] ApproverKind.code⟩
instance : ToJson ApproverKind := ⟨fun k => .str k.code⟩
instance : FromJson Outcome := ⟨decodeEnum [.succeeded, .failed, .declined] Outcome.code⟩
instance : ToJson Outcome := ⟨fun o => .str o.code⟩

instance : FromJson ApproverInfo where
  fromJson j := do
    let fs ← object ["principal", "kind", "roles"] j
    pure ⟨← req fs "principal" string, ← req fs "kind" FromJson.fromJson, ← req fs "roles" strings⟩

instance : ToJson ApproverInfo where
  toJson a := obj [some ("principal", .str a.principal), some ("kind", toJson a.kind),
    some ("roles", Encode.strings a.roles)]

instance : FromJson RequestId where
  fromJson j := do
    let fs ← object ["session", "call", "generation"] j
    pure ⟨← req fs "session" string, ← req fs "call" string, ← req fs "generation" nat⟩

instance : ToJson RequestId where
  toJson r := obj [some ("session", .str r.session), some ("call", .str r.call),
    some ("generation", Encode.nat r.generation)]

instance : FromJson MeterEntry where
  fromJson j := do
    let fs ← object ["meter", "session", "call", "time", "amount", "committed", "excess", "excess_at"] j
    pure ⟨← req fs "meter" string, ← req fs "session" string, ← req fs "call" string,
      ← req fs "time" nat, ← req fs "amount" decodeAmount, ← req fs "committed" bool,
      ← dflt fs "excess" 0 decodeAmount, ← dflt fs "excess_at" 0 nat⟩

instance : ToJson MeterEntry where
  toJson e := obj [
    some ("meter", .str e.meter), some ("session", .str e.session), some ("call", .str e.call),
    some ("time", Encode.nat e.time), some ("amount", encodeAmount e.amount),
    some ("committed", .bool e.committed),
    when (e.excess != 0) "excess" (encodeAmount e.excess),
    when (e.excessAt != 0) "excess_at" (Encode.nat e.excessAt)]

instance : FromJson Ledger where
  fromJson j := do
    let fs ← object ["version", "entries", "tombstone"] j
    pure ⟨← dflt fs "version" 0 nat, ← dflt fs "entries" [] (array FromJson.fromJson),
      ← dflt fs "tombstone" false bool⟩

instance : ToJson Ledger where
  toJson l := obj [
    when (l.version != 0) "version" (Encode.nat l.version),
    when (!l.entries.isEmpty) "entries" (.arr (l.entries.map toJson).toArray),
    when l.tombstone "tombstone" (.bool true)]

instance : FromJson Edit where
  fromJson j := do
    let fs ← object ["new_digest", "new_cost", "escalators"] j
    pure ⟨← req fs "new_digest" string, ← opt fs "new_cost" FromJson.fromJson,
      ← req fs "escalators" (map bool)⟩

def boolMap (xs : List (String × Bool)) : Json := encodeMap Json.bool xs

instance : ToJson Edit where
  toJson e := obj [some ("new_digest", .str e.newDigest), some' "new_cost" e.newCost toJson,
    some ("escalators", boolMap e.escalators)]

/-- Every host-supplied string in an event is limited, so one event cannot grow the state without
bound. `origin`, `audit` and the `ledger` object are not: the ledger comes from the kernel and the
binding, and its entries were limited when the events that created them were decoded. -/
def maxEventStringBytes : Nat := 512

namespace EventField

def str (j : Json) : Decoder String := do
  let s ← string j
  if s.utf8ByteSize > maxEventStringBytes then fail s!"longer than {maxEventStringBytes} bytes"
  else pure s

def strs : Json → Decoder (List String) := array str

def keyed (dec : Json → Decoder α) (j : Json) : Decoder (List (String × α)) := do
  if let .obj kvs := j then
    if kvs.any (·.1.utf8ByteSize > maxEventStringBytes) then
      fail s!"has a key longer than {maxEventStringBytes} bytes"
  Decoder.map dec j

def money (j : Json) : Decoder Cost := do
  let fs ← object ["amount", "currency"] j
  pure ⟨← req fs "amount" decodeAmount, ← req fs "currency" str⟩

def requestId (j : Json) : Decoder RequestId := do
  let fs ← object ["session", "call", "generation"] j
  pure ⟨← req fs "session" str, ← req fs "call" str, ← req fs "generation" nat⟩

def approverInfo (j : Json) : Decoder ApproverInfo := do
  let fs ← object ["principal", "kind", "roles"] j
  pure ⟨← req fs "principal" str, ← req fs "kind" FromJson.fromJson, ← req fs "roles" strs⟩

def edit (j : Json) : Decoder Edit := do
  let fs ← object ["new_digest", "new_cost", "escalators"] j
  pure ⟨← req fs "new_digest" str, ← opt fs "new_cost" money, ← req fs "escalators" (keyed bool)⟩

end EventField

def EventBody.typeName : EventBody → String
  | .sessionStart .. => "session_start" | .sessionEnd => "session_end"
  | .turnStart .. => "turn_start" | .turnEnd => "turn_end" | .stepStart => "step_start"
  | .propose .. => "propose" | .approve .. => "approve" | .reject .. => "reject"
  | .approvalExpire .. => "approval_expire" | .grantCreate .. => "grant_create"
  | .grantRevoke .. => "grant_revoke" | .approverAttest .. => "approver_attest"
  | .permissionAdd .. => "permission_add" | .permissionRevoke .. => "permission_revoke"
  | .dispatch .. => "dispatch" | .result .. => "result" | .outcomeUnknown .. => "outcome_unknown"
  | .reconcile .. => "reconcile" | .cancel .. => "cancel" | .escalationAck .. => "escalation_ack"
  | .ledgerSync .. => "ledger_sync" | .reset => "reset" | .kill => "kill"

def eventTypes : List (String × List String) := [
  ("session_start", ["session_id", "policy_digest", "requester", "permissions", "approvers", "ledger"]),
  ("session_end", []), ("turn_start", ["user_initiated"]), ("turn_end", []), ("step_start", []),
  ("propose", ["call_id", "tool", "call_digest", "cost", "guards", "escalators"]),
  ("approve", ["call_id", "request_id", "approver", "reviewed_digest", "reviewed_cost", "edit"]),
  ("reject", ["call_id", "request_id", "approver"]),
  ("approval_expire", ["call_id", "request_id"]),
  ("grant_create", ["grant_id", "approver", "tool", "call_digest", "scope", "max_uses", "max_cost",
    "not_before", "expires_at", "reviewed_scope_digest"]),
  ("grant_revoke", ["grant_id"]),
  ("approver_attest", ["approver", "principal", "kind", "roles"]),
  ("permission_add", ["permission", "approver"]), ("permission_revoke", ["permission"]),
  ("dispatch", ["call_id", "attempt", "call_digest", "cost", "guards", "idempotency_key"]),
  ("result", ["call_id", "outcome", "actual_cost", "no_effect"]),
  ("outcome_unknown", ["call_id"]),
  ("reconcile", ["call_id", "outcome", "actual_cost", "no_effect"]),
  ("cancel", ["call_id"]), ("escalation_ack", ["approver", "escalation"]),
  ("ledger_sync", ["ledger"]), ("reset", []), ("kill", [])]

def EventBody.fields : EventBody → List (Option (String × Json))
  | .sessionStart sid pd req perms apps led => [
      some ("session_id", .str sid), some ("policy_digest", .str pd), some ("requester", .str req),
      some ("permissions", Encode.strings perms), some ("approvers", encodeMap toJson apps),
      some ("ledger", toJson led)]
  | .sessionEnd | .turnEnd | .stepStart | .reset | .kill => []
  | .turnStart u => [some ("user_initiated", .bool u)]
  | .propose c t d cost gs es => [
      some ("call_id", .str c), some ("tool", .str t), some ("call_digest", .str d),
      some' "cost" cost toJson, some ("guards", boolMap gs), some ("escalators", boolMap es)]
  | .approve c r a rd rc ed => [
      some ("call_id", .str c), some ("request_id", toJson r), some ("approver", .str a),
      some ("reviewed_digest", .str rd), some' "reviewed_cost" rc toJson, some' "edit" ed toJson]
  | .reject c r a => [some ("call_id", .str c), some ("request_id", toJson r), some ("approver", .str a)]
  | .approvalExpire c r => [some ("call_id", .str c), some ("request_id", toJson r)]
  | .grantCreate g a t d sc mu mc nb ex rsd => [
      some ("grant_id", .str g), some ("approver", .str a), some ("tool", .str t),
      some' "call_digest" d Json.str, some ("scope", toJson sc), some ("max_uses", Encode.nat mu),
      some' "max_cost" mc toJson, some' "not_before" nb Encode.nat, some' "expires_at" ex Encode.nat,
      some ("reviewed_scope_digest", .str rsd)]
  | .grantRevoke g => [some ("grant_id", .str g)]
  | .approverAttest a i => [
      some ("approver", .str a), some ("principal", .str i.principal), some ("kind", toJson i.kind),
      some ("roles", Encode.strings i.roles)]
  | .permissionAdd p a => [some ("permission", .str p), some ("approver", .str a)]
  | .permissionRevoke p => [some ("permission", .str p)]
  | .dispatch c n d cost gs k => [
      some ("call_id", .str c), some ("attempt", Encode.nat n), some ("call_digest", .str d),
      some' "cost" cost toJson, some ("guards", boolMap gs), some ("idempotency_key", .str k)]
  | .result c o ac ne | .reconcile c o ac ne => [
      some ("call_id", .str c), some ("outcome", toJson o), some' "actual_cost" ac encodeAmount,
      when ne "no_effect" (.bool true)]
  | .outcomeUnknown c | .cancel c => [some ("call_id", .str c)]
  | .escalationAck a n => [some ("approver", .str a), some ("escalation", Encode.nat n)]
  | .ledgerSync l => [some ("ledger", toJson l)]

instance : ToJson Event where
  toJson e := obj ([
    some ("type", .str e.body.typeName), some ("seq", Encode.nat e.seq), some ("time", Encode.nat e.time),
    some ("state_version", Encode.nat e.stateVersion), some' "origin" e.origin Json.str]
    ++ e.body.fields)

open EventField in
def decodeBody (ty : String) (fs : Array (String × Json)) (defaultDigest : Option String) :
    Decoder EventBody := do
  let callId := req fs "call_id" str
  let rid := req fs "request_id" requestId
  let approver := req fs "approver" str
  let cost := opt fs "cost" money
  let gs := req fs "guards" (keyed bool)
  match ty with
  | "session_start" =>
    let digest ← match defaultDigest with
      | some d => dflt fs "policy_digest" d str
      | none => req fs "policy_digest" str
    pure (.sessionStart (← req fs "session_id" str) digest (← req fs "requester" str)
      (← req fs "permissions" strs) (← req fs "approvers" (keyed approverInfo))
      (← req fs "ledger" FromJson.fromJson))
  | "session_end" => pure .sessionEnd
  | "turn_start" => pure (.turnStart (← req fs "user_initiated" bool))
  | "turn_end" => pure .turnEnd
  | "step_start" => pure .stepStart
  | "propose" =>
    pure (.propose (← callId) (← req fs "tool" str) (← req fs "call_digest" str) (← cost)
      (← gs) (← req fs "escalators" (keyed bool)))
  | "approve" =>
    pure (.approve (← callId) (← rid) (← approver) (← req fs "reviewed_digest" str)
      (← opt fs "reviewed_cost" money) (← opt fs "edit" edit))
  | "reject" => pure (.reject (← callId) (← rid) (← approver))
  | "approval_expire" => pure (.approvalExpire (← callId) (← rid))
  | "grant_create" =>
    pure (.grantCreate (← req fs "grant_id" str) (← approver) (← req fs "tool" str)
      (← opt fs "call_digest" str) (← req fs "scope" FromJson.fromJson) (← req fs "max_uses" nat)
      (← opt fs "max_cost" money) (← opt fs "not_before" nat) (← opt fs "expires_at" nat)
      (← req fs "reviewed_scope_digest" str))
  | "grant_revoke" => pure (.grantRevoke (← req fs "grant_id" str))
  | "approver_attest" =>
    pure (.approverAttest (← approver) ⟨← req fs "principal" str, ← req fs "kind" FromJson.fromJson,
      ← req fs "roles" strs⟩)
  | "permission_add" => pure (.permissionAdd (← req fs "permission" str) (← approver))
  | "permission_revoke" => pure (.permissionRevoke (← req fs "permission" str))
  | "dispatch" =>
    pure (.dispatch (← callId) (← req fs "attempt" nat) (← req fs "call_digest" str) (← cost)
      (← gs) (← req fs "idempotency_key" str))
  | "result" =>
    pure (.result (← callId) (← req fs "outcome" FromJson.fromJson) (← opt fs "actual_cost" decodeAmount)
      (← dflt fs "no_effect" false bool))
  | "outcome_unknown" => pure (.outcomeUnknown (← callId))
  | "reconcile" =>
    pure (.reconcile (← callId) (← req fs "outcome" FromJson.fromJson)
      (← opt fs "actual_cost" decodeAmount) (← dflt fs "no_effect" false bool))
  | "cancel" => pure (.cancel (← callId))
  | "escalation_ack" => pure (.escalationAck (← approver) (← req fs "escalation" nat))
  | "ledger_sync" => pure (.ledgerSync (← req fs "ledger" FromJson.fromJson))
  | "reset" => pure .reset
  | _ => pure .kill

def Event.decoder (defaultDigest : Option String) (j : Json) : Decoder Event := do
  let ty ← match j with
    | .obj kvs =>
      match kvs.find? (·.1 == "type") with
      | some (_, v) => at' "type" (decodeEnum (eventTypes.map (·.1)) id v)
      | none => at' "type" (fail "missing field")
    | _ => fail "expected an object"
  let own := (eventTypes.lookup ty).getD []
  let fs ← object (["type", "seq", "time", "state_version", "origin", "audit"] ++ own) j
  let _ ← opt fs "audit" objectOrFail
  pure ⟨← req fs "seq" nat, ← req fs "time" nat, ← req fs "state_version" nat,
    ← opt fs "origin" string, ← decodeBody ty fs defaultDigest⟩

def Event.decodeWith (defaultDigest : Option String) (j : Json) : Except DecodeError Event :=
  (Event.decoder defaultDigest j).run []

instance : FromJson Event := ⟨Event.decoder none⟩

end Writ
