import Writ.Codec.Event
import Writ.Core.State
import Writ.Core.Messages

namespace Writ

open Decoder Encode

instance : FromJson Reason := ⟨decodeEnum Reason.all Reason.code⟩
instance : ToJson Reason := ⟨fun r => .str r.code⟩

def CallStatus.code : CallStatus → String
  | .denied _ => "denied" | .awaiting => "awaiting" | .authorized => "authorized"
  | .dispatched => "dispatched" | .succeeded => "succeeded" | .failed => "failed"
  | .declined => "declined" | .unknown => "unknown" | .rejected => "rejected"
  | .expired => "expired" | .deniedAtDispatch _ => "denied_at_dispatch" | .cancelled => "cancelled"

def CallStatus.reason? : CallStatus → Option Reason
  | .denied r | .deniedAtDispatch r => some r
  | _ => Option.none

instance : ToJson CallStatus where
  toJson s := match s.reason? with
    | some r => obj [some ("status", .str s.code), some ("reason", toJson r)]
    | none => .str s.code

instance : FromJson CallStatus where
  fromJson
    | .str s =>
      match s with
      | "awaiting" => pure .awaiting | "authorized" => pure .authorized
      | "dispatched" => pure .dispatched | "succeeded" => pure .succeeded
      | "failed" => pure .failed | "declined" => pure .declined | "unknown" => pure .unknown
      | "rejected" => pure .rejected | "expired" => pure .expired | "cancelled" => pure .cancelled
      | "denied" | "denied_at_dispatch" => fail s!"\"{s}\" needs a reason, write it as an object"
      | _ => fail s!"unknown value \"{s}\""
    | j@(.obj _) => do
      let fs ← object ["status", "reason"] j
      let r ← req fs "reason" FromJson.fromJson
      match ← req fs "status" string with
      | "denied" => pure (.denied r)
      | "denied_at_dispatch" => pure (.deniedAtDispatch r)
      | _ => at' "status" (fail "only \"denied\" and \"denied_at_dispatch\" carry a reason")
    | _ => fail "expected a string or an object"

def Decision.code : Decision → Option String
  | .none => Option.none | .pending => some "pending" | .authorized => some "authorized"
  | .allowed => some "allowed" | .allowedByGrant _ => some "allowed_by_grant"
  | .needsApproval _ => some "needs_approval" | .denied _ => some "denied"
  | .dispatchClaimed => some "dispatch_claimed" | .dispatchDenied _ => some "dispatch_denied"
  | .existing _ => some "existing" | .overrun _ => some "overrun"

def Decision.toFields (d : Decision) : Array (String × Json) :=
  let head := (d.code.map fun c => [("decision", Json.str c)]).getD []
  (head ++ match d with
    | .allowedByGrant g => [("grant", .str g)]
    | .needsApproval r => [("request_id", toJson r)]
    | .denied r | .dispatchDenied r => [("reason", toJson r)]
    | .existing s => [("status", toJson s)]
    | .overrun ms => [("meters", Encode.strings ms)]
    | _ => []).toArray

def Decision.reason? : Decision → Option Reason
  | .denied r | .dispatchDenied r => some r
  | .existing s => s.reason?
  | _ => Option.none

def Shadow.toFields : Shadow → Array (String × Json)
  | .wouldDeny r => #[("would_deny", toJson r)]
  | .wouldNeedApproval => #[("would_need_approval", .bool true)]

def decisionKeys : List String := ["grant", "request_id", "status", "reason", "meters"]

def Decision.fromFields (fs : Array (String × Json)) : Decoder Decision := do
  let name ← opt fs "decision" string
  let used : List String := match name with
    | some "allowed_by_grant" => ["grant"] | some "needs_approval" => ["request_id"]
    | some "denied" | some "dispatch_denied" => ["reason"] | some "existing" => ["status"]
    | some "overrun" => ["meters"]
    | _ => []
  for (k, _) in fs do
    if decisionKeys.contains k && !used.contains k then at' k (fail "unknown field")
  match name with
  | Option.none => pure .none
  | some "pending" => pure .pending
  | some "authorized" => pure .authorized
  | some "allowed" => pure .allowed
  | some "allowed_by_grant" => pure (.allowedByGrant (← req fs "grant" string))
  | some "needs_approval" => pure (.needsApproval (← req fs "request_id" FromJson.fromJson))
  | some "denied" => pure (.denied (← req fs "reason" FromJson.fromJson))
  | some "dispatch_claimed" => pure .dispatchClaimed
  | some "dispatch_denied" => pure (.dispatchDenied (← req fs "reason" FromJson.fromJson))
  | some "existing" => pure (.existing (← req fs "status" FromJson.fromJson))
  | some "overrun" =>
    match ← req fs "meters" strings with
    | [] => at' "meters" (fail "expected at least one meter")
    | ms => pure (.overrun ms)
  | some other => at' "decision" (fail s!"unknown value \"{other}\"")

def Shadow.fromFields (fs : Array (String × Json)) : Decoder (Option Shadow) := do
  let deny ← opt fs "would_deny" FromJson.fromJson
  let need ← opt fs "would_need_approval" bool
  match deny, need with
  | some r, none => pure (some (.wouldDeny r))
  | none, some true => pure (some .wouldNeedApproval)
  | none, some false => at' "would_need_approval" (fail "expected true")
  | none, none => pure none
  | some _, some _ => at' "would_need_approval" (fail "conflicts with would_deny")

instance : ToJson Decision := ⟨fun d => .obj d.toFields⟩
instance : FromJson Decision where
  fromJson j := do
    let fs ← object ("decision" :: decisionKeys) j
    Decision.fromFields fs

instance : ToJson Shadow := ⟨fun s => .obj s.toFields⟩
instance : FromJson Shadow where
  fromJson j := do
    let fs ← object ["would_deny", "would_need_approval"] j
    match ← Shadow.fromFields fs with
    | some s => pure s
    | none => fail "expected would_deny or would_need_approval"

def Verdict.fields : Verdict → Array (String × Json)
  | .ok d sh =>
    let advice := match d.reason? with
      | some r => #[("retry", Json.str r.retry.code), ("message", .str r.modelMessage)]
      | none => #[]
    #[("verdict", .str "accepted")] ++ d.toFields ++ (sh.map Shadow.toFields).getD #[] ++ advice
  | .rejected r =>
    #[("verdict", .str "rejected"), ("reason", toJson r), ("retry", .str r.retry.code),
      ("message", .str r.modelMessage)]

instance : ToJson Verdict := ⟨fun v => .obj v.fields⟩

def Verdict.toJsonWith (v : Verdict) (stateVersion : Nat) : Json :=
  let fs := v.fields
  .obj (fs.extract 0 1 ++ #[("state_version", Encode.nat stateVersion)] ++ fs.extract 1 fs.size)

instance : FromJson Verdict where
  fromJson j := do
    let fs ← object (["verdict", "state_version", "decision", "retry", "message",
      "would_deny", "would_need_approval"] ++ decisionKeys) j
    match ← req fs "verdict" string with
    | "accepted" => pure (.ok (← Decision.fromFields fs) (← Shadow.fromFields fs))
    | "rejected" =>
      for (k, _) in fs do
        if k == "decision" || k == "would_deny" || k == "would_need_approval" ||
            (decisionKeys.contains k && k != "reason") then at' k (fail "unknown field")
      pure (.rejected (← req fs "reason" FromJson.fromJson))
    | other => at' "verdict" (fail s!"unknown value \"{other}\", expected one of accepted, rejected")

end Writ
