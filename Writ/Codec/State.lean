import Writ.Codec.Verdict
import Writ.Core.State
import Writ.Core.Version

namespace Writ

open Decoder Encode

def stateSchema : String := "writ.state/1"

def nullable (dec : Json → Decoder α) : Json → Decoder (Option α)
  | .null => pure none
  | j => some <$> dec j

def optJson (o : Option α) (f : α → Json) : Json := (o.map f).getD .null

def natMap (xs : List (String × Nat)) : Json := encodeMap Encode.nat xs

def pairs (k1 k2 : String) (xs : List (String × String)) : Json :=
  .arr (xs.map fun (a, b) => Json.obj #[(k1, .str a), (k2, .str b)]).toArray

def decodePairs (k1 k2 : String) : Json → Decoder (List (String × String)) :=
  array fun j => do
    let fs ← object [k1, k2] j
    pure (← req fs k1 string, ← req fs k2 string)

def costOpt (c : Option Cost) : Json := optJson c toJson

instance : ToJson CallRec where
  toJson r := .obj #[
    ("tool", .str r.tool), ("epoch", Encode.nat r.epoch),
    ("proposed_digest", .str r.proposedDigest), ("proposed_cost", costOpt r.proposedCost),
    ("proposed_guards", boolMap r.proposedGuards),
    ("proposed_escalators", boolMap r.proposedEscalators),
    ("decision", toJson r.decision), ("shadow", optJson r.shadow toJson),
    ("consent", toJson r.consent), ("digest", .str r.digest), ("cost", costOpt r.cost),
    ("status", toJson r.status), ("generation", Encode.nat r.generation),
    ("generations", .arr (r.generations.map fun (d, c) =>
      Json.obj #[("digest", .str d), ("cost", costOpt c)]).toArray),
    ("tally", pairs "principal" "approver" r.tally),
    ("requested_at", Encode.nat r.requestedAt),
    ("authorized_at", optJson r.authorizedAt Encode.nat), ("grant", optJson r.grant Json.str),
    ("attempts", Encode.nat r.attempts), ("idempotency_key", optJson r.idempotencyKey Json.str),
    ("reconciled", optJson r.reconciled toJson)]

def callRecKeys : List String := [
  "tool", "epoch", "proposed_digest", "proposed_cost", "proposed_guards", "proposed_escalators",
  "decision", "shadow", "consent", "digest", "cost", "status", "generation", "generations",
  "tally", "requested_at", "authorized_at", "grant", "attempts", "idempotency_key", "reconciled"]

instance : FromJson CallRec where
  fromJson j := do
    let fs ← object callRecKeys j
    let cost := nullable (FromJson.fromJson (α := Cost))
    pure {
      tool := ← req fs "tool" string, epoch := ← req fs "epoch" nat
      proposedDigest := ← req fs "proposed_digest" string
      proposedCost := ← req fs "proposed_cost" cost
      proposedGuards := ← req fs "proposed_guards" (map bool)
      proposedEscalators := ← req fs "proposed_escalators" (map bool)
      decision := ← req fs "decision" FromJson.fromJson
      shadow := ← req fs "shadow" (nullable FromJson.fromJson)
      consent := ← req fs "consent" FromJson.fromJson
      digest := ← req fs "digest" string, cost := ← req fs "cost" cost
      status := ← req fs "status" FromJson.fromJson, generation := ← req fs "generation" nat
      generations := ← req fs "generations" (array fun g => do
        let gs ← object ["digest", "cost"] g
        pure (← req gs "digest" string, ← req gs "cost" cost))
      tally := ← req fs "tally" (decodePairs "principal" "approver")
      requestedAt := ← req fs "requested_at" nat
      authorizedAt := ← req fs "authorized_at" (nullable nat)
      grant := ← req fs "grant" (nullable string)
      attempts := ← req fs "attempts" nat
      idempotencyKey := ← req fs "idempotency_key" (nullable string)
      reconciled := ← req fs "reconciled" (nullable FromJson.fromJson) }

instance : ToJson GrantRec where
  toJson g := .obj #[
    ("approver", .str g.approver), ("principal", .str g.principal), ("tool", .str g.tool),
    ("call_digest", optJson g.digest Json.str), ("scope", toJson g.scope),
    ("max_uses", Encode.nat g.maxUses), ("consumed", Encode.nat g.consumed),
    ("reserved", Encode.nat g.reserved), ("max_cost", costOpt g.maxCost),
    ("cost_consumed", encodeAmount g.costConsumed), ("cost_reserved", encodeAmount g.costReserved),
    ("not_before", optJson g.notBefore Encode.nat), ("expires_at", optJson g.expiresAt Encode.nat),
    ("revoked", .bool g.revoked), ("epoch", Encode.nat g.epoch), ("turn", Encode.nat g.turn),
    ("reviewed_scope_digest", .str g.reviewedScopeDigest)]

instance : FromJson GrantRec where
  fromJson j := do
    let fs ← object ["approver", "principal", "tool", "call_digest", "scope", "max_uses", "consumed",
      "reserved", "max_cost", "cost_consumed", "cost_reserved", "not_before", "expires_at", "revoked",
      "epoch", "turn", "reviewed_scope_digest"] j
    pure {
      approver := ← req fs "approver" string, principal := ← req fs "principal" string
      tool := ← req fs "tool" string, digest := ← req fs "call_digest" (nullable string)
      scope := ← req fs "scope" FromJson.fromJson, maxUses := ← req fs "max_uses" nat
      consumed := ← req fs "consumed" nat, reserved := ← req fs "reserved" nat
      maxCost := ← req fs "max_cost" (nullable FromJson.fromJson)
      costConsumed := ← req fs "cost_consumed" decodeAmount
      costReserved := ← req fs "cost_reserved" decodeAmount
      notBefore := ← req fs "not_before" (nullable nat)
      expiresAt := ← req fs "expires_at" (nullable nat)
      revoked := ← req fs "revoked" bool, epoch := ← req fs "epoch" nat
      turn := ← req fs "turn" nat
      reviewedScopeDigest := ← req fs "reviewed_scope_digest" string }

def treeJson (enc : α → Json) (m : Std.ExtTreeMap String α compare) : Json :=
  .obj (m.toList.map fun (k, v) => (k, enc v)).toArray

def treeOf (xs : List (String × α)) : Std.ExtTreeMap String α compare := Std.ExtTreeMap.ofList xs

def treeDec (dec : Json → Decoder α) (j : Json) : Decoder (Std.ExtTreeMap String α compare) :=
  treeOf <$> map dec j

instance : ToJson State where
  toJson s := .obj #[
    ("schema", .str stateSchema), ("kernel_version", .str kernelVersion),
    ("policy_digest", .str s.expectedPolicyDigest), ("session_id", .str s.sessionId),
    ("state_version", Encode.nat s.version), ("last_seq", Encode.nat s.lastSeq),
    ("last_time", Encode.nat s.lastTime), ("epoch", Encode.nat s.epoch),
    ("started", .bool s.started), ("ended", .bool s.ended), ("requester", .str s.requester),
    ("permissions", Encode.strings s.permissions), ("approvers", treeJson toJson s.approvers),
    ("turn_active", .bool s.turnActive), ("turn_index", Encode.nat s.turnIndex),
    ("steps_this_turn", Encode.nat s.stepsThisTurn),
    ("proposals_this_turn", Encode.nat s.proposalsThisTurn),
    ("approvals_this_turn", Encode.nat s.approvalsThisTurn),
    ("proposals_this_session", Encode.nat s.proposalsThisSession),
    ("approvals_this_session", Encode.nat s.approvalsThisSession),
    ("calls", treeJson toJson s.calls), ("grants", treeJson toJson s.grants),
    ("session_meters", .arr (s.sessionMeters.map toJson).toArray),
    ("ledger", toJson s.ledger), ("killed", .bool s.killed), ("escalated", .bool s.escalated),
    ("failures", treeJson Encode.nat s.failures),
    ("failures_this_session", Encode.nat s.failuresThisSession),
    ("blocked_tools", Encode.strings s.blockedTools), ("escalations", Encode.nat s.escalations),
    ("rejected_memory", pairs "tool" "digest" s.rejectedMemory)]

def stateKeys : List String := [
  "schema", "kernel_version", "policy_digest", "session_id", "state_version", "last_seq",
  "last_time", "epoch", "started", "ended", "requester", "permissions", "approvers", "turn_active",
  "turn_index", "steps_this_turn", "proposals_this_turn", "approvals_this_turn",
  "proposals_this_session", "approvals_this_session", "calls", "grants", "session_meters", "ledger",
  "killed", "escalated", "failures", "failures_this_session", "blocked_tools", "escalations",
  "rejected_memory"]

instance : FromJson State where
  fromJson j := do
    let fs ← object stateKeys j
    let schema ← req fs "schema" string
    unless schema == stateSchema do
      at' "schema" (fail s!"state document is {schema}, this reader handles {stateSchema}")
    let kv ← req fs "kernel_version" string
    unless kv == kernelVersion do
      at' "kernel_version" (fail s!"state was written by kernel {kv}, this is {kernelVersion}")
    pure {
      expectedPolicyDigest := ← req fs "policy_digest" string
      sessionId := ← req fs "session_id" string, version := ← req fs "state_version" nat
      lastSeq := ← req fs "last_seq" nat, lastTime := ← req fs "last_time" nat
      epoch := ← req fs "epoch" nat, started := ← req fs "started" bool
      ended := ← req fs "ended" bool, requester := ← req fs "requester" string
      permissions := ← req fs "permissions" strings
      approvers := ← req fs "approvers" (treeDec FromJson.fromJson)
      turnActive := ← req fs "turn_active" bool, turnIndex := ← req fs "turn_index" nat
      stepsThisTurn := ← req fs "steps_this_turn" nat
      proposalsThisTurn := ← req fs "proposals_this_turn" nat
      approvalsThisTurn := ← req fs "approvals_this_turn" nat
      proposalsThisSession := ← req fs "proposals_this_session" nat
      approvalsThisSession := ← req fs "approvals_this_session" nat
      calls := ← req fs "calls" (treeDec FromJson.fromJson)
      grants := ← req fs "grants" (treeDec FromJson.fromJson)
      sessionMeters := ← req fs "session_meters" (array FromJson.fromJson)
      ledger := ← req fs "ledger" FromJson.fromJson
      killed := ← req fs "killed" bool, escalated := ← req fs "escalated" bool
      failures := ← req fs "failures" (treeDec nat)
      failuresThisSession := ← req fs "failures_this_session" nat
      blockedTools := ← req fs "blocked_tools" strings
      escalations := ← req fs "escalations" nat
      rejectedMemory := ← req fs "rejected_memory" (decodePairs "tool" "digest") }

end Writ
