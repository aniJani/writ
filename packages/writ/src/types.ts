import type { Reason, Retry } from "./reasons.js"

export type { Reason, Retry }

export interface Cost { amount: string; currency: string }
export interface RequestId { session: string; call: string; generation: number }
export interface Approver { principal: string; kind: "human" | "automated"; roles: string[] }
export type Outcome = "succeeded" | "failed" | "declined"

export interface MeterEntry {
  meter: string
  session: string
  call: string
  time: number
  amount: string
  committed: boolean
  excess?: string
  excess_at?: number
}
export interface Ledger { version?: number; entries?: MeterEntry[]; tombstone?: boolean }

interface Base {
  seq: number
  time: number
  state_version: number
  origin?: string
  audit?: Record<string, unknown>
}
export interface Edit { new_digest: string; new_cost?: Cost; escalators: Record<string, boolean> }

export type WritEvent = Base & (
  | {
    type: "session_start"
    session_id: string
    policy_digest: string
    requester: string
    permissions: string[]
    approvers: Record<string, Approver>
    ledger: Ledger
  }
  | { type: "session_end" | "turn_end" | "step_start" | "reset" | "kill" }
  | { type: "turn_start"; user_initiated: boolean }
  | {
    type: "propose"
    call_id: string
    tool: string
    call_digest: string
    cost?: Cost
    guards: Record<string, boolean>
    escalators: Record<string, boolean>
  }
  | {
    type: "approve"
    call_id: string
    request_id: RequestId
    approver: string
    reviewed_digest: string
    reviewed_cost?: Cost
    edit?: Edit
  }
  | { type: "reject"; call_id: string; request_id: RequestId; approver: string }
  | { type: "approval_expire"; call_id: string; request_id: RequestId }
  | {
    type: "grant_create"
    grant_id: string
    approver: string
    tool: string
    call_digest?: string
    scope: "turn" | "session"
    max_uses: number
    max_cost?: Cost
    not_before?: number
    expires_at?: number
    reviewed_scope_digest: string
  }
  | { type: "grant_revoke"; grant_id: string }
  | { type: "approver_attest"; approver: string; principal: string; kind: "human" | "automated"; roles: string[] }
  | { type: "permission_add"; permission: string; approver: string }
  | { type: "permission_revoke"; permission: string }
  | {
    type: "dispatch"
    call_id: string
    attempt: number
    call_digest: string
    cost?: Cost
    guards: Record<string, boolean>
    idempotency_key: string
  }
  | { type: "result" | "reconcile"; call_id: string; outcome: Outcome; actual_cost?: string; no_effect?: boolean }
  | { type: "outcome_unknown" | "cancel"; call_id: string }
  | { type: "escalation_ack"; approver: string; escalation: number }
  | { type: "ledger_sync"; ledger: Ledger }
)

export type CallStatus =
  | "awaiting" | "authorized" | "dispatched" | "succeeded" | "failed" | "declined" | "unknown"
  | "rejected" | "expired" | "cancelled"
  | { status: "denied" | "denied_at_dispatch"; reason: Reason }

export type Decision =
  | { decision: "pending" | "authorized" | "allowed" | "dispatch_claimed" }
  | { decision: "allowed_by_grant"; grant: string }
  | { decision: "needs_approval"; request_id: RequestId }
  | { decision: "denied" | "dispatch_denied"; reason: Reason }
  | { decision: "existing"; status: CallStatus }
  | { decision: "overrun"; meters: string[] }

export interface Explanation { retry?: Retry; message?: string }
export type Shadow =
  | { would_deny?: undefined; would_need_approval?: undefined }
  | { would_deny: Reason; would_need_approval?: undefined }
  | { would_deny?: undefined; would_need_approval: true }

export type Verdict =
  | ({ verdict: "accepted"; state_version: number } & ({ decision?: undefined; reason?: undefined; request_id?: undefined; grant?: undefined; status?: undefined; meters?: undefined } | Decision) & Shadow & Explanation)
  | { verdict: "rejected"; state_version: number; reason: Reason; retry: Retry; message: string }

export interface Finding { code: string; action?: string; message: string }
export type CheckResult =
  | { ok: boolean; errors: Finding[]; warnings: Finding[]; policy_digest: string }

export interface StepReplay { step: number; message: string }
export interface TraceReplay { id: string; ok: boolean; mismatches: StepReplay[] }
export interface ReplayResult { traces: TraceReplay[] }

export interface CallView {
  call_id: string
  tool: string
  status: CallStatus
  digest: string
  cost: Cost | null
  attempts: number
  generation: number
  epoch: number
  /** Present only while the call is awaiting approval. */
  request_id?: RequestId
}

/**
 * Amounts are decimal strings in the meter's unit; `cap` and `remaining` are null without a cap.
 * `remaining` is never below "0", and `used` may exceed `cap` after an overrun.
 */
export interface MeterView {
  meter: string
  scope: "session" | "principal"
  used: string
  cap: string | null
  remaining: string | null
}

export interface SessionView {
  session_id: string
  state_version: number
  ledger_version: number
  started: boolean
  ended: boolean
  killed: boolean
  tombstone: boolean
  escalated: boolean
  escalations: number
  blocked_tools: string[]
  calls: CallView[]
  meters: MeterView[]
}

/** SEP-2848's `io.modelcontextprotocol/tool-approval-disposition`, plus SEP-2663's `cancelled`. */
export type Disposition = "approved-executed" | "denied-not-executed" | "execution-error" | "outcome-unknown" | "cancelled"

/** The SEP-2643 envelope (`io.modelcontextprotocol/authorization`) the mcp-tool-approval profile gives a verdict. */
export type ProfileEnvelope =
  | {
    reason: "insufficient_authorization"; remediation: "available"; remediationHints: { type: "task" }[]
    requestId: RequestId
  }
  | { reason: "insufficient_authorization"; remediation: "unavailable"; code: Reason; retry: Retry; message: string }

export interface ProfileResult { disposition?: Disposition; envelope?: ProfileEnvelope }
