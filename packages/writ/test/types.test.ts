import assert from "node:assert/strict"
import { test } from "node:test"
import type { ProposeResult, Reason, RequestId, Verdict } from "../src/index.js"

// Compiles only if narrowing on `decision` makes the payload fields required.
function requestOf(v: Verdict): RequestId | undefined {
  if (v.verdict === "accepted" && v.decision === "needs_approval") {
    const id: RequestId = v.request_id
    return id
  }
  if (v.verdict === "rejected") {
    const reason: string = v.reason
    const retry: string = v.retry
    void reason
    void retry
  }
  return undefined
}

// Compiles only if narrowing on `kind` gives the propose result's payload.
function payloadOf(r: ProposeResult): number | Reason | undefined {
  if (r.kind === "needs_approval") {
    const generation: number = r.requestId.generation
    return generation
  }
  if (r.kind === "rejected") {
    const reason: Reason = r.reason
    return reason
  }
  return undefined
}

test("narrowing a propose result on kind gives its payload", () => {
  const base = { stateVersion: 1 }
  const rid = { session: "s", call: "c", generation: 3 }
  assert.equal(payloadOf({ ...base, kind: "needs_approval", requestId: rid, verdict: { verdict: "accepted", state_version: 1, decision: "needs_approval", request_id: rid } }), 3)
  const rejected: Verdict = { verdict: "rejected", state_version: 1, reason: "turn_state", retry: "fix_request", message: "m" }
  assert.equal(payloadOf({ ...base, kind: "rejected", reason: "turn_state", verdict: rejected }), "turn_state")
})

test("narrowing a needs_approval verdict gives a request id", () => {
  const id = { session: "s", call: "c", generation: 0 }
  assert.deepEqual(requestOf({ verdict: "accepted", state_version: 1, decision: "needs_approval", request_id: id }), id)
  assert.equal(requestOf({ verdict: "accepted", state_version: 1 }), undefined)
})

// Each line below must fail to compile; tsc reports an unused directive if the type loosens.
// @ts-expect-error an accepted verdict without a decision carries no reason
export const noReason: Verdict = { verdict: "accepted", state_version: 1, reason: "not_started" }
// @ts-expect-error needs_approval requires request_id
export const noRequest: Verdict = { verdict: "accepted", state_version: 1, decision: "needs_approval" }
// @ts-expect-error would_deny and would_need_approval never appear together
export const bothShadows: Verdict = { verdict: "accepted", state_version: 1, would_deny: "killed", would_need_approval: true }
// @ts-expect-error a rejected propose result always has a reason
export const rejectedNoReason: ProposeResult = { kind: "rejected", stateVersion: 1, verdict: { verdict: "rejected", state_version: 1, reason: "killed", retry: "never", message: "m" } }
// @ts-expect-error a rejected verdict always has retry
export const noRetry: Verdict = { verdict: "rejected", state_version: 1, reason: "killed", message: "m" }
