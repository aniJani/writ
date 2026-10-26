import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"
import { test } from "node:test"
import { repoRoot } from "./helpers.js"
import { loadKernel, mcpToolApproval, REASONS, WritInputError } from "../src/index.js"
import type { CallStatus, ProfileResult, Verdict } from "../src/index.js"

const kernel = await loadKernel()

interface Vector { id: string; input: { profile: string; verdict?: Verdict; status?: CallStatus }; output: ProfileResult }
const vectors = readFileSync(join(repoRoot, "corpus/profiles/mcp-tool-approval-v1.jsonl"), "utf8")
  .split("\n").filter((l) => l !== "").map((l) => JSON.parse(l) as Vector)

test("every profile vector gives its output through kernel.profile", () => {
  assert.ok(vectors.length > 0)
  for (const v of vectors) {
    const { profile, ...input } = v.input
    assert.deepEqual(kernel.profile(profile, input as { verdict: Verdict } | { status: CallStatus }), v.output, v.id)
  }
})

test("the vectors cover every reason code and every call status", () => {
  const rejected = vectors.flatMap((v) => v.input.verdict?.verdict === "rejected" ? [v.input.verdict.reason] : [])
  assert.deepEqual(rejected, [...REASONS])
  const statuses = new Set(vectors.flatMap((v) => {
    const s = v.input.status
    return s === undefined ? [] : [typeof s === "string" ? s : s.status]
  }))
  assert.deepEqual([...statuses].sort(), [
    "authorized", "awaiting", "cancelled", "declined", "denied", "denied_at_dispatch", "dispatched", "expired",
    "failed", "rejected", "succeeded", "unknown",
  ])
})

test("mcpToolApproval reads dispositions and envelopes from the kernel", () => {
  assert.equal(mcpToolApproval.id, "mcp-tool-approval")
  assert.equal(mcpToolApproval.disposition(kernel, "unknown"), "outcome-unknown")
  assert.equal(mcpToolApproval.disposition(kernel, "cancelled"), "cancelled")
  assert.equal(mcpToolApproval.disposition(kernel, { status: "denied_at_dispatch", reason: "grant_invalid" }), "denied-not-executed")
  assert.equal(mcpToolApproval.disposition(kernel, "authorized"), undefined)
  const rid = { session: "s1", call: "c1", generation: 1 }
  assert.deepEqual(mcpToolApproval.envelope(kernel, { verdict: "accepted", state_version: 4, decision: "needs_approval", request_id: rid }), {
    reason: "insufficient_authorization", remediation: "available", remediationHints: [{ type: "task" }], requestId: rid,
  })
  const env = mcpToolApproval.envelope(kernel, {
    verdict: "accepted", state_version: 4, decision: "denied", reason: "killed", retry: "never", message: "ignored",
  })
  assert.ok(env !== undefined && env.remediation === "unavailable")
  assert.deepEqual(Object.keys(env), ["reason", "remediation", "code", "retry", "message"])
  assert.equal(env.code, "killed")
  assert.notEqual(env.message, "ignored")
  assert.equal(mcpToolApproval.envelope(kernel, { verdict: "accepted", state_version: 4, decision: "allowed" }), undefined)
})

const inputError = (path: string) => (e: unknown) => {
  assert.ok(e instanceof WritInputError, String(e))
  assert.equal(e.path, path)
  return true
}

test("profile input errors name id or input, and the kernel lives on", () => {
  assert.throws(() => kernel.profile("writ/mcp-tool-approval", { status: "unknown" }), inputError("id"))
  assert.throws(() => kernel.profile("nope", { status: "unknown" }), { message: 'id: unknown profile "nope", expected mcp-tool-approval' })
  assert.throws(() => kernel.profile("mcp-tool-approval", { status: "denied" as CallStatus }), inputError("input"))
  assert.throws(() => kernel.profile("mcp-tool-approval", {} as { status: CallStatus }), inputError("input"))
  assert.equal(kernel.profile("mcp-tool-approval", { status: "succeeded" }).disposition, "approved-executed")
})
