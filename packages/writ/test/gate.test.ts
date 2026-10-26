import assert from "node:assert/strict"
import { test } from "node:test"
import { canonicalize, clampUntrusted, createGate, defaultIdempotencyKey, MemoryStore } from "../src/index.js"
import type { Commit, Kernel, LedgerCommit, Store, StepResult, WritEvent, Verdict } from "../src/index.js"
import { proposeKind } from "../src/gate.js"
import { gateSuite, kernel } from "./gate-suite.js"

gateSuite("MemoryStore", () => new MemoryStore())

test("clampUntrusted rewrites only result and reconcile", () => {
  const base = { seq: 1, time: 0, state_version: 0, call_id: "c" }
  assert.deepEqual(
    clampUntrusted({ ...base, type: "result", outcome: "declined", actual_cost: "5", no_effect: true }, { trustedDecline: false, reservation: "10" }),
    { ...base, type: "result", outcome: "failed", actual_cost: "10", no_effect: false },
  )
  assert.deepEqual(
    clampUntrusted({ ...base, type: "reconcile", outcome: "declined", actual_cost: "15" }, { trustedDecline: true, reservation: "10" }),
    { ...base, type: "reconcile", outcome: "declined", actual_cost: "15", no_effect: false },
  )
  assert.deepEqual(
    clampUntrusted({ ...base, type: "result", outcome: "succeeded", actual_cost: "0" }, { trustedDecline: false }),
    { ...base, type: "result", outcome: "succeeded", actual_cost: "0", no_effect: false },
  )
  const other: WritEvent = { ...base, type: "outcome_unknown" }
  assert.equal(clampUntrusted(other, { trustedDecline: false }), other)
})

test("proposeKind table", () => {
  const acc = (d: object): Verdict => ({ verdict: "accepted", state_version: 1, ...d }) as Verdict
  const rid = { session: "s", call: "c", generation: 0 }
  const cases: [Verdict, string][] = [
    [acc({ decision: "allowed" }), "allowed"],
    [acc({ decision: "allowed_by_grant", grant: "g" }), "allowed"],
    [acc({ decision: "authorized" }), "allowed"],
    [acc({ decision: "existing", status: "authorized" }), "allowed"],
    [acc({ decision: "existing", status: "dispatched" }), "denied"],
    [acc({ decision: "needs_approval", request_id: rid }), "needs_approval"],
    [acc({ decision: "denied", reason: "unknown_tool" }), "denied"],
    [acc({ decision: "existing", status: { status: "denied", reason: "guard_false" } }), "denied"],
    [acc({ decision: "existing", status: { status: "denied_at_dispatch", reason: "permission_missing" } }), "denied"],
    [acc({ decision: "existing", status: "succeeded" }), "denied"],
    [acc({ decision: "existing", status: "unknown" }), "denied"],
    [acc({ decision: "existing", status: "cancelled" }), "denied"],
    [acc({}), "denied"],
    [{ verdict: "rejected", state_version: 1, reason: "turn_state", retry: "fix_request", message: "m" }, "rejected"],
  ]
  for (const [v, want] of cases) assert.equal(proposeKind(v), want, JSON.stringify(v))
})

class Counting implements Store {
  commits: Commit[] = []
  constructor(readonly inner: Store) {}
  load(id: string) { return this.inner.load(id) }
  loadLedger(p: string) { return this.inner.loadLedger(p) }
  commitLedger(c: LedgerCommit) { return this.inner.commitLedger(c) }
  commit(c: Commit) {
    this.commits.push(c)
    return this.inner.commit(c)
  }
}

const retryPolicy = JSON.stringify({
  writ: "0.1",
  actions: { ping: { consent: "none", idempotent: true, retry_after_unknown: true, max_attempts: 3 } },
})

test("dispatch without idempotencyKey sends H(principal, session_id, call_id), the same on every attempt", async () => {
  const { createHash } = await import("node:crypto")
  const want = "sha256:" + createHash("sha256").update(canonicalize({ principal: "u1", session: "s1", call: "c1" })).digest("hex")
  assert.equal(await defaultIdempotencyKey("u1", "s1", "c1"), want)
  assert.notEqual(await defaultIdempotencyKey("u1", "s1", "c2"), want)
  assert.notEqual(await defaultIdempotencyKey("u1", "s2", "c1"), want)
  assert.notEqual(await defaultIdempotencyKey("u2", "s1", "c1"), want)

  const store = new Counting(new MemoryStore())
  let t = 0
  const gate = createGate({ kernel, policyText: retryPolicy, store, clock: () => (t += 10) })
  await gate.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: {}, userInitiated: true })
  await gate.stepStart("s1")
  assert.equal((await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
  const keys: unknown[] = []
  for (const attempt of [1, 2]) {
    const d = await gate.dispatch("s1", { callId: "c1", attempt, callDigest: "d" })
    assert.equal(d.verdict.verdict === "accepted" && d.verdict.decision, "dispatch_claimed", JSON.stringify(d.verdict))
    keys.push(JSON.parse((await store.load("s1"))!.state).calls.c1.idempotency_key)
    if (attempt === 1) await gate.outcomeUnknown("s1", "c1")
  }
  assert.deepEqual(keys, [want, want])

  // An explicit key is still sent as given, and must then stay the same across attempts.
  await gate.propose("s1", { callId: "c2", tool: "ping", callDigest: "d" })
  await gate.dispatch("s1", { callId: "c2", attempt: 1, callDigest: "d", idempotencyKey: "k-own" })
  assert.equal(JSON.parse((await store.load("s1"))!.state).calls.c2.idempotency_key, "k-own")
  await gate.outcomeUnknown("s1", "c2")
  const other = await gate.dispatch("s1", { callId: "c2", attempt: 2, callDigest: "d" })
  assert.equal(other.verdict.verdict === "rejected" && other.verdict.reason, "idempotency_key_mismatch")
})

test("the gate commits nothing for a rejected verdict, even when the kernel says changed", async () => {
  const store = new Counting(new MemoryStore())
  let lie = false
  const liar: Kernel = {
    ...kernel,
    step(policyText, stateText, event): StepResult {
      const r = kernel.step(policyText, stateText, event)
      if (!lie) return r
      const verdict: Verdict = { verdict: "rejected", state_version: r.stateVersion, reason: "call_awaiting", retry: "fix_request", message: "stub" }
      return { ...r, verdict, changed: true }
    },
  }
  let t = 0
  const gate = createGate({ kernel: liar, policyText: retryPolicy, store, clock: () => (t += 10) })
  await gate.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: {}, userInitiated: true })
  const before = await store.load("s1")
  const commits = store.commits.length
  lie = true
  const r = await gate.stepStart("s1")
  assert.equal(r.verdict.verdict, "rejected")
  assert.equal(r.stateVersion, before!.stateVersion)
  assert.equal(store.commits.length, commits)
  assert.deepEqual(await store.load("s1"), before)
})
