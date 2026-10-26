import assert from "node:assert/strict"
import { test } from "node:test"
import { loadKernel, WritInputError } from "../src/index.js"
import { simpleGate, simplePolicy } from "../src/simple.js"
import type { SimpleConsent } from "../src/simple.js"

test("simplePolicy passes check", async () => {
  const k = await loadKernel()
  const r = k.check(simplePolicy({ web_search: "none", send_email: "per_call" }))
  assert.equal(r.ok, true)
  assert.deepEqual(r.warnings, [])
})

test("simplePolicy emits a layer-1 policy with the user as the only approver role", () => {
  assert.deepEqual(JSON.parse(simplePolicy({ web_search: "none", send_email: "per_call" }, { approvalTtlMs: 5000 })), {
    writ: "0.1",
    approver_roles: ["user"],
    limits: { approval_ttl_ms: 5000 },
    actions: { web_search: { consent: "none" }, send_email: { consent: "per_call" } },
  })
  assert.equal(JSON.parse(simplePolicy({ t: "none" })).limits.approval_ttl_ms, 600_000)
})

test("simplePolicy refuses a bad consent and an empty map", () => {
  assert.throws(() => simplePolicy({ a: "always" as SimpleConsent }), (e) => e instanceof WritInputError && e.path === "tools.a")
  assert.throws(() => simplePolicy({}), (e) => e instanceof WritInputError && e.path === "tools")
  assert.throws(() => simplePolicy({ t: "none" }, { approvalTtlMs: 1.5 }), (e) => e instanceof WritInputError && e.path === "approvalTtlMs")
})

test("a free tool runs, an approved tool runs once, an unknown tool is denied", async () => {
  const w = await simpleGate({ user: "user:alice", tools: { web_search: "none", send_email: "per_call" } })
  const s = await w.session()
  const a = await s.propose("web_search", { q: "tea" })
  assert.equal(a.status, "allowed")
  assert.deepEqual(await s.run(a, async () => 1), { ran: true, value: 1 })
  let b = await s.propose("send_email", { to: "bob" })
  assert.equal(b.status, "needs_approval")
  assert.ok(b.requestId)
  b = await s.approve(b)
  assert.equal(b.status, "allowed")
  let calls = 0
  assert.deepEqual(await s.run(b, async () => ++calls), { ran: true, value: 1 })
  assert.deepEqual(await s.run(b, async () => ++calls), { ran: false, reason: "call_ended" })
  assert.equal(calls, 1)
  const c = await s.propose("delete_all", {})
  assert.equal(c.status, "denied")
  assert.equal(c.reason, "unknown_tool")
})

test("a throwing tool is reported unknown and not run again", async () => {
  const w = await simpleGate({ user: "u", tools: { t: "none" } })
  const s = await w.session()
  const a = await s.propose("t", {})
  await assert.rejects(s.run(a, async () => { throw new Error("boom") }), /boom/)
  const view = await w.gate.inspect(s.id)
  assert.equal(view?.calls.find((c) => c.call_id === a.callId)?.status, "unknown")
  let ran = false
  assert.deepEqual(await s.run(a, async () => { ran = true }), { ran: false, reason: "retry_not_allowed" })
  assert.equal(ran, false)
})

test("a rejected call never runs", async () => {
  const w = await simpleGate({ user: "user:alice", tools: { send_email: "per_call" } })
  const s = await w.session()
  let b = await s.propose("send_email", { to: "bob" })
  assert.equal(b.status, "needs_approval")
  b = await s.reject(b)
  assert.equal(b.status, "denied")
  let ran = false
  assert.deepEqual(await s.run(b, async () => { ran = true }), { ran: false, reason: "call_ended" })
  assert.equal(ran, false)
})

test("a call awaiting approval does not run", async () => {
  const w = await simpleGate({ user: "user:alice", tools: { send_email: "per_call" } })
  const s = await w.session()
  const b = await s.propose("send_email", { to: "bob" })
  let ran = false
  assert.deepEqual(await s.run(b, async () => { ran = true }), { ran: false, reason: "call_awaiting" })
  assert.equal(ran, false)
})

test("sessions are separate, take a given id, and use the gate's clock and store", async () => {
  let now = 1000
  const w = await simpleGate({ user: "u", tools: { t: "per_call" }, approvalTtlMs: 10, clock: () => now })
  const s1 = await w.session("s-1")
  assert.equal(s1.id, "s-1")
  const s2 = await w.session()
  assert.notEqual(s2.id, s1.id)
  const a = await s1.propose("t", { n: 1 })
  assert.equal(a.status, "needs_approval")
  now += 11
  const late = await s1.approve(a)
  assert.equal(late.status, "denied")
  assert.equal(late.reason, "approval_expired")
  assert.equal((await w.gate.inspect(s2.id))?.calls.length, 0)
  await assert.rejects(w.session("s-1"), (e) => e instanceof WritInputError && /already_started/.test(e.message))
})

test("a second approve reports the call allowed with the refusal reason, and the call runs once", async () => {
  const w = await simpleGate({ user: "user:alice", tools: { send_email: "per_call" } })
  const s = await w.session()
  const b = await s.propose("send_email", { to: "bob" })
  const first = await s.approve(b)
  assert.equal(first.status, "allowed")
  const second = await s.approve(b)
  assert.equal(second.status, "allowed")
  assert.equal(second.reason, "call_authorized")
  let calls = 0
  assert.deepEqual(await s.run(second, async () => ++calls), { ran: true, value: 1 })
  assert.equal((await s.run(second, async () => ++calls)).ran, false)
  assert.equal(calls, 1)
})

test("an approve with a wrong digest leaves the call awaiting with its request id", async () => {
  const w = await simpleGate({ user: "user:alice", tools: { send_email: "per_call" } })
  const s = await w.session()
  const b = await s.propose("send_email", { to: "bob" })
  const tampered = await s.approve({ ...b, callDigest: "sha256:" + "0".repeat(64) })
  assert.equal(tampered.status, "needs_approval")
  assert.equal(tampered.reason, "digest_mismatch")
  assert.equal(tampered.requestId, b.requestId)
  assert.equal(tampered.callDigest, b.callDigest)
  assert.equal((await s.approve(tampered)).status, "allowed")
})

test("a reject after approval vetoes the call, and a refused reject keeps the reason", async () => {
  const w = await simpleGate({ user: "user:alice", tools: { send_email: "per_call" } })
  const s = await w.session()
  const b = await s.propose("send_email", { to: "bob" })
  assert.equal((await s.approve(b)).status, "allowed")
  const vetoed = await s.reject(b)
  assert.equal(vetoed.status, "denied")
  let ran = false
  assert.deepEqual(await s.run(b, async () => { ran = true }), { ran: false, reason: "call_ended" })
  assert.equal(ran, false)
  const again = await s.reject(b)
  assert.equal(again.status, "denied")
  assert.equal(again.reason, "call_ended")
})

test("an approve after the TTL ends the request", async () => {
  let now = 1000
  const w = await simpleGate({ user: "u", tools: { t: "per_call" }, approvalTtlMs: 10, clock: () => now })
  const s = await w.session()
  const a = await s.propose("t", {})
  now += 11
  const late = await s.approve(a)
  assert.equal(late.status, "denied")
  assert.equal(late.reason, "approval_expired")
  assert.equal(late.requestId, undefined)
  assert.equal((await w.gate.inspect(s.id))?.calls.find((c) => c.call_id === a.callId)?.status, "expired")
})

test("a failing outcomeUnknown does not hide the tool's error", async () => {
  const w = await simpleGate({ user: "u", tools: { t: "none" } })
  const s = await w.session()
  const a = await s.propose("t", {})
  w.gate.outcomeUnknown = async () => { throw new Error("store down") }
  await assert.rejects(s.run(a, async () => { throw new Error("boom") }), /boom/)
})

test("simplePolicy keeps a tool named __proto__", async () => {
  const text = simplePolicy({ ["__proto__"]: "none" })
  assert.ok(Object.keys(JSON.parse(text).actions).includes("__proto__"))
  assert.equal((await loadKernel()).check(text).ok, true)
})
