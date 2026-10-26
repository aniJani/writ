import assert from "node:assert/strict"
import { test } from "node:test"
import { Command } from "@langchain/langgraph"
import { createGate, loadKernel, MemoryStore } from "@anijani/writ"
import { buildGraph } from "../graph.mjs"

const kernel = await loadKernel()
const policyText = JSON.stringify({
  writ: "0.1",
  approver_roles: ["reviewer"],
  limits: { approval_ttl_ms: 600000 },
  actions: {
    "deploy.prod": { consent: { quorum: 1, roles: ["reviewer"], exclude_requester: true } },
    "notes.read": {},
  },
})

/** A started session and a graph over it; `log` lists each gate call the graph makes, with its answer. */
async function setup(tools) {
  let t = 0
  const raw = createGate({ kernel, policyText, store: new MemoryStore(), clock: () => (t += 1000) })
  const log = []
  const answer = (r) => r.verdict.decision ?? r.verdict.reason ?? r.verdict.verdict
  const gate = {
    ...raw,
    propose: async (sid, i) => {
      const r = await raw.propose(sid, i)
      log.push(["propose", i.callId, i.callDigest, answer(r)])
      return r
    },
    dispatch: async (sid, i) => {
      const r = await raw.dispatch(sid, i)
      log.push(["dispatch", i.callId, i.callDigest, answer(r)])
      return r
    },
    result: async (sid, i) => {
      log.push(["result", i.callId, i.outcome])
      return raw.result(sid, i)
    },
    outcomeUnknown: async (sid, callId) => {
      log.push(["outcome_unknown", callId])
      return raw.outcomeUnknown(sid, callId)
    },
  }
  await raw.start({
    sessionId: "s1", requester: "u1", permissions: [], userInitiated: true,
    approvers: { rev1: { principal: "carol", kind: "human", roles: ["reviewer"] } },
  })
  await raw.stepStart("s1")
  const runs = {}
  const counted = Object.fromEntries(Object.entries(tools).map(([name, fn]) => [
    name, async (args) => { runs[name] = (runs[name] ?? 0) + 1; return fn(args) },
  ]))
  const graph = buildGraph(gate, "s1", { tools: counted })
  const approve = (p, edit) => raw.approve("s1", {
    callId: p.callId, requestId: p.requestId, approverId: "rev1", reviewedDigest: p.callDigest, edit,
  })
  const reject = (p) => raw.reject("s1", { callId: p.callId, requestId: p.requestId, approverId: "rev1" })
  return { raw, gate, log, runs, graph, approve, reject, config: { configurable: { thread_id: "t1" } } }
}

const deploy = (callId, callDigest) => ({ callId, tool: "deploy.prod", callDigest })
const pendingOf = (out) => out.__interrupt__?.[0]?.value.pending

/** No ToolMessage tells the model "not run" for a call the gate claimed, or "already dispatched" for one it never claimed. */
function assertTruthful(messages, log) {
  const claimed = new Set(log.filter(([type, , , a]) => type === "dispatch" && a === "dispatch_claimed").map(([, id]) => id))
  const untrue = messages.filter((m) => {
    const text = String(m.content)
    return claimed.has(m.tool_call_id) ? text.startsWith("not run") : text.startsWith("already dispatched")
  })
  assert.deepEqual(untrue.map((m) => [m.tool_call_id, m.content]), [])
}

test("a resume without an update re-proposes the checkpointed call", async () => {
  const { graph, config, log, runs, approve } = await setup({ "deploy.prod": async () => "deployed" })
  const first = await graph.invoke({ calls: [deploy("c1", "d1")] }, config)
  const pending = pendingOf(first)
  assert.deepEqual(pending.map((p) => [p.callId, p.callDigest]), [["c1", "d1"]])
  await approve(pending[0])
  const second = await graph.invoke(new Command({ resume: true }), config)
  assert.equal(second.__interrupt__, undefined)
  assert.deepEqual(log, [
    ["propose", "c1", "d1", "needs_approval"],
    ["propose", "c1", "d1", "authorized"],
    ["dispatch", "c1", "d1", "dispatch_claimed"],
    ["result", "c1", "succeeded"],
  ])
  assert.equal(runs["deploy.prod"], 1)
})

test("the graph pauses again while a second call awaits approval", async () => {
  const { graph, config, log, runs, approve } = await setup({ "deploy.prod": async () => "deployed" })
  const first = await graph.invoke({ calls: [deploy("c1", "d1"), deploy("c2", "d2")] }, config)
  assert.deepEqual(pendingOf(first).map((p) => p.callId), ["c1", "c2"])
  await approve(pendingOf(first)[0])
  const second = await graph.invoke(new Command({ resume: true }), config)
  assert.deepEqual(pendingOf(second).map((p) => p.callId), ["c2"])
  assert.equal(runs["deploy.prod"], undefined)
  assert.deepEqual(log.filter(([type]) => type === "dispatch"), [])
  await approve(pendingOf(second)[0])
  const third = await graph.invoke(new Command({ resume: true }), config)
  assert.equal(third.__interrupt__, undefined)
  assert.equal(runs["deploy.prod"], 2)
  assert.deepEqual(log.filter(([type]) => type === "dispatch"), [
    ["dispatch", "c1", "d1", "dispatch_claimed"],
    ["dispatch", "c2", "d2", "dispatch_claimed"],
  ])
  assert.deepEqual(third.messages.map((m) => [m.tool_call_id, m.status, m.content]), [
    ["c1", "success", "deployed"],
    ["c2", "success", "deployed"],
  ])
  assertTruthful(third.messages, log)
})

test("a re-proposed call that already ran reports its recorded status", async () => {
  const { graph, config, log, runs, approve } = await setup({ "deploy.prod": async () => "deployed" })
  const first = await graph.invoke({ calls: [deploy("c1", "d1")] }, config)
  await approve(pendingOf(first)[0])
  await graph.invoke(new Command({ resume: true }), config)
  const again = await graph.invoke({ calls: [deploy("c1", "d1")] }, config)
  assert.deepEqual(again.messages.at(-1).content, "already dispatched: succeeded")
  assert.equal(runs["deploy.prod"], 1)
  assertTruthful(again.messages, log)
})

test("the default path dispatches each call id once", async () => {
  const { graph, config, log, runs, approve } = await setup({ "deploy.prod": async () => "deployed" })
  const first = await graph.invoke({ calls: [deploy("c1", "d1")] }, config)
  await approve(pendingOf(first)[0], { newDigest: "d1-canary", escalators: {} })
  // Both digests answer `authorized` after the edit; only the edited one can claim.
  await graph.invoke(new Command({ resume: true, update: { calls: [deploy("c1", "d1-canary"), deploy("c1", "d1")] } }), config)
  assert.deepEqual(log.filter(([type]) => type === "dispatch"), [["dispatch", "c1", "d1-canary", "dispatch_claimed"]])
  assert.equal(runs["deploy.prod"], 1)
})

test("a call with no tool function is refused before dispatch", async () => {
  const { graph, config, log } = await setup({})
  const out = await graph.invoke({ calls: [{ callId: "c1", tool: "notes.read", callDigest: "d1" }] }, config)
  assert.deepEqual(log, [["propose", "c1", "d1", "allowed"]])
  assert.equal(out.messages.at(-1).status, "error")
})

test("a report that throws is not turned into a failed tool", async () => {
  const { graph, config, log, runs, gate } = await setup({ "notes.read": async () => "notes" })
  gate.result = async (sid, i) => {
    log.push(["result", i.callId, i.outcome])
    throw new Error("store unavailable")
  }
  await assert.rejects(graph.invoke({ calls: [{ callId: "c1", tool: "notes.read", callDigest: "d1" }] }, config), /store unavailable/)
  assert.equal(runs["notes.read"], 1)
  assert.deepEqual(log.filter(([type]) => type === "result"), [["result", "c1", "succeeded"]])
})

test("a tool that throws after its dispatch is claimed is reported outcome unknown", async () => {
  const { raw, graph, config, log } = await setup({ "notes.read": async () => { throw new Error("timed out") } })
  const out = await graph.invoke({ calls: [{ callId: "c1", tool: "notes.read", callDigest: "d1" }] }, config)
  assert.deepEqual(log.filter(([type]) => type === "result" || type === "outcome_unknown"), [["outcome_unknown", "c1"]])
  assert.deepEqual(out.messages.map((m) => [m.tool_call_id, m.status, m.content]), [["c1", "error", "outcome unknown: timed out"]])
  const view = await raw.inspect("s1")
  assert.equal(view.calls.find((c) => c.call_id === "c1").status, "unknown")
  assertTruthful(out.messages, log)
})

test("a tool error survives an outcome report that throws", async () => {
  const { graph, config, log, gate } = await setup({ "notes.read": async () => { throw new Error("timed out") } })
  gate.outcomeUnknown = async (sid, callId) => {
    log.push(["outcome_unknown", callId])
    throw new Error("store unavailable")
  }
  const out = await graph.invoke({ calls: [{ callId: "c1", tool: "notes.read", callDigest: "d1" }] }, config)
  assert.deepEqual(log.filter(([type]) => type === "outcome_unknown"), [["outcome_unknown", "c1"]])
  assert.deepEqual(out.messages.map((m) => m.content), ["outcome unknown: timed out"])
})

test("a call cancelled between propose and dispatch reads not run", async () => {
  const { raw, gate, graph, config, log, runs } = await setup({ "notes.read": async () => "notes" })
  const dispatch = gate.dispatch
  gate.dispatch = async (sid, i) => {
    await raw.cancel(sid, i.callId)
    return dispatch(sid, i)
  }
  const out = await graph.invoke({ calls: [{ callId: "c1", tool: "notes.read", callDigest: "d1" }] }, config)
  assert.equal(runs["notes.read"], undefined)
  assert.deepEqual(out.messages.map((m) => [m.tool_call_id, m.status, m.content]), [["c1", "error", "not run: cancelled"]])
  assertTruthful(out.messages, log)
})

test("a rejected call dispatched anyway gets one not run message", async () => {
  const { graph, config, log, runs, reject } = await setup({ "deploy.prod": async () => "deployed" })
  const first = await graph.invoke({ calls: [deploy("c1", "d1")] }, config)
  await reject(pendingOf(first)[0])
  const out = await graph.invoke(new Command({ resume: true, update: { dispatch: [deploy("c1", "d1")] } }), config)
  assert.equal(runs["deploy.prod"], undefined)
  assert.deepEqual(out.messages.map((m) => [m.tool_call_id, m.status, m.content]), [["c1", "error", "not run: rejected"]])
  assertTruthful(out.messages, log)
})
