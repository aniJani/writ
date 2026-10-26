import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { test } from "node:test"
import { Command } from "@langchain/langgraph"
import { createGate, loadKernel, MemoryStore } from "@anijani/writ"
import { buildGraph } from "../graph.mjs"

const traces = readFileSync(new URL("../../../corpus/examples/langgraph-resume.jsonl", import.meta.url), "utf8")
  .split("\n").filter((l) => l.trim() !== "").map((l) => JSON.parse(l))
const kernel = await loadKernel()

// The gate stamps seq, time and state_version itself, so it never sends an event these reject.
const UNSENDABLE = new Set(["stale_seq", "state_version_mismatch", "time_decreasing"])
const EXCLUDED = {
  "langgraph-resume/approval-hours-later": 0,
  "langgraph-resume/edit-restarts-tally": 0,
  "langgraph-resume/resumed-repeat-edited-digest": 0,
  "langgraph-resume/argument-swap": 0,
}
const GRAPH_SIDE = new Set(["propose", "dispatch", "result"])
const ALLOWED = new Set(["allowed", "allowed_by_grant", "authorized"])

const withoutStateVersion = ({ state_version, ...rest }) => rest

/** Wraps the gate so each call runs at the time of the trace event it stands for, and is recorded. */
function recording(gate, events, clock) {
  const recorded = []
  let next = 0
  const wrap = (type, method) => async (...args) => {
    if (events[next]?.event.type === type) clock.now = events[next++].event.time
    const r = await method(...args)
    recorded.push({ type, verdict: r.verdict })
    return r
  }
  return {
    recorded,
    gate: {
      ...gate,
      start: wrap("session_start", gate.start),
      turnStart: wrap("turn_start", gate.turnStart),
      turnEnd: wrap("turn_end", gate.turnEnd),
      stepStart: wrap("step_start", gate.stepStart),
      approve: wrap("approve", gate.approve),
      reject: wrap("reject", gate.reject),
      propose: wrap("propose", gate.propose),
      dispatch: wrap("dispatch", gate.dispatch),
      result: wrap("result", gate.result),
    },
  }
}

function control(gate, sid, e) {
  switch (e.type) {
    case "session_start":
      return gate.start({ sessionId: sid, requester: e.requester, permissions: e.permissions, approvers: e.approvers })
    case "turn_start": return gate.turnStart(sid, e.user_initiated)
    case "turn_end": return gate.turnEnd(sid)
    case "step_start": return gate.stepStart(sid)
    case "approve":
      return gate.approve(sid, {
        callId: e.call_id, requestId: e.request_id, approverId: e.approver, reviewedDigest: e.reviewed_digest,
        edit: e.edit && { newDigest: e.edit.new_digest, escalators: e.edit.escalators },
      })
    case "reject": return gate.reject(sid, { callId: e.call_id, requestId: e.request_id, approverId: e.approver })
    default: throw new Error(`no control-plane method for ${e.type}`)
  }
}

/**
 * Splits the trace into control events and graph steps. A step is a run of propose, dispatch and result
 * events; a propose after a dispatch or result starts the next step, since the node proposes first.
 */
function plan(events) {
  const out = []
  const tools = new Map()
  let step = null
  for (const { event: e, expect } of events) {
    if (!GRAPH_SIDE.has(e.type)) {
      step = null
      out.push({ control: e })
      continue
    }
    if (step === null || (e.type === "propose" && step.dispatched)) {
      step = { calls: [], dispatch: [], allowed: [], dispatched: false }
      out.push({ step })
    }
    if (e.type === "propose") {
      tools.set(e.call_id, e.tool)
      const call = { callId: e.call_id, tool: e.tool, callDigest: e.call_digest }
      step.calls.push(call)
      if (expect.verdict === "accepted" && ALLOWED.has(expect.decision)) step.allowed.push(call)
    } else if (e.type === "dispatch") {
      step.dispatch.push({ callId: e.call_id, tool: tools.get(e.call_id), callDigest: e.call_digest })
      step.dispatched = true
    } else {
      assert.equal(e.outcome, "succeeded", "the scripted tools always succeed")
      step.dispatched = true
    }
  }
  for (const s of out) {
    if (s.step === undefined) continue
    const { calls, dispatch, allowed } = s.step
    // The node dispatches the allowed calls by default; a trace that dispatches anything else lists it.
    s.input = { calls, dispatch: JSON.stringify(dispatch) === JSON.stringify(allowed) ? null : dispatch }
  }
  return out
}

/** `live` receives the graph and the resumes as they happen, for tools that act during the replay. */
async function replay(trace, { tools = {}, live = {} } = {}) {
  const events = trace.events.filter(({ expect }) => !UNSENDABLE.has(expect?.reason))
  const clock = { now: 0 }
  const raw = createGate({ kernel, policyText: JSON.stringify(trace.policy), store: new MemoryStore(), clock: () => clock.now })
  const { gate, recorded } = recording(raw, events, clock)
  const sid = events[0].event.session_id
  const runs = {}
  const counted = Object.fromEntries([...new Set(trace.events.map(({ event }) => event.tool).filter(Boolean))].map((name) => [
    name, async (args) => { runs[name] = (runs[name] ?? 0) + 1; await tools[name]?.(args); return `${name} done` },
  ]))
  const graph = buildGraph(gate, sid, { tools: counted })
  const config = { configurable: { thread_id: trace.id } }
  const resumes = []
  Object.assign(live, { graph, resumes })
  let interrupted = false
  for (const s of plan(events)) {
    if (s.control !== undefined) {
      await control(gate, sid, s.control)
      continue
    }
    let out
    if (interrupted) {
      const command = new Command({ resume: { approved: true }, update: s.input })
      resumes.push({ from: (await graph.getState(config)).config, command })
      out = await graph.invoke(command, config)
    } else {
      out = await graph.invoke(s.input, config)
    }
    interrupted = (out.__interrupt__ ?? []).length > 0
  }
  return { events, recorded, runs, excluded: trace.events.length - events.length }
}

test("the corpus has exactly the traces this file accounts for", () => {
  assert.deepEqual(traces.map((t) => t.id), Object.keys(EXCLUDED))
})

for (const trace of traces) {
  test(`${trace.id} through a LangGraph graph`, async () => {
    const { events, recorded, excluded } = await replay(trace)
    assert.equal(excluded, EXCLUDED[trace.id])
    const got = recorded.map(({ type }, i) => {
      const keys = Object.keys(withoutStateVersion(events[i]?.expect ?? {}))
      return { type, expect: Object.fromEntries(keys.map((k) => [k, recorded[i].verdict[k]])) }
    })
    const want = events.map(({ event, expect }) => ({ type: event.type, expect: withoutStateVersion(expect ?? {}) }))
    assert.deepEqual(got, want)
  })
}

test("a resume delivered twice runs the deploy once", async () => {
  const trace = traces.find((t) => t.id === "langgraph-resume/approval-hours-later")
  const live = {}
  let second = null
  const { runs, recorded } = await replay(trace, {
    live,
    tools: {
      "deploy.prod": async () => {
        if (second !== null) return
        // A second worker resumes from the same interrupted checkpoint while the deploy is running. Its
        // propose answers `existing`, so it lists the dispatch itself, to show the gate refuses it anyway.
        const { from, command } = live.resumes[0]
        const deploy = { callId: "c1", tool: "deploy.prod", callDigest: "d-deploy-v42" }
        second = live.graph.invoke(new Command({ resume: command.resume, update: { calls: [deploy], dispatch: [deploy] } }), from)
        await second
      },
    },
  })
  assert.equal(runs["deploy.prod"], 1)
  const dispatches = recorded.filter((r) => r.type === "dispatch").map((r) => r.verdict)
  assert.deepEqual(dispatches.map((v) => [v.verdict, v.decision ?? v.reason]), [
    ["accepted", "dispatch_claimed"],
    ["rejected", "call_dispatched"],
  ])
  assert.equal((await second).messages.at(-1).status, "error")
  for (const m of (await second).messages) assert.ok(!String(m.content).startsWith("not run"), m.content)
  const results = recorded.filter((r) => r.type === "result").map((r) => r.verdict.verdict)
  assert.deepEqual(results, ["accepted"])
})
