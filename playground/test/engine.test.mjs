import assert from "node:assert/strict"
import { readdirSync, readFileSync } from "node:fs"
import { test } from "node:test"
import { loadKernel } from "../../packages/writ/dist/src/index.js"
import {
  SAMPLE_POLICY, SERVE_HINT, bootKernel, createPlayground, digestFor, parseScenarios, playScenario,
} from "../engine.js"

const kernel = await loadKernel()
const corpus = new URL("../../corpus/examples/", import.meta.url)
const corpusFiles = readdirSync(corpus).filter((f) => f.endsWith(".jsonl")).sort()

function started() {
  const made = createPlayground(kernel, SAMPLE_POLICY)
  assert.equal(made.ok, true)
  const { session } = made
  for (const type of ["session_start", "turn_start", "step_start"]) {
    assert.equal(session.apply(type === "session_start" ? sessionStart() : { type, ...(type === "turn_start" && { user_initiated: true }) }).verdict.verdict, "accepted", type)
  }
  return session
}

function sessionStart() {
  return {
    type: "session_start", session_id: "s1", requester: "visitor", permissions: [],
    approvers: { user: { principal: "user", kind: "human", roles: ["user"] } }, ledger: {},
  }
}

const EMAIL = { to: "ana@example.com", subject: "Lunch" }

test("the sample policy checks with no errors or warnings", () => {
  const report = kernel.check(SAMPLE_POLICY)
  assert.deepEqual([report.ok, report.errors, report.warnings], [true, [], []])
})

test("a bad policy returns check errors and no session", () => {
  const bad = createPlayground(kernel, JSON.stringify({ writ: "0.1", actions: { a: { meters: ["nope"] } } }))
  assert.equal(bad.ok, false)
  assert.equal(bad.errors[0].code, "unknown_meter")
  assert.equal(bad.session, undefined)
  const unparsed = createPlayground(kernel, '{"writ":"0.1","actions":{"a":{"consnet":"per_call"}}}')
  assert.equal(unparsed.ok, false)
  assert.equal(unparsed.errors[0].code, "invalid_policy")
  assert.match(unparsed.errors[0].message, /actions\.a\.consnet: unknown field/)
  assert.equal(createPlayground(kernel, "{not json").ok, false)
})

test("apply fills seq, time and state_version", () => {
  const session = started()
  const events = session.history.map((h) => h.event)
  assert.deepEqual(events.map((e) => [e.seq, e.time, e.state_version]), [[1, 0, 0], [2, 1000, 1], [3, 2000, 2]])
  assert.equal(events[0].policy_digest, kernel.check(SAMPLE_POLICY).policy_digest)
  const r = session.apply({ type: "turn_end", time: 9000 })
  assert.deepEqual([r.event.seq, r.event.time, r.event.state_version], [4, 9000, 3])
  assert.equal(session.apply({ type: "turn_start", user_initiated: true }).event.time, 10000)
})

test("propose send_email needs approval, approve, dispatch claims", async () => {
  const session = started()
  const proposed = await session.send("propose", {
    callId: "c1", tool: "send_email", args: JSON.stringify(EMAIL), costAmount: "25", costCurrency: "USD",
  })
  assert.equal(proposed.verdict.decision, "needs_approval")
  assert.deepEqual(proposed.verdict.request_id, { session: "s1", call: "c1", generation: 0 })
  assert.equal(proposed.event.call_digest, await digestFor("send_email", EMAIL))
  assert.equal(proposed.view.calls[0].status, "awaiting")

  const approved = await session.send("approve", { callId: "c1" })
  assert.deepEqual([approved.verdict.verdict, approved.verdict.decision], ["accepted", "authorized"])

  const searched = await session.send("propose", { callId: "c2", tool: "web_search", args: '{"q":"weather"}' })
  assert.equal(searched.verdict.decision, "allowed")

  const dispatched = await session.send("dispatch", { callId: "c1" })
  assert.equal(dispatched.verdict.decision, "dispatch_claimed")
  const done = await session.send("result", { callId: "c1", outcome: "succeeded" })
  assert.equal(done.verdict.verdict, "accepted")
  const call = done.view.calls.find((c) => c.call_id === "c1")
  assert.equal(call.status, "succeeded")
  assert.equal(done.view.meters.find((m) => m.meter === "spend").used, "25")
})

test("a rejected step keeps the state", async () => {
  const session = started()
  await session.send("propose", { callId: "c1", tool: "send_email", args: JSON.stringify(EMAIL), costAmount: "25" })
  const before = session.view
  const r = await session.send("dispatch", { callId: "c1" })
  assert.deepEqual([r.verdict.verdict, r.verdict.reason], ["rejected", "call_awaiting"])
  assert.deepEqual(r.view, before)
  assert.deepEqual(session.view, before)
  const next = session.apply({ type: "step_start" })
  assert.equal(next.event.seq, r.event.seq, "a rejected event does not use up its seq")
  assert.equal(next.event.time, r.event.time, "a rejected event does not advance the clock")
  assert.equal(next.verdict.verdict, "accepted")
})

test("malformed event JSON is a returned error, not a throw", async () => {
  const session = started()
  const before = session.view
  const history = session.history.length
  for (const raw of ["{\"type\":", "[1,2]", "42", '{"type":"propose","call_id":"c9"}', '{"type":"warp"}']) {
    const r = session.apply(raw)
    assert.equal(r.ok, false, raw)
    assert.ok(r.error.code && r.error.message, raw)
    assert.deepEqual(r.view, before, raw)
  }
  const badArgs = await session.send("propose", { callId: "c1", tool: "send_email", args: "{oops" })
  assert.equal(badArgs.ok, false)
  assert.equal(badArgs.error.code, "invalid_arguments")
  assert.deepEqual(session.view, before)
  assert.equal(session.history.length, history)
  assert.equal(session.apply('{"type":"step_start"}').verdict.verdict, "accepted")
})

test("every corpus scenario plays with every step matching", () => {
  assert.ok(corpusFiles.length >= 6)
  let traces = 0
  for (const file of corpusFiles) {
    const scenarios = parseScenarios(readFileSync(new URL(file, corpus), "utf8"))
    assert.ok(scenarios.length > 0, file)
    for (const scenario of scenarios) {
      traces++
      assert.ok(scenario.id && scenario.policy && scenario.events.length > 0, scenario.id)
      const rows = playScenario(kernel, scenario)
      assert.equal(rows.length, scenario.events.length, scenario.id)
      rows.forEach((row, i) => assert.equal(row.matches, true, `${scenario.id} step ${i}: ${JSON.stringify(row.verdict)} vs ${JSON.stringify(row.expect)}`))
    }
  }
  assert.ok(traces >= 24)
})

test("a scenario step that misses its expect is marked", () => {
  const [scenario] = parseScenarios(readFileSync(new URL("web-chat.jsonl", corpus), "utf8"))
  const wrong = { ...scenario, events: scenario.events.map((e, i) => (i === 0 ? { ...e, expect: { verdict: "rejected" } } : e)) }
  const rows = playScenario(kernel, wrong)
  assert.deepEqual(rows.map((r) => r.matches).slice(0, 2), [false, true])
})

test("a changed digest at dispatch is refused", async () => {
  const session = started()
  await session.send("propose", { callId: "c1", tool: "send_email", args: JSON.stringify(EMAIL), costAmount: "25" })
  await session.send("approve", { callId: "c1" })
  const swapped = await session.send("dispatch", { callId: "c1", args: JSON.stringify({ ...EMAIL, to: "eve@example.com" }) })
  assert.equal(swapped.verdict.reason, "digest_mismatch")
  assert.notEqual(swapped.verdict.decision, "dispatch_claimed")
  assert.equal(swapped.view.calls[0].status, "authorized")
  assert.ok(session.history.every((h) => h.verdict.decision !== "dispatch_claimed"))
})

test("loading from file:// or a failed kernel load says to serve the page", async () => {
  const fromFile = await bootKernel({ protocol: "file:", load: () => assert.fail("must not load from file://") })
  assert.deepEqual(fromFile, { ok: false, message: SERVE_HINT })
  assert.equal(SERVE_HINT, "Serve this page: run node playground/build.mjs && node playground/serve.mjs")
  const failed = await bootKernel({ protocol: "http:", load: async () => { throw new TypeError("Failed to fetch") } })
  assert.equal(failed.ok, false)
  assert.ok(failed.message.startsWith(SERVE_HINT))
  assert.match(failed.message, /Failed to fetch/)
  const ok = await bootKernel({ protocol: "http:", load: async () => kernel })
  assert.deepEqual(ok, { ok: true, kernel })
})

test("a rejected re-proposal does not replace the guards a dispatch sends", async () => {
  const session = started()
  const first = await session.send("propose", { callId: "c1", tool: "send_email", args: JSON.stringify(EMAIL), costAmount: "25", guards: "signed_in" })
  assert.equal(first.verdict.decision, "needs_approval")
  const again = await session.send("propose", { callId: "c1", tool: "send_email", args: JSON.stringify({ ...EMAIL, to: "eve@example.com" }), costAmount: "25" })
  assert.deepEqual([again.verdict.verdict, again.verdict.reason], ["rejected", "duplicate_call"])
  await session.send("approve", { callId: "c1" })
  const dispatched = await session.send("dispatch", { callId: "c1" })
  assert.equal(dispatched.verdict.decision, "dispatch_claimed")
  assert.deepEqual(dispatched.event.guards, { signed_in: true })
})

test("the page's file:// hint is SERVE_HINT", () => {
  const html = readFileSync(new URL("../index.html", import.meta.url), "utf8")
  const attr = html.match(/data-serve-hint="([^"]*)"/)
  assert.ok(attr, "index.html has a data-serve-hint attribute")
  assert.equal(attr[1], SERVE_HINT.replaceAll("&", "&amp;"))
})
