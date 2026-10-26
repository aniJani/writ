import assert from "node:assert/strict"
import { test } from "node:test"
import { callDigest, createGate, loadKernel, MemoryStore, WritInputError } from "../src/index.js"
import type { Gate } from "../src/index.js"
import { writTools } from "../src/ai-sdk.js"
import type { AiTool } from "../src/ai-sdk.js"

const policyText = JSON.stringify({
  writ: "0.1",
  approver_roles: ["user"],
  limits: { approval_ttl_ms: 600_000 },
  actions: { lookup: { consent: "none" }, deleteFile: { consent: "per_call" } },
})

async function setup(extra: Record<string, AiTool> = {}) {
  const gate: Gate = createGate({ kernel: await loadKernel(), policyText, store: new MemoryStore() })
  const sessionId = "s-1"
  await gate.start({
    sessionId,
    requester: "user:alice",
    permissions: [],
    approvers: { user: { principal: "user:alice", kind: "human", roles: ["user"] } },
    userInitiated: true,
  })
  const ran: { tool: string; input: unknown }[] = []
  const tools: Record<string, AiTool> = {
    lookup: { description: "look up", execute: async (input: unknown) => { ran.push({ tool: "lookup", input }); return { found: 3 } } },
    deleteFile: { execute: async (input: unknown) => { ran.push({ tool: "deleteFile", input }); return { deleted: true } } },
    ...extra,
  }
  const writ = writTools({ gate, sessionId, tools })
  const status = async (callId: string) => (await gate.inspect(sessionId))?.calls.find((c) => c.call_id === callId)?.status
  return { gate, sessionId, ran, writ, status }
}

const call = (toolCallId: string, toolName: string, input: unknown) => ({ toolCall: { toolCallId, toolName, input } })
const opts = (toolCallId: string) => ({ toolCallId, messages: [] })

test("an allowed tool is not-applicable and runs once through dispatch", async () => {
  const { ran, writ, status } = await setup()
  assert.equal(await writ.toolApproval(call("c1", "lookup", { q: "tea" })), "not-applicable")
  assert.deepEqual(writ.pending(), [])
  assert.equal(writ.tools.lookup?.description, "look up")
  assert.deepEqual(await writ.tools.lookup?.execute?.({ q: "tea" }, opts("c1")), { found: 3 })
  assert.deepEqual(ran, [{ tool: "lookup", input: { q: "tea" } }])
  assert.equal(await status("c1"), "succeeded")
})

test("a per_call tool asks for user approval and runs only after gate approval", async () => {
  const { ran, writ, status } = await setup()
  const input = { path: "/tmp/a.txt" }
  const answer = await writ.toolApproval(call("c1", "deleteFile", input))
  assert.equal(typeof answer === "object" && answer.type, "user-approval")
  const [p, ...rest] = writ.pending()
  assert.deepEqual(rest, [])
  assert.equal(p?.toolCallId, "c1")
  assert.equal(p?.tool, "deleteFile")
  assert.deepEqual(p?.input, input)
  assert.equal(p?.callDigest, await callDigest({ server: "ai-sdk", tool: "deleteFile", toolDigest: "unversioned", args: input }))
  assert.deepEqual(p?.requestId, { session: "s-1", call: "c1", generation: 0 })
  const r = await writ.approve("c1", "user")
  assert.equal(r.verdict.verdict, "accepted")
  assert.deepEqual(writ.pending(), [])
  // The SDK runs the approval function again when it resumes an approved call.
  assert.equal(await writ.toolApproval(call("c1", "deleteFile", input)), "not-applicable")
  assert.deepEqual(await writ.tools.deleteFile?.execute?.(input, opts("c1")), { deleted: true })
  assert.deepEqual(ran, [{ tool: "deleteFile", input }])
  assert.equal(await status("c1"), "succeeded")
})

test("an SDK approval without a Writ approval runs nothing (call_awaiting)", async () => {
  const { ran, writ, status } = await setup()
  const input = { path: "/tmp/a.txt" }
  await writ.toolApproval(call("c1", "deleteFile", input))
  await assert.rejects(writ.tools.deleteFile!.execute!(input, opts("c1")) as Promise<unknown>, /^Error: writ: call_awaiting: /)
  assert.deepEqual(ran, [])
  assert.equal(await status("c1"), "awaiting")
  assert.equal(writ.pending().length, 1)
})

test("a rejected call is denied on resume and does not run", async () => {
  const { ran, writ, status } = await setup()
  const input = { path: "/tmp/a.txt" }
  await writ.toolApproval(call("c1", "deleteFile", input))
  assert.equal((await writ.reject("c1", "user")).verdict.verdict, "accepted")
  assert.deepEqual(writ.pending(), [])
  const again = await writ.toolApproval(call("c1", "deleteFile", input))
  assert.equal(typeof again === "object" && again.type, "denied")
  await assert.rejects(writ.tools.deleteFile!.execute!(input, opts("c1")) as Promise<unknown>, /^Error: writ: call_ended: /)
  assert.deepEqual(ran, [])
  assert.equal(await status("c1"), "rejected")
})

test("an edited input after approval is refused digest_mismatch and the tool does not run", async () => {
  const { ran, writ, status } = await setup()
  await writ.toolApproval(call("c1", "deleteFile", { path: "/tmp/a.txt" }))
  await writ.approve("c1", "user")
  const edited = { path: "/etc/passwd" }
  const answer = await writ.toolApproval(call("c1", "deleteFile", edited))
  assert.equal(typeof answer === "object" && answer.type, "denied")
  assert.match(typeof answer === "object" ? answer.reason ?? "" : "", /^writ: duplicate_call: /)
  await assert.rejects(writ.tools.deleteFile!.execute!(edited, opts("c1")) as Promise<unknown>, /^Error: writ: digest_mismatch: The call's contents differ/)
  assert.deepEqual(ran, [])
  assert.equal(await status("c1"), "authorized")
})

test("a replayed execute after success is refused and the tool runs once", async () => {
  const { ran, writ } = await setup()
  const input = { path: "/tmp/a.txt" }
  await writ.toolApproval(call("c1", "deleteFile", input))
  await writ.approve("c1", "user")
  await writ.tools.deleteFile!.execute!(input, opts("c1"))
  const again = await writ.toolApproval(call("c1", "deleteFile", input))
  assert.deepEqual(again, { type: "denied", reason: "writ: call already succeeded" })
  await assert.rejects(writ.tools.deleteFile!.execute!(input, opts("c1")) as Promise<unknown>, /^Error: writ: call_ended: /)
  assert.equal(ran.length, 1)
})

test("an unknown tool is denied unknown_tool", async () => {
  let shellRan = false
  const { writ, status } = await setup({ shell: { execute: async () => { shellRan = true } } })
  const answer = await writ.toolApproval(call("c1", "shell", { cmd: "rm -rf /" }))
  assert.equal(typeof answer === "object" && answer.type, "denied")
  assert.match(typeof answer === "object" ? answer.reason ?? "" : "", /^writ: unknown_tool: This tool is not part of the policy/)
  assert.deepEqual(writ.pending(), [])
  await assert.rejects(writ.tools.shell!.execute!({ cmd: "rm -rf /" }, opts("c1")) as Promise<unknown>, /^Error: writ: unknown_call: /)
  assert.equal(shellRan, false)
  assert.equal(await status("c1"), undefined)
  for (const name of ["constructor", "__proto__", "toString"]) {
    const a = await writ.toolApproval(call(`p-${name}`, name, {}))
    assert.match(typeof a === "object" ? a.reason ?? "" : "", /^writ: unknown_tool: /, name)
  }
})

test("a fabricated toolCallId with no proposal is refused unknown_call", async () => {
  const { ran, writ } = await setup()
  await assert.rejects(writ.tools.deleteFile!.execute!({ path: "/etc/passwd" }, opts("forged")) as Promise<unknown>, /^Error: writ: unknown_call: /)
  await assert.rejects(writ.tools.lookup!.execute!({ q: "x" }, opts("forged-2")) as Promise<unknown>, /^Error: writ: unknown_call: /)
  await assert.rejects(writ.tools.lookup!.execute!({ q: "x" }, {}) as Promise<unknown>, (e) => e instanceof WritInputError && e.path === "options.toolCallId")
  assert.deepEqual(ran, [])
})

test("a throwing tool is reported outcomeUnknown and rethrown", async () => {
  const { writ, status } = await setup({ lookup: { execute: async () => { throw new Error("boom") } } })
  await writ.toolApproval(call("c1", "lookup", {}))
  await assert.rejects(writ.tools.lookup!.execute!({}, opts("c1")) as Promise<unknown>, /^Error: boom$/)
  assert.equal(await status("c1"), "unknown")
  await assert.rejects(writ.tools.lookup!.execute!({}, opts("c1")) as Promise<unknown>, /^Error: writ: retry_not_allowed: /)
})

test("needsApproval or a missing execute is a WritInputError", async () => {
  const gate = createGate({ kernel: await loadKernel(), policyText, store: new MemoryStore() })
  const execute = async () => 1
  assert.throws(() => writTools({ gate, sessionId: "s", tools: { a: { execute, needsApproval: true } } }),
    (e) => e instanceof WritInputError && e.path === "tools.a")
  assert.throws(() => writTools({ gate, sessionId: "s", tools: { a: { execute, needsApproval: false } } }),
    (e) => e instanceof WritInputError && e.path === "tools.a")
  assert.throws(() => writTools({ gate, sessionId: "s", tools: { b: { description: "provider tool" } } }),
    (e) => e instanceof WritInputError && e.path === "tools.b")
})

test("a toolDigests value that is not a non-empty string, or a cost that is not a function, throws at construction", async () => {
  const gate = createGate({ kernel: await loadKernel(), policyText, store: new MemoryStore() })
  const tools = { a: { execute: async () => 1 } }
  const bad = (extra: object, path: string) =>
    assert.throws(() => writTools({ gate, sessionId: "s", tools, ...extra }), (e) => e instanceof WritInputError && e.path === path)
  bad({ toolDigests: { a: "" } }, "toolDigests.a")
  bad({ toolDigests: { a: 7 } }, "toolDigests.a")
  bad({ toolDigests: { a: "v1", b: null } }, "toolDigests.b")
  bad({ toolDigests: "v1" }, "toolDigests")
  bad({ cost: { a: { amount: 1 } } }, "cost.a")
  bad({ cost: { a: () => undefined, b: "free" } }, "cost.b")
  bad({ cost: [() => undefined] }, "cost")
  assert.doesNotThrow(() => writTools({ gate, sessionId: "s", tools, toolDigests: { a: "v1" }, cost: { a: () => undefined } }))
})

test("approve and reject need a call awaiting approval", async () => {
  const { writ } = await setup()
  await assert.rejects(writ.approve("nope", "user"), (e) => e instanceof WritInputError && e.path === "toolCallId")
  await assert.rejects(writ.reject("nope", "user"), (e) => e instanceof WritInputError && e.path === "toolCallId")
})

test("toolDigests and cost enter the digest, and the recorded cost is reviewed", async () => {
  const money = JSON.stringify({
    writ: "0.1",
    approver_roles: ["user"],
    meters: { spend: { scope: "session", currency: "USD", cap: 10 } },
    actions: { buy: { consent: "per_call", meters: ["spend"] } },
  })
  const kernel = await loadKernel()
  assert.equal(kernel.check(money).ok, true, JSON.stringify(kernel.check(money).errors))
  const gate = createGate({ kernel, policyText: money, store: new MemoryStore() })
  await gate.start({
    sessionId: "m", requester: "u", permissions: [],
    approvers: { user: { principal: "u", kind: "human", roles: ["user"] } }, userInitiated: true,
  })
  let bought = 0
  const writ = writTools({
    gate, sessionId: "m", server: "shop", toolDigests: { buy: "sha256:tool-v2" },
    tools: { buy: { execute: async (_input: unknown, _options: unknown) => ++bought } },
    cost: { buy: (input) => ({ amount: String((input as { usd: number }).usd), currency: "USD" }) },
  })
  await writ.toolApproval(call("c1", "buy", { usd: 4 }))
  const p = writ.pending()[0]
  assert.deepEqual(p?.cost, { amount: "4", currency: "USD" })
  assert.equal(p?.callDigest, await callDigest({ server: "shop", tool: "buy", toolDigest: "sha256:tool-v2", args: { usd: 4 }, cost: { amount: "4", currency: "USD" } }))
  assert.equal((await writ.approve("c1", "user")).verdict.verdict, "accepted")
  assert.equal(await writ.tools.buy!.execute!({ usd: 4 }, opts("c1")), 1)
})

test("pending() keeps a quorum call listed until it is decided", async () => {
  const quorum = JSON.stringify({
    writ: "0.1",
    approver_roles: ["user"],
    actions: { deleteFile: { consent: { all: [{ quorum: 2, roles: ["user"] }] } } },
  })
  const kernel = await loadKernel()
  assert.equal(kernel.check(quorum).ok, true, JSON.stringify(kernel.check(quorum).errors))
  const gate = createGate({ kernel, policyText: quorum, store: new MemoryStore() })
  await gate.start({
    sessionId: "q", requester: "u", permissions: [], userInitiated: true,
    approvers: {
      a: { principal: "user:a", kind: "human", roles: ["user"] },
      b: { principal: "user:b", kind: "human", roles: ["user"] },
    },
  })
  let ran = 0
  const writ = writTools({ gate, sessionId: "q", tools: { deleteFile: { execute: async (_input: unknown, _options: unknown) => ++ran } } })
  await writ.toolApproval(call("c1", "deleteFile", { path: "/tmp/a" }))
  assert.equal((await writ.approve("c1", "a")).verdict.verdict, "accepted")
  assert.equal(writ.pending().length, 1)
  await assert.rejects(writ.tools.deleteFile.execute({ path: "/tmp/a" }, opts("c1")) as Promise<unknown>, /^Error: writ: call_awaiting: /)
  assert.equal((await writ.approve("c1", "b")).verdict.verdict, "accepted")
  assert.deepEqual(writ.pending(), [])
  assert.equal(await writ.tools.deleteFile.execute({ path: "/tmp/a" }, opts("c1")), 1)
})

test("a streaming execute runs through dispatch, yields every item, and succeeds only after the last", async () => {
  const log: unknown[] = []
  let status: (callId: string) => Promise<unknown> = async () => undefined
  const s = await setup({
    lookup: {
      execute: async function* (input: unknown) {
        log.push(input)
        yield { step: 1 }
        log.push(await status("c1"))
        yield { step: 2 }
      },
    },
  })
  status = s.status
  assert.equal(await s.writ.toolApproval(call("c1", "lookup", { q: "tea" })), "not-applicable")
  const out = s.writ.tools.lookup!.execute!({ q: "tea" }, opts("c1")) as AsyncIterable<unknown>
  assert.equal(typeof out[Symbol.asyncIterator], "function")
  const items: unknown[] = []
  for await (const item of out) items.push(item)
  assert.deepEqual(items, [{ step: 1 }, { step: 2 }])
  assert.deepEqual(log, [{ q: "tea" }, "dispatched"])
  assert.equal(await s.status("c1"), "succeeded")
})

test("a streaming execute that throws or is stopped early is reported outcomeUnknown", async () => {
  const s = await setup({
    lookup: { execute: async function* () { yield 1; throw new Error("boom") } },
    deleteFile: { execute: async function* () { yield 1; yield 2 } },
  })
  await s.writ.toolApproval(call("c1", "lookup", {}))
  const items: unknown[] = []
  await assert.rejects((async () => { for await (const i of s.writ.tools.lookup!.execute!({}, opts("c1")) as AsyncIterable<unknown>) items.push(i) })(), /^Error: boom$/)
  assert.deepEqual(items, [1])
  assert.equal(await s.status("c1"), "unknown")
  await s.writ.toolApproval(call("c2", "deleteFile", {}))
  await s.writ.approve("c2", "user")
  for await (const _ of s.writ.tools.deleteFile!.execute!({}, opts("c2")) as AsyncIterable<unknown>) break
  assert.equal(await s.status("c2"), "unknown")
})

test("a refused streaming execute never starts the generator", async () => {
  let started = false
  const s = await setup({ lookup: { execute: async function* () { started = true; yield 1 } } })
  const out = s.writ.tools.lookup!.execute!({}, opts("forged")) as AsyncIterable<unknown>
  await assert.rejects((async () => { for await (const _ of out) {} })(), /^Error: writ: unknown_call: /)
  assert.equal(started, false)
})

test("a plain execute that returns an async iterable is drained and returns the last item", async () => {
  const s = await setup({
    lookup: { execute: (_input: unknown, _options: unknown) => (async function* () { yield 1; yield 2 })() },
  })
  await s.writ.toolApproval(call("c1", "lookup", {}))
  assert.equal(await s.writ.tools.lookup!.execute!({}, opts("c1")), 2)
  assert.equal(await s.status("c1"), "succeeded")
})

test("an input that is not plain JSON is denied invalid_input and never proposed or dispatched", async () => {
  const s = await setup()
  for (const [id, input, path] of [["c1", { n: 12345678901234567890 }, "args.n"], ["c2", { when: new Date(0) }, "args.when"]] as const) {
    const answer = await s.writ.toolApproval(call(id, "lookup", input))
    assert.equal(typeof answer === "object" && answer.type, "denied")
    assert.match(typeof answer === "object" ? answer.reason ?? "" : "", new RegExp(`^writ: invalid_input: ${path}: `))
    await assert.rejects(s.writ.tools.lookup!.execute!(input, opts(id)) as Promise<unknown>, new RegExp(`^Error: writ: invalid_input: ${path}: `))
  }
  assert.deepEqual((await s.gate.inspect(s.sessionId))?.calls, [])
  assert.deepEqual(s.ran, [])
})

test("a fresh writTools instance approves with the shown input, and the tool runs once", async () => {
  const s = await setup()
  const input = { path: "/tmp/a.txt" }
  await s.writ.toolApproval(call("c1", "deleteFile", input))
  let ran = 0
  const tools = { deleteFile: { execute: async (_input: unknown, _options: unknown) => ++ran } }
  const fresh = writTools({ gate: s.gate, sessionId: s.sessionId, tools })
  assert.deepEqual(fresh.pending(), [])
  await assert.rejects(fresh.approve("c1", "user"), (e) => e instanceof WritInputError && e.path === "toolCallId")
  const wrong = await fresh.approve("c1", "user", { tool: "deleteFile", input: { path: "/etc/passwd" } })
  assert.equal(wrong.verdict.verdict === "rejected" && wrong.verdict.reason, "digest_mismatch")
  assert.equal(await s.status("c1"), "awaiting")
  assert.equal((await fresh.approve("c1", "user", { tool: "deleteFile", input })).verdict.verdict, "accepted")
  const next = writTools({ gate: s.gate, sessionId: s.sessionId, tools })
  assert.equal(await next.tools.deleteFile.execute(input, opts("c1")), 1)
  await assert.rejects(next.tools.deleteFile.execute(input, opts("c1")), /^Error: writ: call_ended: /)
  assert.equal(ran, 1)
})

test("a fresh writTools instance can reject, and a shown input wins over the recorded one", async () => {
  const s = await setup()
  const input = { path: "/tmp/a.txt" }
  await s.writ.toolApproval(call("c1", "deleteFile", input))
  const r = await s.writ.approve("c1", "user", { tool: "deleteFile", input: { path: "/etc/passwd" } })
  assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "digest_mismatch")
  assert.equal(s.writ.pending().length, 1)
  const fresh = writTools({ gate: s.gate, sessionId: s.sessionId, tools: { deleteFile: { execute: async () => 1 } } })
  assert.equal((await fresh.reject("c1", "user")).verdict.verdict, "accepted")
  assert.equal(await s.status("c1"), "rejected")
  await assert.rejects(fresh.reject("c1", "user"), (e) => e instanceof WritInputError && e.path === "toolCallId")
})

test("a refused re-proposal of an awaiting call keeps it pending", async () => {
  const s = await setup()
  await s.writ.toolApproval(call("c1", "deleteFile", { path: "/tmp/a.txt" }))
  const edited = await s.writ.toolApproval(call("c1", "deleteFile", { path: "/etc/passwd" }))
  assert.match(typeof edited === "object" ? edited.reason ?? "" : "", /^writ: duplicate_call: /)
  assert.deepEqual(s.writ.pending().map((p) => p.input), [{ path: "/tmp/a.txt" }])
  assert.equal((await s.writ.approve("c1", "user")).verdict.verdict, "accepted")
})

test("wrapped tools keep non-enumerable properties", async () => {
  const caller = { kind: "caller" }
  const t: AiTool = { execute: async () => 1 }
  Object.defineProperty(t, "experimental_toolCaller", { value: caller })
  const s = await setup({ lookup: t })
  assert.equal(s.writ.tools.lookup?.experimental_toolCaller, caller)
  assert.notEqual(s.writ.tools.lookup?.execute, t.execute)
})
