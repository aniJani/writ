import assert from "node:assert/strict"
import { test } from "node:test"
import { generateText, simulateReadableStream, streamText, tool } from "ai"
import { MockLanguageModelV4 } from "ai/test"
import { z } from "zod"
import { createGate, loadKernel, MemoryStore } from "@anijani/writ"
import { writTools } from "@anijani/writ/ai-sdk"

const policyText = JSON.stringify({
  writ: "0.1",
  approver_roles: ["user"],
  limits: { approval_ttl_ms: 600_000 },
  actions: {
    deleteFile: { consent: "per_call" },
    readFile: { consent: "none" },
    progress: { consent: "none" },
    count: { consent: "none" },
    schedule: { consent: "none" },
  },
})

const usage = {
  inputTokens: { total: 1, noCache: 1, cacheRead: undefined, cacheWrite: undefined },
  outputTokens: { total: 1, text: 1, reasoning: undefined },
}
const toolCallsTurn = (...calls) => ({
  content: calls.map(([toolCallId, toolName, input]) =>
    ({ type: "tool-call", toolCallId, toolName, input: typeof input === "string" ? input : JSON.stringify(input) })),
  finishReason: { unified: "tool-calls", raw: undefined }, usage, warnings: [],
})
const toolCallTurn = (toolName, input) => toolCallsTurn(["call-1", toolName, input])
const textTurn = { content: [{ type: "text", text: "done" }], finishReason: { unified: "stop", raw: undefined }, usage, warnings: [] }

async function setup(turns) {
  const gate = createGate({ kernel: await loadKernel(), policyText, store: new MemoryStore() })
  const sessionId = "chat-1"
  await gate.start({
    sessionId,
    requester: "user:alice",
    permissions: [],
    approvers: { user: { principal: "user:alice", kind: "human", roles: ["user"] } },
    userInitiated: true,
  })
  const executed = []
  const build = () => writTools({
    gate,
    sessionId,
    tools: {
      deleteFile: tool({
        inputSchema: z.object({ path: z.string() }),
        execute: async ({ path }) => { executed.push(path); return { deleted: path } },
      }),
      shell: tool({
        inputSchema: z.object({ cmd: z.string() }),
        execute: async ({ cmd }) => { executed.push(cmd); return { ok: true } },
      }),
      readFile: tool({
        inputSchema: z.object({ path: z.string() }),
        execute: async ({ path }) => { executed.push(path); return { text: `contents of ${path}` } },
      }),
      progress: tool({
        inputSchema: z.object({ job: z.string() }),
        execute: async function* ({ job }) {
          executed.push(job)
          yield { job, step: 1 }
          executed.push((await gate.inspect(sessionId)).calls.find((c) => c.call_id === "call-1").status)
          yield { job, step: 2 }
        },
      }),
      count: tool({
        inputSchema: z.object({ n: z.number() }),
        execute: async ({ n }) => { executed.push(n); return n },
      }),
      schedule: tool({
        inputSchema: z.object({ when: z.string().transform((w) => new Date(w)) }),
        execute: async ({ when }) => { executed.push(when); return "scheduled" },
      }),
    },
  })
  const writ = build()
  const model = new MockLanguageModelV4({ doGenerate: turns })
  const messages = [{ role: "user", content: "Delete /tmp/a.txt" }]
  const run = (extra = {}) => generateText({ model, tools: writ.tools, toolApproval: writ.toolApproval, messages, ...extra })
  return { gate, sessionId, executed, writ, build, model, messages, run }
}

/** Asks, records the approval request, and returns its id. */
async function ask(s) {
  const first = await s.run()
  s.messages.push(...first.responseMessages)
  const req = first.content.find((p) => p.type === "tool-approval-request")
  assert.ok(req, "the SDK asks for approval")
  assert.deepEqual(s.executed, [])
  return req.approvalId
}

const respond = (s, approvalId, approved) =>
  s.messages.push({ role: "tool", content: [{ type: "tool-approval-response", approvalId, approved }] })

/** The output the SDK recorded for call-1 when it resumed: what the model reads next. */
const resumedOutput = (result) => {
  const part = result.responseMessages[0].content.find((c) => c.type === "tool-result" && c.toolCallId === "call-1")
  assert.ok(part, "the resumed run records an output for call-1")
  return part.output
}

const editHistory = (s, input) => {
  s.messages.find((m) => m.role === "assistant").content.find((c) => c.type === "tool-call").input = input
}

test("approval flow: the SDK asks, Writ approves, the tool runs once", async () => {
  const s = await setup([toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn])
  const approvalId = await ask(s)
  const [p] = s.writ.pending()
  assert.equal(p.toolCallId, "call-1")
  assert.deepEqual(p.input, { path: "/tmp/a.txt" })
  assert.equal((await s.writ.approve("call-1", "user")).verdict.verdict, "accepted")
  respond(s, approvalId, true)
  const second = await s.run()
  assert.deepEqual(s.executed, ["/tmp/a.txt"])
  assert.equal(second.text, "done")
  assert.equal((await s.gate.inspect(s.sessionId)).calls[0].status, "succeeded")
})

test("control: without Writ the SDK runs the edited input", async () => {
  const executed = []
  const tools = {
    deleteFile: tool({
      inputSchema: z.object({ path: z.string() }),
      execute: async ({ path }) => { executed.push(path); return { deleted: path } },
    }),
  }
  const model = new MockLanguageModelV4({ doGenerate: [toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn] })
  const messages = [{ role: "user", content: "Delete /tmp/a.txt" }]
  const toolApproval = { deleteFile: "user-approval" }
  const first = await generateText({ model, tools, toolApproval, messages })
  messages.push(...first.responseMessages)
  const req = first.content.find((p) => p.type === "tool-approval-request")
  assert.deepEqual(req.toolCall.input, { path: "/tmp/a.txt" })
  messages.push({ role: "tool", content: [{ type: "tool-approval-response", approvalId: req.approvalId, approved: true }] })
  messages.find((m) => m.role === "assistant").content.find((c) => c.type === "tool-call").input = { path: "/etc/passwd" }
  await generateText({ model, tools, toolApproval, messages })
  assert.deepEqual(executed, ["/etc/passwd"])
})

test("an edited tool-call input before resuming does not run (Loopjacking)", async () => {
  const s = await setup([toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn])
  const approvalId = await ask(s)
  await s.writ.approve("call-1", "user")
  respond(s, approvalId, true)
  editHistory(s, { path: "/etc/passwd" })
  // The SDK runs toolApproval again on resume; the re-proposal of call-1 with another digest is refused.
  const output = resumedOutput(await s.run())
  assert.equal(output.type, "execution-denied")
  assert.match(output.reason, /^writ: duplicate_call: /)
  assert.deepEqual(s.executed, [])
  assert.equal((await s.gate.inspect(s.sessionId)).calls[0].status, "authorized")
})

test("an edited input fails at dispatch with digest_mismatch when the resume drops toolApproval", async () => {
  const s = await setup([toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn])
  const approvalId = await ask(s)
  await s.writ.approve("call-1", "user")
  respond(s, approvalId, true)
  editHistory(s, { path: "/etc/passwd" })
  const output = resumedOutput(await s.run({ toolApproval: undefined }))
  assert.equal(output.type, "error-text")
  assert.match(output.value, /writ: digest_mismatch: /)
  assert.deepEqual(s.executed, [])
})

test("a replayed approved history runs the tool once", async () => {
  const s = await setup([toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn, textTurn, textTurn])
  const approvalId = await ask(s)
  await s.writ.approve("call-1", "user")
  respond(s, approvalId, true)
  const replay = structuredClone(s.messages)
  await s.run()
  assert.deepEqual(s.executed, ["/tmp/a.txt"])
  const again = resumedOutput(await s.run({ messages: structuredClone(replay) }))
  assert.deepEqual(again, { type: "execution-denied", reason: "writ: call already succeeded" })
  const dropped = resumedOutput(await s.run({ messages: structuredClone(replay), toolApproval: undefined }))
  assert.equal(dropped.type, "error-text")
  assert.match(dropped.value, /writ: call_ended: /)
  assert.deepEqual(s.executed, ["/tmp/a.txt"])
})

test("an SDK approval with no Writ approval runs nothing", async () => {
  const s = await setup([toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn])
  const approvalId = await ask(s)
  respond(s, approvalId, true)
  const output = resumedOutput(await s.run())
  assert.equal(output.type, "error-text")
  assert.match(output.value, /writ: call_awaiting: /)
  assert.deepEqual(s.executed, [])
  assert.equal((await s.gate.inspect(s.sessionId)).calls[0].status, "awaiting")
})

test("a tool the policy does not list is refused unknown_tool and does not run", async () => {
  const s = await setup([toolCallTurn("shell", { cmd: "rm -rf /" }), textTurn])
  const first = await s.run()
  const denied = first.content.find((p) => p.type === "tool-approval-response")
  assert.equal(denied.approved, false)
  assert.match(denied.reason, /^writ: unknown_tool: /)
  assert.deepEqual(s.executed, [])
  assert.deepEqual(s.writ.pending(), [])
})

test("a streaming tool's yields reach the SDK and the call succeeds only after the last", async () => {
  const s = await setup([toolCallTurn("progress", { job: "build" }), textTurn])
  const result = await s.run()
  const output = result.content.find((p) => p.type === "tool-result")
  assert.deepEqual(output.output, { job: "build", step: 2 })
  assert.deepEqual(s.executed, ["build", "dispatched"])
  assert.equal((await s.gate.inspect(s.sessionId)).calls[0].status, "succeeded")
})

test("streamText passes every yield of a streaming tool as a preliminary result", async () => {
  const s = await setup([])
  const model = new MockLanguageModelV4({
    doStream: async () => ({
      stream: simulateReadableStream({
        chunks: [
          { type: "tool-call", toolCallId: "call-1", toolName: "progress", input: JSON.stringify({ job: "build" }) },
          { type: "finish", finishReason: { unified: "tool-calls", raw: undefined }, usage },
        ],
      }),
    }),
  })
  const result = streamText({ model, tools: s.writ.tools, toolApproval: s.writ.toolApproval, messages: s.messages })
  const outputs = []
  for await (const part of result.fullStream) {
    if (part.type === "tool-result") outputs.push([part.preliminary === true, part.output])
  }
  assert.deepEqual(outputs, [
    [true, { job: "build", step: 1 }],
    [true, { job: "build", step: 2 }],
    [false, { job: "build", step: 2 }],
  ])
  assert.equal((await s.gate.inspect(s.sessionId)).calls[0].status, "succeeded")
})

test("an input that is not plain JSON is denied invalid_input and the turn goes on", async () => {
  const s = await setup([
    toolCallsTurn(["call-1", "count", '{"n":12345678901234567890}'], ["call-2", "schedule", { when: "2026-10-22T00:00:00Z" }]),
    textTurn,
  ])
  const first = await s.run()
  const denied = first.content.filter((p) => p.type === "tool-approval-response")
  assert.deepEqual(denied.map((p) => p.approved), [false, false])
  assert.match(denied[0].reason, /^writ: invalid_input: args\.n: /)
  assert.match(denied[1].reason, /^writ: invalid_input: args\.when: /)
  assert.deepEqual(s.executed, [])
  assert.deepEqual((await s.gate.inspect(s.sessionId)).calls, [])
})

test("two tool calls in one step each dispatch once", async () => {
  const s = await setup([toolCallsTurn(["call-1", "readFile", { path: "/a" }], ["call-2", "readFile", { path: "/b" }]), textTurn])
  const result = await s.run()
  assert.deepEqual(s.executed.toSorted(), ["/a", "/b"])
  assert.equal(result.content.filter((p) => p.type === "tool-result").length, 2)
  const calls = (await s.gate.inspect(s.sessionId)).calls
  assert.deepEqual(calls.map((c) => [c.call_id, c.status, c.attempts]).toSorted(), [["call-1", "succeeded", 1], ["call-2", "succeeded", 1]])
})

test("a server that rebuilds writTools per request approves with the input it showed", async () => {
  const s = await setup([toolCallTurn("deleteFile", { path: "/tmp/a.txt" }), textTurn])
  const first = await s.run()
  s.messages.push(...first.responseMessages)
  const req = first.content.find((p) => p.type === "tool-approval-request")
  // What the server stored in its own trusted store when it rendered the approval.
  const shown = { tool: req.toolCall.toolName, input: structuredClone(req.toolCall.input) }
  const approvalRequest = s.build()
  assert.deepEqual(approvalRequest.pending(), [])
  assert.equal((await approvalRequest.approve(req.toolCall.toolCallId, "user", shown)).verdict.verdict, "accepted")
  respond(s, req.approvalId, true)
  const resume = s.build()
  await generateText({ model: s.model, tools: resume.tools, toolApproval: resume.toolApproval, messages: s.messages })
  assert.deepEqual(s.executed, ["/tmp/a.txt"])
})
