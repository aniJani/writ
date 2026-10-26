import { callDigest } from "./digest.js"
import { WritInputError } from "./errors.js"
import type { Gate, GateResult } from "./gate.js"
import type { Cost, RequestId } from "./types.js"

/** The parts of an AI SDK tool this module reads. Typed structurally so the package never imports `ai`. */
export interface AiTool {
  // `any` so tools built with the SDK's `tool()`, whose execute takes a typed input, are assignable.
  execute?: (input: any, options: any) => unknown
  needsApproval?: unknown
  [key: string]: unknown
}

export type AiApprovalStatus =
  | "not-applicable" | "denied" | "user-approval"
  | { type: "denied" | "user-approval"; reason?: string }

export interface WritToolsOptions<TOOLS extends Record<string, AiTool> = Record<string, AiTool>> {
  gate: Gate
  sessionId: string
  tools: TOOLS
  /** The `server` of every call digest. Defaults to `"ai-sdk"`. */
  server?: string
  /** Each tool's `toolDigest`. Defaults to `"unversioned"`. */
  toolDigests?: Record<string, string>
  /** The cost a tool's call reserves, from its input. */
  cost?: Record<string, (input: unknown) => Cost | undefined>
}

export interface PendingApproval {
  toolCallId: string
  tool: string
  /** The input the approver must be shown: the call's digest is over exactly this. */
  input: unknown
  callDigest: string
  requestId: RequestId
  cost?: Cost
}

export interface WritTools<TOOLS extends Record<string, AiTool> = Record<string, AiTool>> {
  /** The same tools, each `execute` run only after a claimed `gate.dispatch`. */
  tools: TOOLS
  /** Pass as `toolApproval` to `generateText`, `streamText` or `ToolLoopAgent`. */
  toolApproval: (options: { toolCall: { toolCallId: string; toolName: string; input: unknown } }) => Promise<AiApprovalStatus>
  /** Process-local and not durable: an instance lists only the calls its own `toolApproval` saw. */
  pending(): PendingApproval[]
  /**
   * `shown` is the call the approver reviewed. It is required when this instance has no pending entry for
   * the call (another instance or request saw it), and when given, the reviewed digest is computed from it.
   */
  approve(toolCallId: string, approverId: string, shown?: ShownCall): Promise<GateResult>
  reject(toolCallId: string, approverId: string): Promise<GateResult>
}

export interface ShownCall { tool: string; input: unknown }

const isAsyncIterable = (v: unknown): v is AsyncIterable<unknown> =>
  v !== null && typeof v === "object" && typeof (v as { [Symbol.asyncIterator]?: unknown })[Symbol.asyncIterator] === "function"

const isAsyncGeneratorFunction = (f: unknown): boolean =>
  Object.prototype.toString.call(f) === "[object AsyncGeneratorFunction]"

const own = <T>(record: Record<string, T> | undefined, key: string): T | undefined =>
  record !== undefined && Object.hasOwn(record, key) ? record[key] : undefined

/** The text the model reads for a refusal: `writ: <reason>: <model message>`. */
function refusal(r: GateResult & { status?: unknown }): string {
  const code = r.reason ?? (typeof r.status === "string" ? `call already ${r.status}` : "denied")
  const message = r.verdict.message
  return message === undefined ? `writ: ${code}` : `writ: ${code}: ${message}`
}

export function writTools<TOOLS extends Record<string, AiTool>>(options: WritToolsOptions<TOOLS>): WritTools<TOOLS> {
  const { gate, sessionId } = options
  const server = options.server ?? "ai-sdk"
  if (options.tools === null || typeof options.tools !== "object" || Array.isArray(options.tools)) {
    throw new WritInputError("expected an object of tools", "tools")
  }
  for (const [name, t] of Object.entries(options.tools)) {
    // Approval belongs to the gate: an SDK-level needsApproval would be a second, weaker gate.
    if (t?.needsApproval !== undefined) throw new WritInputError("remove needsApproval; the Writ policy decides approval", `tools.${name}`)
    // A tool the SDK cannot execute locally would never pass through dispatch.
    if (typeof t?.execute !== "function") throw new WritInputError("expected an execute function", `tools.${name}`)
  }
  // Checked here so a host misconfiguration throws to the host instead of reaching the model as invalid_input.
  const record = (value: unknown, path: string): [string, unknown][] => {
    if (value === undefined) return []
    if (value === null || typeof value !== "object" || Array.isArray(value)) throw new WritInputError("expected an object keyed by tool name", path)
    return Object.entries(value)
  }
  for (const [name, d] of record(options.toolDigests, "toolDigests")) {
    if (typeof d !== "string" || d === "") throw new WritInputError("expected a non-empty string", `toolDigests.${name}`)
  }
  for (const [name, f] of record(options.cost, "cost")) {
    if (typeof f !== "function") throw new WritInputError("expected a function from the input to a cost", `cost.${name}`)
  }

  const pendingCalls = new Map<string, PendingApproval>()

  const describe = async (tool: string, input: unknown): Promise<{ digest: string; cost?: Cost }> => {
    const cost = own(options.cost, tool)?.(input)
    const toolDigest = own(options.toolDigests, tool) ?? "unversioned"
    const digest = await callDigest({ server, tool, toolDigest, args: input, ...(cost === undefined ? {} : { cost }) })
    return cost === undefined ? { digest } : { digest, cost }
  }

  const toolApproval: WritTools<TOOLS>["toolApproval"] = async ({ toolCall }) => {
    const { toolCallId, toolName, input } = toolCall
    let described
    try {
      described = await describe(toolName, input)
    } catch (e) {
      if (e instanceof WritInputError) return { type: "denied", reason: `writ: invalid_input: ${e.message}` }
      throw e
    }
    const { digest, cost } = described
    const r = await gate.propose(sessionId, { callId: toolCallId, tool: toolName, callDigest: digest, ...(cost === undefined ? {} : { cost }) })
    if (r.kind === "needs_approval") {
      const p: PendingApproval = { toolCallId, tool: toolName, input, callDigest: digest, requestId: r.requestId }
      if (cost !== undefined) p.cost = cost
      pendingCalls.set(toolCallId, p)
      return { type: "user-approval", reason: "writ: needs_approval" }
    }
    // A rejected verdict changed nothing, so a call that was awaiting still is.
    if (r.kind !== "rejected") pendingCalls.delete(toolCallId)
    // Never "approved": the SDK's auto-approval would run the call without a Writ approval record.
    return r.kind === "allowed" ? "not-applicable" : { type: "denied", reason: refusal(r) }
  }

  /** The request to answer: this instance's pending entry, else the stored call's. */
  const request = async (toolCallId: string, needShown: boolean): Promise<{ requestId: RequestId; cost?: Cost; digest?: string }> => {
    const p = pendingCalls.get(toolCallId)
    if (p !== undefined) return { requestId: p.requestId, digest: p.callDigest, ...(p.cost === undefined ? {} : { cost: p.cost }) }
    if (needShown) throw new WritInputError("no pending entry in this instance; pass the call the approver was shown", "toolCallId")
    const view = (await gate.inspect(sessionId))?.calls.find((c) => c.call_id === toolCallId)
    if (view?.request_id === undefined) throw new WritInputError("no call awaiting approval has this id", "toolCallId")
    return view.cost === null ? { requestId: view.request_id } : { requestId: view.request_id, cost: view.cost }
  }

  // A quorum leaves a call awaiting after one answer, and a refused answer may leave it awaiting too,
  // so pending() follows the stored call rather than the answer.
  const settle = async (toolCallId: string, requestId: RequestId, r: GateResult): Promise<GateResult> => {
    if (r.verdict.verdict === "rejected" && r.verdict.reason === "approval_expired") {
      // The kernel refuses an answer after the TTL, but the call stays awaiting until approval_expire ends it.
      await gate.approvalExpire(sessionId, { callId: toolCallId, requestId })
    }
    const p = pendingCalls.get(toolCallId)
    if (p === undefined) return r
    const view = (await gate.inspect(sessionId))?.calls.find((c) => c.call_id === toolCallId)
    if (view?.status === "awaiting") {
      if (view.request_id !== undefined) p.requestId = view.request_id
    } else {
      pendingCalls.delete(toolCallId)
    }
    return r
  }

  /** Dispatches the call; returns its id once the gate claims it, and throws without claiming otherwise. */
  const claim = async (name: string, input: unknown, execOptions: { toolCallId?: unknown } | undefined): Promise<string> => {
    const callId = execOptions?.toolCallId
    if (typeof callId !== "string") throw new WritInputError("expected the SDK's toolCallId", "options.toolCallId")
    let described
    try {
      described = await describe(name, input)
    } catch (e) {
      if (e instanceof WritInputError) throw new Error(`writ: invalid_input: ${e.message}`)
      throw e
    }
    const { digest, cost } = described
    const d = await gate.dispatch(sessionId, { callId, callDigest: digest, ...(cost === undefined ? {} : { cost }) })
    if (!d.claimed) throw new Error(refusal(d))
    return callId
  }

  // The tool's error is the one the model needs. If this report fails too, the call stays
  // dispatched, and `gate.inspect` lists it for `outcomeUnknown` or `reconcile` later.
  const unknown = (callId: string) => gate.outcomeUnknown(sessionId, callId).catch(() => {})

  type Execute = NonNullable<AiTool["execute"]>

  const wrap = (name: string, original: Execute): Execute => {
    // The SDK streams an execute only when the value it returns is itself an AsyncIterable, so a wrapper
    // that must await dispatch first can keep streaming only for an async generator function.
    if (isAsyncGeneratorFunction(original)) {
      return async function* (input: unknown, execOptions: { toolCallId?: unknown } | undefined) {
        const callId = await claim(name, input, execOptions)
        let finished = false
        try {
          yield* original(input, execOptions) as AsyncIterable<unknown>
          finished = true
        } finally {
          // A throw, or a consumer that stops early, leaves the effect unknown.
          if (!finished) await unknown(callId)
        }
        await gate.result(sessionId, { callId, outcome: "succeeded" })
      }
    }
    return async (input: unknown, execOptions: { toolCallId?: unknown } | undefined) => {
      const callId = await claim(name, input, execOptions)
      let value
      try {
        value = await original(input, execOptions)
        // Too late to stream it: drain it here and return the last item, which the SDK would make the output.
        if (isAsyncIterable(value)) {
          let last
          for await (const item of value) last = item
          value = last
        }
      } catch (e) {
        await unknown(callId)
        throw e
      }
      await gate.result(sessionId, { callId, outcome: "succeeded" })
      return value
    }
  }

  // Descriptors, not spread: the SDK keeps some tool properties non-enumerable (experimental_toolCaller).
  const tools = Object.fromEntries(Object.entries(options.tools).map(([name, t]) => [name, Object.create(Object.getPrototypeOf(t), {
    ...Object.getOwnPropertyDescriptors(t),
    execute: { value: wrap(name, t.execute as Execute), enumerable: true, writable: true, configurable: true },
  })])) as TOOLS

  return {
    tools,
    toolApproval,
    pending: () => [...pendingCalls.values()].map((p) => ({ ...p })),
    async approve(toolCallId, approverId, shown) {
      const req = await request(toolCallId, shown === undefined)
      // A digest that differs from the call's is left to the kernel, which refuses it digest_mismatch.
      const reviewedDigest = shown === undefined ? req.digest as string : (await describe(shown.tool, shown.input)).digest
      const r = await gate.approve(sessionId, {
        callId: toolCallId, requestId: req.requestId, approverId, reviewedDigest,
        ...(req.cost === undefined ? {} : { reviewedCost: req.cost }),
      })
      return settle(toolCallId, req.requestId, r)
    },
    async reject(toolCallId, approverId) {
      const req = await request(toolCallId, false)
      return settle(toolCallId, req.requestId, await gate.reject(sessionId, { callId: toolCallId, requestId: req.requestId, approverId }))
    },
  }
}
