import { randomUUID } from "node:crypto"
import { callDigest } from "./digest.js"
import { WritInputError } from "./errors.js"
import { createGate } from "./gate.js"
import type { Gate, GateResult } from "./gate.js"
import { loadKernel } from "./kernel.js"
import type { Kernel } from "./kernel.js"
import { MemoryStore } from "./store.js"
import type { Store } from "./store.js"
import type { RequestId } from "./types.js"

export type SimpleConsent = "none" | "per_call"
export type SimpleTools = Record<string, SimpleConsent>

export interface SimpleCall {
  callId: string
  tool: string
  callDigest: string
  status: "allowed" | "needs_approval" | "denied"
  reason?: string
  /** Opaque to callers; `JSON.parse` gives the gate's `RequestId`. */
  requestId?: string
}

export interface SimpleSession {
  id: string
  propose(tool: string, args: unknown): Promise<SimpleCall>
  approve(call: SimpleCall): Promise<SimpleCall>
  reject(call: SimpleCall): Promise<SimpleCall>
  run<T>(call: SimpleCall, fn: () => Promise<T>): Promise<{ ran: true; value: T } | { ran: false; reason: string }>
}

export interface SimpleGate {
  /** The layer-1 policy the gate runs. Take it, and `gate`, when you outgrow the simple path. */
  policyText: string
  gate: Gate
  session(sessionId?: string): Promise<SimpleSession>
}

export interface SimpleGateOptions {
  user: string
  tools: SimpleTools
  /** Defaults to 600_000. */
  approvalTtlMs?: number
  kernel?: Kernel
  /** Defaults to a new `MemoryStore`. */
  store?: Store
  clock?: () => number
}

const APPROVER = "user"

export function simplePolicy(tools: SimpleTools, opts: { approvalTtlMs?: number } = {}): string {
  if (tools === null || typeof tools !== "object" || Array.isArray(tools)) {
    throw new WritInputError("expected an object of tool names to consents", "tools")
  }
  const names = Object.keys(tools)
  if (names.length === 0) throw new WritInputError("expected at least one tool", "tools")
  const actions = Object.fromEntries(names.map((name) => {
    const consent = tools[name]
    if (consent !== "none" && consent !== "per_call") {
      throw new WritInputError('expected "none" or "per_call"', `tools.${name}`)
    }
    return [name, { consent }]
  }))
  const ttl = opts.approvalTtlMs ?? 600_000
  if (!Number.isSafeInteger(ttl) || ttl < 0) throw new WritInputError("expected a non-negative integer", "approvalTtlMs")
  return JSON.stringify({
    writ: "0.1",
    approver_roles: [APPROVER],
    limits: { approval_ttl_ms: ttl },
    actions,
  })
}

function statusOf(r: GateResult): SimpleCall["status"] {
  const v = r.verdict
  if (v.verdict === "rejected") return "denied"
  switch (v.decision) {
    case "allowed": case "allowed_by_grant": case "authorized": return "allowed"
    case "needs_approval": return "needs_approval"
    case "existing": return v.status === "authorized" ? "allowed" : v.status === "awaiting" ? "needs_approval" : "denied"
    case "pending": return "needs_approval"
    default: return "denied"
  }
}

// The simple API hands the request id around as an opaque string so callers can store or show it.
const encodeRequest = (r: RequestId): string => JSON.stringify(r)

function decodeRequest(call: SimpleCall): RequestId {
  if (call.requestId === undefined) throw new WritInputError("the call is not awaiting approval", "requestId")
  try {
    const r = JSON.parse(call.requestId) as RequestId
    if (typeof r.session === "string" && typeof r.call === "string" && Number.isInteger(r.generation)) return r
  } catch {}
  throw new WritInputError("expected a request id from propose", "requestId")
}

export async function simpleGate(opts: SimpleGateOptions): Promise<SimpleGate> {
  const policyText = simplePolicy(opts.tools, { approvalTtlMs: opts.approvalTtlMs })
  const gate = createGate({
    kernel: opts.kernel ?? await loadKernel(),
    policyText,
    store: opts.store ?? new MemoryStore(),
    ...(opts.clock === undefined ? {} : { clock: opts.clock }),
  })
  const user = opts.user

  async function session(sessionId: string = randomUUID()): Promise<SimpleSession> {
    const started = await gate.start({
      sessionId,
      requester: user,
      permissions: [],
      approvers: { [APPROVER]: { principal: user, kind: "human", roles: [APPROVER] } },
      userInitiated: true,
    })
    if (started.verdict.verdict === "rejected") {
      throw new WritInputError(`the session could not start: ${started.verdict.reason}`, "sessionId")
    }

    const settle = (call: SimpleCall, r: GateResult): SimpleCall => {
      const status = statusOf(r)
      const next: SimpleCall = { callId: call.callId, tool: call.tool, callDigest: call.callDigest, status }
      if (r.reason !== undefined) next.reason = r.reason
      if (status === "needs_approval" && call.requestId !== undefined) next.requestId = call.requestId
      return next
    }

    // A refused approve or reject is reported from where the call stands afterwards, which an expired
    // approval changes.
    const refused = async (call: SimpleCall, reason: string): Promise<SimpleCall> => {
      // The kernel refuses an answer after the TTL, but the stored call stays awaiting until an
      // approval_expire event ends it.
      if (reason === "approval_expired") await gate.approvalExpire(sessionId, { callId: call.callId, requestId: decodeRequest(call) })
      const view = (await gate.inspect(sessionId))?.calls.find((c) => c.call_id === call.callId)
      const next: SimpleCall = { callId: call.callId, tool: call.tool, callDigest: view?.digest ?? call.callDigest, status: "denied", reason }
      if (view?.status === "authorized") next.status = "allowed"
      if (view?.status === "awaiting") {
        next.status = "needs_approval"
        next.requestId = view.request_id === undefined ? call.requestId : encodeRequest(view.request_id)
      }
      return next
    }

    return {
      id: sessionId,

      async propose(tool, args) {
        const callId = randomUUID()
        const digest = await callDigest({ server: "local", tool, toolDigest: "unversioned", args })
        const r = await gate.propose(sessionId, { callId, tool, callDigest: digest })
        const call: SimpleCall = { callId, tool, callDigest: digest, status: statusOf(r) }
        if (r.reason !== undefined) call.reason = r.reason
        if (r.kind === "needs_approval") call.requestId = encodeRequest(r.requestId)
        return call
      },

      async approve(call) {
        const r = await gate.approve(sessionId, {
          callId: call.callId, requestId: decodeRequest(call), approverId: APPROVER, reviewedDigest: call.callDigest,
        })
        return r.verdict.verdict === "rejected" ? refused(call, r.verdict.reason) : settle(call, r)
      },

      async reject(call) {
        const r = await gate.reject(sessionId, { callId: call.callId, requestId: decodeRequest(call), approverId: APPROVER })
        if (r.verdict.verdict === "rejected") return refused(call, r.verdict.reason)
        // An accepted reject ends the call rejected; its verdict carries no decision or reason.
        return { callId: call.callId, tool: call.tool, callDigest: call.callDigest, status: "denied" }
      },

      async run(call, fn) {
        const d = await gate.dispatch(sessionId, { callId: call.callId, callDigest: call.callDigest })
        if (!d.claimed) return { ran: false, reason: d.reason ?? "not_claimed" }
        let value
        try {
          value = await fn()
        } catch (e) {
          // The tool's error is the one the caller needs. If this report fails too, the call stays
          // dispatched, and `gate.inspect` lists it for `outcomeUnknown` or `reconcile` later.
          await gate.outcomeUnknown(sessionId, call.callId).catch(() => {})
          throw e
        }
        await gate.result(sessionId, { callId: call.callId, outcome: "succeeded" })
        return { ran: true, value }
      },
    }
  }

  return { policyText, gate, session }
}
