import { canonicalize, parseStrict } from "./canonical.js"
import { clampUntrusted } from "./clamp.js"
import { sha256 } from "./digest.js"
import { WritConflictError, WritInputError, WritPolicyChangedError, WritStateFullError } from "./errors.js"
import { MAX_INPUT_BYTES } from "./kernel.js"
import type { Kernel } from "./kernel.js"
import type { LedgerRecord, Store, Stored } from "./store.js"
import type {
  Approver, CallStatus, Cost, Ledger, Outcome, Reason, RequestId, SessionView, Verdict, WritEvent,
} from "./types.js"

export interface GateOptions {
  kernel: Kernel
  policyText: string
  store: Store
  /** Integer milliseconds from a trusted clock. Defaults to `Date.now`. */
  clock?: () => number
  /**
   * `"principal"` (the default) shares one ledger between the live sessions of a principal.
   * `"none"` never reads or writes principal ledgers, so run one live session per principal.
   */
  ledgerScope?: "principal" | "none"
  /**
   * The byte budget of one session's stored state, in UTF-8 bytes. Growth events are refused once the
   * stored state is above seven eighths of it, so kill, end and reports still fit. Defaults to
   * `store.maxStateBytes`, else `MAX_INPUT_BYTES / 2`, and is never above `store.maxStateBytes`.
   */
  maxStateBytes?: number
  /**
   * Earlier policies whose sessions may still be live. A session started under one of them can only
   * be settled, ended and inspected (`end`, `kill`, `result`, `outcomeUnknown`, `reconcile`, `inspect`).
   */
  retiredPolicyTexts?: string[]
}

/**
 * `stateVersion` is the version of the stored state after the call. `reason` is a rejected verdict's
 * reason, else a `denied` or `dispatch_denied` decision's, else the one inside an `existing` denied status.
 */
export interface GateResult { verdict: Verdict; stateVersion: number; reason?: Reason }
export type ProposeResult = GateResult & (
  | { kind: "allowed" }
  | { kind: "needs_approval"; requestId: RequestId }
  /** `status` is the call's status when the verdict is an `existing` decision. */
  | { kind: "denied"; reason?: Reason; status?: CallStatus }
  | { kind: "rejected"; reason: Reason })
export type ProposeKind = ProposeResult["kind"]
/** `claimed` is true only for a `dispatch_claimed` decision: run the tool then, and only then. */
export interface DispatchResult extends GateResult { claimed: boolean }
/** `overrun` names the meters an accepted report committed above the reservation. */
export interface ReportResult extends GateResult { overrun: string[] }

export interface StartInput {
  sessionId: string
  requester: string
  permissions: string[]
  approvers: Record<string, Approver>
  /** When set, the first turn is started too and its result is returned. */
  userInitiated?: boolean
}
export interface ProposeInput {
  callId: string
  tool: string
  callDigest: string
  cost?: Cost
  guards?: Record<string, boolean>
  escalators?: Record<string, boolean>
}
export interface ApproveInput {
  callId: string
  requestId: RequestId
  approverId: string
  reviewedDigest: string
  reviewedCost?: Cost
  edit?: { newDigest: string; newCost?: Cost; escalators?: Record<string, boolean> }
}
export interface RejectInput { callId: string; requestId: RequestId; approverId: string }
export interface ApprovalExpireInput { callId: string; requestId: RequestId }
export interface GrantCreateInput {
  grantId: string
  approverId: string
  tool: string
  callDigest?: string
  scope: "turn" | "session"
  maxUses: number
  maxCost?: Cost
  notBefore?: number
  expiresAt?: number
  reviewedScopeDigest: string
}
export interface DispatchInput {
  callId: string
  /** Defaults to the stored call's attempts plus one, read once when the call begins. */
  attempt?: number
  callDigest: string
  cost?: Cost
  guards?: Record<string, boolean>
  /** Defaults to `defaultIdempotencyKey(principal, sessionId, callId)`, the same for every attempt. */
  idempotencyKey?: string
}
export interface ReportInput { callId: string; outcome: Outcome; actualCost?: string; noEffect?: boolean }
/** `untrusted` applies `clampUntrusted` with the call's current reservation. */
export interface ReportOptions { untrusted?: boolean; trustedDecline?: boolean }
export interface EscalationAckInput { approverId: string; escalation: number }
export interface PermissionAddInput { permission: string; approverId: string }
export interface ApproverAttestInput { approverId: string; principal: string; kind: "human" | "automated"; roles: string[] }
/** `ledgerVersion` is the version of the stored ledger after the call; `changed` is false when it already was so. */
export interface PrincipalKillResult { ledgerVersion: number; changed: boolean }

export interface Gate {
  start(input: StartInput): Promise<GateResult>
  turnStart(sessionId: string, userInitiated: boolean): Promise<GateResult>
  turnEnd(sessionId: string): Promise<GateResult>
  stepStart(sessionId: string): Promise<GateResult>
  propose(sessionId: string, input: ProposeInput): Promise<ProposeResult>
  approve(sessionId: string, input: ApproveInput): Promise<GateResult>
  reject(sessionId: string, input: RejectInput): Promise<GateResult>
  approvalExpire(sessionId: string, input: ApprovalExpireInput): Promise<GateResult>
  grantCreate(sessionId: string, input: GrantCreateInput): Promise<GateResult>
  grantRevoke(sessionId: string, grantId: string): Promise<GateResult>
  dispatch(sessionId: string, input: DispatchInput): Promise<DispatchResult>
  result(sessionId: string, input: ReportInput, opts?: ReportOptions): Promise<ReportResult>
  outcomeUnknown(sessionId: string, callId: string): Promise<GateResult>
  reconcile(sessionId: string, input: ReportInput, opts?: ReportOptions): Promise<ReportResult>
  cancel(sessionId: string, callId: string): Promise<GateResult>
  escalationAck(sessionId: string, input: EscalationAckInput): Promise<GateResult>
  permissionAdd(sessionId: string, input: PermissionAddInput): Promise<GateResult>
  permissionRevoke(sessionId: string, permission: string): Promise<GateResult>
  approverAttest(sessionId: string, input: ApproverAttestInput): Promise<GateResult>
  reset(sessionId: string): Promise<GateResult>
  kill(sessionId: string): Promise<GateResult>
  end(sessionId: string): Promise<GateResult>
  /** Sets the principal's tombstone in the stored ledger. Live sessions learn of it at their next commit. */
  killPrincipal(principal: string): Promise<PrincipalKillResult>
  /** Clears the principal's tombstone. Live sessions that saw it set are ended at their next commit. */
  clearPrincipalKill(principal: string): Promise<PrincipalKillResult>
  /**
   * The stored session as the kernel sees it at the gate's clock, or null when none is stored. Reads
   * only, and works under a retired policy too: after a crash, it lists the calls left to settle.
   */
  inspect(sessionId: string): Promise<SessionView | null>
}

export function proposeKind(v: Verdict): ProposeKind {
  if (v.verdict === "rejected") return "rejected"
  switch (v.decision) {
    // A repeated propose of an approved call answers `authorized`.
    case "allowed": case "allowed_by_grant": case "authorized": return "allowed"
    case "needs_approval": return "needs_approval"
    // A dispatched call cannot be dispatched again; it is recovered with outcomeUnknown or reconcile.
    case "existing": return v.status === "authorized" ? "allowed" : "denied"
    // Anything else, a finished call included, must not run now.
    default: return "denied"
  }
}

function reasonOf(v: Verdict): Reason | undefined {
  if (v.verdict === "rejected") return v.reason
  if (v.decision === "denied" || v.decision === "dispatch_denied") return v.reason
  if (v.decision === "existing" && typeof v.status === "object") return v.status.reason
  return undefined
}

function proposeResult(r: GateResult): ProposeResult {
  const v = r.verdict
  if (v.verdict === "rejected") return { ...r, kind: "rejected", reason: v.reason }
  if (v.decision === "needs_approval") return { ...r, kind: "needs_approval", requestId: v.request_id }
  if (proposeKind(v) === "allowed") return { ...r, kind: "allowed" }
  return v.decision === "existing" ? { ...r, kind: "denied", status: v.status } : { ...r, kind: "denied" }
}

/** The idempotency key spec section 6 derives from the principal, the session and the call: H(principal, session_id, call_id). */
export const defaultIdempotencyKey = (principal: string, sessionId: string, callId: string): Promise<string> =>
  sha256(canonicalize({ principal, session: sessionId, call: callId }))

type Envelope = "seq" | "time" | "state_version" | "origin" | "audit"
type Body = WritEvent extends infer E ? E extends WritEvent ? Omit<E, Envelope> : never : never

interface Current {
  /** The text of the policy the session runs under: the gate's, or a retired one. */
  policyText: string
  state: string
  stateVersion: number
  /** null while the session record does not exist. */
  expected: number | null
  principal: string
  lastSeq: number
  lastTime: number
  ledgerVersion: number
  policyDigest: string
  ended: boolean
  calls: Record<string, { cost?: Cost | null; attempts?: number } | undefined>
}

interface Plan {
  body: Body
  /** The ledger version the step read: the state's, or the one a session_start or ledger_sync brings in. */
  baseline: number
  expectedLedger: number | null
  writeLedger: boolean
  reloadOnLedgerConflict?: boolean
  /** The ledger text a session_start brings in, counted against the state budget. */
  incoming?: string
  clamp?: { trustedDecline: boolean; reservation: string | undefined }
}

type Mode =
  | { kind: "event" }
  | { kind: "sync" }
  | { kind: "end"; verdict: Verdict; expectedLedger: number | null }

const MAX_COMMITS = 5

const GROWTH = new Set<WritEvent["type"]>([
  "session_start", "propose", "approve", "grant_create", "approver_attest", "permission_add", "dispatch",
])

/** `"settle"` marks the methods a session under a retired policy still accepts. */
type Access = "live" | "settle"

const utf8 = new TextEncoder()
const bytesOf = (s: string): number => utf8.encode(s).length

const gateResult = (verdict: Verdict, stateVersion: number): GateResult => {
  const reason = reasonOf(verdict)
  return reason === undefined ? { verdict, stateVersion } : { verdict, stateVersion, reason }
}

const MAX_PRINCIPAL_BYTES = 512

function principalOf(p: unknown): string {
  if (typeof p !== "string" || p === "") throw new WritInputError("expected a non-empty string", "principal")
  const bytes = bytesOf(p)
  if (bytes > MAX_PRINCIPAL_BYTES) throw new WritInputError(`${bytes} UTF-8 bytes, over the limit of ${MAX_PRINCIPAL_BYTES}`, "principal")
  return p
}

function current(policyText: string, state: string, stateVersion: number, expected: number | null, principal: string): Current {
  // Read only. The gate never edits state.
  const s = JSON.parse(state) as {
    last_seq: number
    last_time: number
    policy_digest: string
    ended?: boolean
    ledger?: { version?: number }
    calls?: Current["calls"]
  }
  return {
    policyText, state, stateVersion, expected, principal,
    lastSeq: s.last_seq,
    lastTime: s.last_time,
    ledgerVersion: s.ledger?.version ?? 0,
    policyDigest: s.policy_digest,
    ended: s.ended === true,
    calls: s.calls ?? {},
  }
}

const parseLedger = (r: LedgerRecord | null): Ledger => (r === null ? {} : parseStrict(r.text) as Ledger)

function checked(kernel: Kernel, text: string, path: string): string {
  if (typeof text !== "string") throw new WritInputError("expected policy text", path)
  let r
  try {
    r = kernel.check(text)
  } catch (e) {
    if (e instanceof WritInputError) throw new WritInputError(e.message.replace(/^policyText: /, ""), path)
    throw e
  }
  const first = r.errors[0]
  if (first !== undefined) throw new WritInputError(`policy fails check: ${first.code}: ${first.message}`, path)
  return kernel.digest(text)
}

interface MeterIdentity { currency: string | undefined; window: unknown }

/** Kind, currency and `window_ms` of each principal-scope meter; read from a policy that passed `check`. */
function principalMeters(text: string): Map<string, MeterIdentity> {
  const meters = (parseStrict(text) as {
    meters?: Record<string, { scope?: unknown; currency?: string; window_ms?: unknown }>
  }).meters ?? {}
  const out = new Map<string, MeterIdentity>()
  for (const [name, m] of Object.entries(meters)) {
    if (m.scope === "principal") out.set(name, { currency: m.currency, window: m.window_ms })
  }
  return out
}

const kindText = (c: string | undefined) => (c === undefined ? "a calls meter" : `money in ${JSON.stringify(c)}`)
const windowText = (w: unknown) => (w === undefined ? "no window_ms" : `window_ms ${JSON.stringify(w)}`)

function identityMismatch(name: string, here: MeterIdentity, there: MeterIdentity, therePath: string): string | null {
  const kind = here.currency !== there.currency
  const window = here.window !== there.window
  if (!kind && !window) return null
  const what = kind && window
    ? `is ${kindText(here.currency)} with ${windowText(here.window)} here, ` +
      `but ${therePath} makes it ${kindText(there.currency)} with ${windowText(there.window)}`
    : kind
      ? `is ${kindText(here.currency)} here, but ${therePath} makes it ${kindText(there.currency)}`
      : `has ${windowText(here.window)} here, but ${therePath} gives it ${windowText(there.window)}`
  return `principal meter "${name}" ${what}; policies that share a principal ledger need the same kind, currency and window_ms ` +
    `for each shared principal meter, so rename the meter to change any of them`
}

export function createGate(opts: GateOptions): Gate {
  const { kernel, policyText, store } = opts
  const clock = opts.clock ?? Date.now
  const shared = (opts.ledgerScope ?? "principal") === "principal"
  // A budget above the store's would let the store refuse a kill or end before the headroom check runs.
  const maxStateBytes = opts.maxStateBytes !== undefined && store.maxStateBytes !== undefined
    ? Math.min(opts.maxStateBytes, store.maxStateBytes)
    : opts.maxStateBytes ?? store.maxStateBytes ?? MAX_INPUT_BYTES / 2
  if (!Number.isSafeInteger(maxStateBytes) || maxStateBytes <= 0) {
    throw new WritInputError(`expected a positive integer of bytes, got ${maxStateBytes}`, "maxStateBytes")
  }
  const headroom = Math.floor(maxStateBytes * 7 / 8)
  const policyDigest = checked(kernel, policyText, "policyText")
  const retired = new Map<string, string>()
  const seen: { path: string; meters: Map<string, MeterIdentity> }[] = [{ path: "policyText", meters: principalMeters(policyText) }]
  for (const [i, text] of (opts.retiredPolicyTexts ?? []).entries()) {
    const path = `retiredPolicyTexts[${i}]`
    const d = checked(kernel, text, path)
    const meters = principalMeters(text)
    // Ledger entries carry only a meter name and an amount, so a shared meter that changes kind or currency
    // sums unlike amounts; each session also prunes by its own policy's window, so a window mismatch lets
    // one policy drop entries the other still counts.
    for (const earlier of seen) {
      for (const [name, m] of meters) {
        const there = earlier.meters.get(name)
        const msg = there === undefined ? null : identityMismatch(name, m, there, earlier.path)
        if (msg !== null) throw new WritInputError(msg, path)
      }
    }
    seen.push({ path, meters })
    if (d !== policyDigest && !retired.has(d)) retired.set(d, text)
  }

  const now = (lastTime: number): number => {
    const t = clock()
    if (!Number.isSafeInteger(t)) throw new TypeError(`clock returned ${t}, expected integer milliseconds`)
    return Math.max(lastTime, t)
  }

  const load = async (sessionId: string, requester: string, access: Access): Promise<Current> => {
    const stored = await store.load(sessionId)
    if (stored === null) {
      const init = kernel.initial(policyText, policyDigest)
      return current(policyText, init.state, init.stateVersion, null, requester)
    }
    return resolve(sessionId, stored, access)
  }

  const resolve = (sessionId: string, stored: Stored, access: Access): Current => {
    const cur = current(policyText, stored.state, stored.stateVersion, stored.stateVersion, stored.principal)
    if (cur.policyDigest === policyDigest) return cur
    const text = retired.get(cur.policyDigest)
    if (text === undefined) {
      throw new WritPolicyChangedError(
        `session ${sessionId} runs under policy ${cur.policyDigest}, which this gate neither runs nor lists as retired`,
        sessionId, cur.policyDigest,
      )
    }
    if (access !== "settle") {
      throw new WritPolicyChangedError(
        `session ${sessionId} runs under the retired policy ${cur.policyDigest}: only end, kill, result, outcomeUnknown, reconcile and inspect`,
        sessionId, cur.policyDigest,
      )
    }
    return { ...cur, policyText: text }
  }

  const full = (sessionId: string, bytes: number, limit: number, what: string): WritStateFullError =>
    new WritStateFullError(
      `session ${sessionId}: ${what} is ${bytes} UTF-8 bytes, over the limit of ${limit} (budget ${maxStateBytes}); end the session and start a new one`,
      sessionId, bytes, limit,
    )

  const plan = (cur: Current, body: Body): Plan => ({
    body,
    baseline: cur.ledgerVersion,
    // Version 0 is the empty ledger, which is never stored.
    expectedLedger: shared && cur.ledgerVersion !== 0 ? cur.ledgerVersion : null,
    writeLedger: shared,
  })

  const brought = (body: Body, record: LedgerRecord | null): Plan => ({
    body,
    baseline: record?.version ?? 0,
    expectedLedger: record?.version ?? null,
    writeLedger: shared,
    incoming: record?.text,
  })

  /** `ended` is true when a forced `session_end` was committed in place of the step. */
  async function attempt(
    sessionId: string,
    make: (cur: Current) => Plan | Promise<Plan>,
    access: Access,
    requester: string,
  ): Promise<{ result: GateResult; ended: boolean }> {
    let cur = await load(sessionId, requester, access)
    let mode: Mode = { kind: "event" }
    let failed = 0
    for (;;) {
      let p: Plan
      if (mode.kind === "event") {
        p = await make(cur)
        if (GROWTH.has(p.body.type)) {
          const bytes = bytesOf(cur.state) + (p.body.type === "session_start" ? bytesOf(p.incoming ?? "") : 0)
          if (bytes > headroom) throw full(sessionId, bytes, headroom, `the stored state before ${p.body.type}`)
        }
      } else if (mode.kind === "sync") {
        const record = await store.loadLedger(cur.principal)
        p = brought({ type: "ledger_sync", ledger: parseLedger(record) }, record)
      } else {
        // The stored ledger moved on without this session; its state can only be ended.
        p = { body: { type: "session_end" }, baseline: cur.ledgerVersion, expectedLedger: mode.expectedLedger, writeLedger: false }
      }
      let event = { ...p.body, seq: cur.lastSeq + 1, time: now(cur.lastTime), state_version: cur.stateVersion } as WritEvent
      if (p.clamp !== undefined) event = clampUntrusted(event, p.clamp)
      const r = kernel.step(cur.policyText, cur.state, event)
      if (mode.kind === "sync" && r.verdict.verdict === "rejected" && r.verdict.reason === "ledger_conflict") {
        mode = { kind: "end", verdict: r.verdict, expectedLedger: p.expectedLedger }
        continue
      }
      const verdict = mode.kind === "end" ? mode.verdict : r.verdict
      const ended = mode.kind === "end"
      if (!r.changed) return { result: gateResult(verdict, r.stateVersion), ended: false }
      // `changed` alone is not trusted: only an accepted step is stored, including the forced session_end.
      if (r.verdict.verdict !== "accepted") return { result: gateResult(verdict, cur.stateVersion), ended: false }
      const bytes = bytesOf(r.state)
      if (bytes > maxStateBytes) throw full(sessionId, bytes, maxStateBytes, `the state after ${event.type}`)
      const outcome = await store.commit({
        sessionId,
        state: r.state,
        stateVersion: r.stateVersion,
        expectedStateVersion: cur.expected,
        principal: cur.principal,
        ledger: p.writeLedger && r.ledgerVersion !== p.baseline ? { text: r.ledger, version: r.ledgerVersion } : undefined,
        expectedLedgerVersion: p.expectedLedger,
      })
      if (outcome === "ok") {
        if (mode.kind !== "sync") return { result: gateResult(verdict, r.stateVersion), ended }
        cur = current(cur.policyText, r.state, r.stateVersion, r.stateVersion, cur.principal)
        mode = { kind: "event" }
        continue
      }
      if (outcome !== "state_conflict" && outcome !== "ledger_conflict") throw new Error(`store.commit returned ${String(outcome)}`)
      if (outcome === "ledger_conflict" && !shared) {
        throw new WritConflictError(`principal ${cur.principal} has a stored ledger, but this gate runs with ledgerScope "none"`)
      }
      if (++failed >= MAX_COMMITS) throw new WritConflictError(`session ${sessionId}: ${MAX_COMMITS} commits in a row conflicted`)
      if (outcome === "state_conflict" || p.reloadOnLedgerConflict === true) {
        cur = await load(sessionId, requester, access)
        mode = { kind: "event" }
      } else {
        mode = { kind: "sync" }
      }
    }
  }

  const run = async (
    sessionId: string,
    make: (cur: Current) => Plan | Promise<Plan>,
    access: Access = "live",
    requester = "",
  ): Promise<GateResult> => (await attempt(sessionId, make, access, requester)).result

  const step = (sessionId: string, body: Body | ((cur: Current) => Body | Promise<Body>), access: Access = "live") =>
    run(sessionId, async (cur) => plan(cur, typeof body === "function" ? await body(cur) : body), access)

  const report = (type: "result" | "reconcile") =>
    async (sessionId: string, input: ReportInput, ro: ReportOptions = {}): Promise<ReportResult> => {
      let sawEnded = false
      const send = (as: "result" | "reconcile") => attempt(sessionId, (cur) => {
        sawEnded = cur.ended
        return {
          ...plan(cur, { type: as, call_id: input.callId, outcome: input.outcome, actual_cost: input.actualCost, no_effect: input.noEffect }),
          clamp: ro.untrusted === true
            ? { trustedDecline: ro.trustedDecline === true, reservation: cur.calls[input.callId]?.cost?.amount }
            : undefined,
        }
      }, "settle", "")
      const first = await send(type)
      const fv = first.result.verdict
      const endedBefore = type === "result" && sawEnded && fv.verdict === "rejected" && fv.reason === "session_ended"
      // An ended session accepts only reconcile (spec section 6, Ended sessions), so the call still settles here.
      const r = first.ended || endedBefore ? (await send("reconcile")).result : first.result
      const v = r.verdict
      return { ...r, overrun: v.verdict === "accepted" && v.decision === "overrun" ? v.meters : [] }
    }

  const tombstone = (set: boolean) => async (input: string): Promise<PrincipalKillResult> => {
    const principal = principalOf(input)
    if (!shared) throw new WritInputError(`a gate with ledgerScope "none" keeps no principal ledgers`, "ledgerScope")
    for (let failed = 0; ;) {
      const record = await store.loadLedger(principal)
      const t = kernel.tombstone(record?.text ?? "", set)
      if (!t.changed) return { ledgerVersion: t.ledgerVersion, changed: false }
      const outcome = await store.commitLedger({
        principal, ledger: { text: t.ledger, version: t.ledgerVersion }, expectedLedgerVersion: record?.version ?? null,
      })
      if (outcome === "ok") return { ledgerVersion: t.ledgerVersion, changed: true }
      if (outcome !== "ledger_conflict") throw new Error(`store.commitLedger returned ${String(outcome)}`)
      if (++failed >= MAX_COMMITS) throw new WritConflictError(`principal ${principal}: ${MAX_COMMITS} ledger commits in a row conflicted`)
    }
  }

  const gate: Gate = {
    async start(input) {
      const r = await run(input.sessionId, async () => {
        const record = shared ? await store.loadLedger(input.requester) : null
        return {
          ...brought({
            type: "session_start",
            session_id: input.sessionId,
            policy_digest: policyDigest,
            requester: input.requester,
            permissions: input.permissions,
            approvers: input.approvers,
            ledger: parseLedger(record),
          }, record),
          // There is no session state to sync yet, so a moved ledger is simply read again.
          reloadOnLedgerConflict: true,
        }
      }, "live", input.requester)
      if (input.userInitiated === undefined || r.verdict.verdict !== "accepted") return r
      return gate.turnStart(input.sessionId, input.userInitiated)
    },
    turnStart: (sid, userInitiated) => step(sid, { type: "turn_start", user_initiated: userInitiated }),
    turnEnd: (sid) => step(sid, { type: "turn_end" }),
    stepStart: (sid) => step(sid, { type: "step_start" }),
    async propose(sid, i) {
      const r = await step(sid, {
        type: "propose", call_id: i.callId, tool: i.tool, call_digest: i.callDigest, cost: i.cost,
        guards: i.guards ?? {}, escalators: i.escalators ?? {},
      })
      return proposeResult(r)
    },
    approve: (sid, i) => step(sid, {
      type: "approve", call_id: i.callId, request_id: i.requestId, approver: i.approverId,
      reviewed_digest: i.reviewedDigest, reviewed_cost: i.reviewedCost,
      edit: i.edit === undefined ? undefined
        : { new_digest: i.edit.newDigest, new_cost: i.edit.newCost, escalators: i.edit.escalators ?? {} },
    }),
    reject: (sid, i) => step(sid, { type: "reject", call_id: i.callId, request_id: i.requestId, approver: i.approverId }),
    approvalExpire: (sid, i) => step(sid, { type: "approval_expire", call_id: i.callId, request_id: i.requestId }),
    grantCreate: (sid, i) => step(sid, {
      type: "grant_create", grant_id: i.grantId, approver: i.approverId, tool: i.tool, call_digest: i.callDigest,
      scope: i.scope, max_uses: i.maxUses, max_cost: i.maxCost, not_before: i.notBefore, expires_at: i.expiresAt,
      reviewed_scope_digest: i.reviewedScopeDigest,
    }),
    grantRevoke: (sid, grantId) => step(sid, { type: "grant_revoke", grant_id: grantId }),
    async dispatch(sid, i) {
      // Read once: recomputed after a lost commit, it would claim a retry another writer just allowed.
      let attempt = i.attempt
      const r = await step(sid, async (cur) => {
        attempt ??= (cur.calls[i.callId]?.attempts ?? 0) + 1
        return {
          type: "dispatch", call_id: i.callId, attempt, call_digest: i.callDigest, cost: i.cost,
          guards: i.guards ?? {}, idempotency_key: i.idempotencyKey ?? await defaultIdempotencyKey(cur.principal, sid, i.callId),
        }
      })
      const v = r.verdict
      return { ...r, claimed: v.verdict === "accepted" && v.decision === "dispatch_claimed" }
    },
    result: report("result"),
    outcomeUnknown: (sid, callId) => step(sid, { type: "outcome_unknown", call_id: callId }, "settle"),
    reconcile: report("reconcile"),
    cancel: (sid, callId) => step(sid, { type: "cancel", call_id: callId }),
    escalationAck: (sid, i) => step(sid, { type: "escalation_ack", approver: i.approverId, escalation: i.escalation }),
    permissionAdd: (sid, i) => step(sid, { type: "permission_add", permission: i.permission, approver: i.approverId }),
    permissionRevoke: (sid, permission) => step(sid, { type: "permission_revoke", permission }),
    approverAttest: (sid, i) => step(sid, {
      type: "approver_attest", approver: i.approverId, principal: i.principal, kind: i.kind, roles: i.roles,
    }),
    reset: (sid) => step(sid, { type: "reset" }),
    kill: (sid) => step(sid, { type: "kill" }, "settle"),
    end: (sid) => step(sid, { type: "session_end" }, "settle"),
    killPrincipal: tombstone(true),
    clearPrincipalKill: tombstone(false),
    async inspect(sid) {
      const stored = await store.load(sid)
      if (stored === null) return null
      const cur = resolve(sid, stored, "settle")
      return kernel.inspect(cur.policyText, cur.state, now(cur.lastTime))
    },
  }
  return gate
}
