// build.mjs rewrites this specifier to "./dist/src/index.js" in site/, where dist/ sits next to this file.
import { callDigest, loadKernel } from "../packages/writ/dist/src/index.js"

export { loadKernel }

export const SERVE_HINT = "Serve this page: run node playground/build.mjs && node playground/serve.mjs"

export const SAMPLE_POLICY = `{
  "writ": "0.1",
  "approver_roles": ["user"],
  "meters": {
    "spend": { "currency": "USD", "cap": 5000, "scope": "session" }
  },
  "limits": { "approval_ttl_ms": 600000 },
  "actions": {
    "web_search": { "consent": "none" },
    "send_email": { "consent": "per_call", "meters": ["spend"] }
  }
}
`

export const APPROVER = "user"

export async function bootKernel({ protocol = globalThis.location?.protocol, load = loadKernel } = {}) {
  if (protocol === "file:") return { ok: false, message: SERVE_HINT }
  try {
    return { ok: true, kernel: await load() }
  } catch (e) {
    return { ok: false, message: `${SERVE_HINT}. The kernel did not load: ${errorText(e)}` }
  }
}

export async function digestFor(tool, args) {
  return callDigest({ server: "playground", tool, toolDigest: "unversioned", args })
}

function errorText(e) {
  return e instanceof Error ? e.message : String(e)
}

function isObject(v) {
  return v !== null && typeof v === "object" && !Array.isArray(v)
}

/** JSON values compared structurally, key order ignored, as `writ replay` compares `expect`. */
function sameJson(a, b) {
  if (a === b) return true
  if (Array.isArray(a)) return Array.isArray(b) && a.length === b.length && a.every((x, i) => sameJson(x, b[i]))
  if (!isObject(a) || !isObject(b)) return false
  const ka = Object.keys(a)
  return ka.length === Object.keys(b).length && ka.every((k) => Object.hasOwn(b, k) && sameJson(a[k], b[k]))
}

// state_version is compared too when expect lists it: scenarios step events as written, so it must reproduce.
export function matchesExpect(verdict, expect) {
  if (verdict === null) return false
  return Object.keys(expect ?? {}).every((k) => sameJson(verdict[k], expect[k]))
}

function names(text) {
  if (Array.isArray(text)) return text
  return String(text ?? "").split(",").map((s) => s.trim()).filter((s) => s !== "")
}

function flags(text) {
  return Object.fromEntries(names(text).map((n) => [n, true]))
}

function parseArgs(text) {
  if (typeof text !== "string") return { ok: true, value: text ?? {} }
  if (text.trim() === "") return { ok: true, value: {} }
  try {
    return { ok: true, value: JSON.parse(text) }
  } catch (e) {
    return { ok: false, error: { code: "invalid_arguments", message: `arguments: ${errorText(e)}` } }
  }
}

function cost(amount, currency) {
  const a = String(amount ?? "").trim()
  return a === "" ? undefined : { amount: a, currency: String(currency ?? "").trim() || "USD" }
}

/**
 * Checks the policy and, when it has no errors, returns a session that steps the kernel.
 * A policy the kernel cannot decode comes back as one `invalid_policy` error.
 */
export function createPlayground(kernel, policyText) {
  let report
  try {
    report = kernel.check(policyText)
  } catch (e) {
    return { ok: false, errors: [{ code: "invalid_policy", message: errorText(e) }], warnings: [] }
  }
  if (!report.ok) return { ok: false, errors: report.errors, warnings: report.warnings }
  return { ok: true, session: makeSession(kernel, policyText, report), warnings: report.warnings }
}

function makeSession(kernel, policyText, report) {
  let state = kernel.initial(policyText).state
  let stateVersion = 0
  let lastSeq = 0
  let lastTime = null
  let view = kernel.inspect(policyText, state, 0)
  const history = []
  const proposals = new Map()

  const failure = (code, message, event = null) => ({ ok: false, error: { code, message }, event, verdict: null, view })

  function apply(body) {
    if (typeof body === "string") {
      try {
        body = JSON.parse(body)
      } catch (e) {
        return failure("invalid_json", `event: ${errorText(e)}`)
      }
    }
    if (!isObject(body)) return failure("invalid_event", "an event is a JSON object")
    const event = {
      ...body,
      seq: body.seq ?? lastSeq + 1,
      time: body.time ?? (lastTime === null ? 0 : lastTime + 1000),
      state_version: body.state_version ?? stateVersion,
    }
    if (event.type === "session_start" && event.policy_digest === undefined) event.policy_digest = report.policy_digest
    let r
    try {
      r = kernel.step(policyText, state, event)
    } catch (e) {
      return failure("invalid_event", errorText(e), event)
    }
    if (r.verdict.verdict === "accepted") {
      state = r.state
      stateVersion = r.stateVersion
      lastSeq = event.seq
      lastTime = event.time
      view = kernel.inspect(policyText, state, lastTime)
      // A repeat of a known call answers existing and must not replace the guards the call was proposed with.
      if (event.type === "propose" && r.verdict.decision !== "existing") proposals.set(event.call_id, { guards: event.guards })
    }
    history.push({ event, verdict: r.verdict })
    return { ok: true, event, verdict: r.verdict, view }
  }

  const callOf = (callId) => view.calls.find((c) => c.call_id === callId)
  const requestOf = (callId) => {
    const call = callOf(callId)
    return call?.request_id ?? { session: view.session_id, call: callId, generation: call?.generation ?? 0 }
  }

  /** Builds an event from a form's fields; the kernel, not this code, decides whether it is acceptable. */
  async function build(type, form = {}) {
    const callId = form.callId
    switch (type) {
      case "session_start":
        return {
          type, session_id: form.sessionId || "s1", requester: form.requester || "visitor",
          permissions: names(form.permissions),
          approvers: { [APPROVER]: { principal: APPROVER, kind: "human", roles: [APPROVER] } }, ledger: {},
        }
      case "turn_start":
        return { type, user_initiated: form.userInitiated ?? true }
      case "turn_end": case "step_start": case "session_end": case "kill":
        return { type }
      case "propose": {
        const args = parseArgs(form.args)
        if (!args.ok) return args
        const guards = flags(form.guards)
        return {
          type, call_id: callId, tool: form.tool, call_digest: await digestFor(form.tool, args.value),
          cost: cost(form.costAmount, form.costCurrency), guards, escalators: flags(form.escalators),
        }
      }
      case "approve": {
        const call = callOf(callId)
        return {
          type, call_id: callId, request_id: requestOf(callId), approver: APPROVER,
          reviewed_digest: call?.digest ?? "", reviewed_cost: call?.cost ?? undefined,
        }
      }
      case "reject":
        return { type, call_id: callId, request_id: requestOf(callId), approver: APPROVER }
      case "dispatch": {
        const call = callOf(callId)
        let digest = call?.digest ?? ""
        if (typeof form.args === "string" && form.args.trim() !== "") {
          const args = parseArgs(form.args)
          if (!args.ok) return args
          digest = await digestFor(call?.tool ?? "", args.value)
        }
        return {
          type, call_id: callId, attempt: (call?.attempts ?? 0) + 1, call_digest: digest, cost: call?.cost ?? undefined,
          guards: proposals.get(callId)?.guards ?? {}, idempotency_key: `${view.session_id}/${callId}`,
        }
      }
      case "result": case "reconcile": {
        const actual = String(form.actualCost ?? "").trim()
        return { type, call_id: callId, outcome: form.outcome || "succeeded", actual_cost: actual || undefined }
      }
      case "outcome_unknown": case "cancel":
        return { type, call_id: callId }
      default:
        return { ok: false, error: { code: "invalid_event", message: `no form for event type ${type}` } }
    }
  }

  async function send(type, form) {
    let body
    try {
      body = await build(type, form)
    } catch (e) {
      return failure("invalid_arguments", errorText(e))
    }
    if (body.ok === false) return failure(body.error.code, body.error.message)
    for (const k of Object.keys(body)) if (body[k] === undefined) delete body[k]
    return apply(body)
  }

  return {
    policyText,
    policyDigest: report.policy_digest,
    apply,
    send,
    nextCallId() {
      const used = new Set(history.map((h) => h.event.call_id))
      let n = 1
      while (used.has(`c${n}`)) n++
      return `c${n}`
    },
    get view() { return view },
    get history() { return history.slice() },
  }
}

export function parseScenarios(jsonlText) {
  return jsonlText.split("\n").filter((l) => l.trim() !== "").map((line) => {
    const t = JSON.parse(line)
    return { id: t.id, description: t.description ?? "", policy: t.policy, policyDigest: t.policy_digest, events: t.events }
  })
}

/**
 * Steps a trace's events as written, so deliberately stale events reproduce. As in `writ replay`, a
 * `session_start` without `policy_digest` gets the trace's digest.
 */
export function scenarioPlayer(kernel, scenario) {
  const policyText = JSON.stringify(scenario.policy)
  const digest = scenario.policyDigest ?? kernel.digest(policyText)
  let state = kernel.initial(policyText).state
  let lastTime = 0
  let view = kernel.inspect(policyText, state, 0)
  const rows = []
  return {
    policyText,
    rows,
    get done() { return rows.length >= scenario.events.length },
    get view() { return view },
    next() {
      const step = scenario.events[rows.length]
      if (step === undefined) return null
      const event = { ...step.event }
      if (event.type === "session_start" && event.policy_digest === undefined) event.policy_digest = digest
      const expect = step.expect ?? null
      let verdict = null
      let error = null
      try {
        const r = kernel.step(policyText, state, event)
        verdict = r.verdict
        if (verdict.verdict === "accepted") {
          state = r.state
          lastTime = event.time
          view = kernel.inspect(policyText, state, lastTime)
        }
      } catch (e) {
        error = { code: "invalid_event", message: errorText(e) }
      }
      const row = { event, verdict, expect, matches: matchesExpect(verdict, expect), ...(error && { error }) }
      rows.push(row)
      return row
    },
  }
}

export function playScenario(kernel, scenario) {
  const player = scenarioPlayer(kernel, scenario)
  while (!player.done) player.next()
  return player.rows
}

export function actionNames(policyText) {
  try {
    const actions = JSON.parse(policyText).actions
    return isObject(actions) ? Object.keys(actions) : []
  } catch {
    return []
  }
}

export function verdictLine(verdict) {
  if (verdict === null || verdict === undefined) return "no verdict"
  const parts = [verdict.verdict, verdict.decision, verdict.reason, verdict.status?.status ?? verdict.status]
  return parts.filter((p) => typeof p === "string").join(" ")
}

export function eventLine(event) {
  if (!isObject(event)) return "?"
  return [`#${event.seq}`, event.type, event.call_id, event.tool, event.outcome].filter((p) => p !== undefined).join(" ")
}
