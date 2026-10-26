import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"
import { test } from "node:test"
import { fixture, repoRoot } from "./helpers.js"
import {
  createGate, defaultIdempotencyKey, loadKernel, WritConflictError, WritInputError, WritPolicyChangedError, WritStateFullError,
} from "../src/index.js"
import type { Commit, Gate, GateOptions, Kernel, LedgerCommit, Store, Verdict, WritEvent } from "../src/index.js"

export const kernel = await loadKernel()

interface Deferred { promise: Promise<void>; resolve(): void }
function deferred(): Deferred {
  let resolve!: () => void
  const promise = new Promise<void>((r) => { resolve = r })
  return { promise, resolve }
}

/** Counts commits and can hold the next one until released, to force an interleaving. */
class Probe implements Store {
  commits = 0
  private held: { entered: Deferred; release: Deferred } | null = null
  constructor(readonly inner: Store) {}
  get maxStateBytes() { return this.inner.maxStateBytes }
  load(id: string) { return this.inner.load(id) }
  loadLedger(p: string) { return this.inner.loadLedger(p) }
  commitLedger(c: LedgerCommit) { return this.inner.commitLedger(c) }
  async commit(c: Commit) {
    this.commits++
    const h = this.held
    if (h !== null) {
      this.held = null
      h.entered.resolve()
      await h.release.promise
    }
    return this.inner.commit(c)
  }
  /** The next commit waits; `entered` resolves once it has been reached. */
  holdNext(): { entered: Promise<void>; release(): void } {
    const h = { entered: deferred(), release: deferred() }
    this.held = h
    return { entered: h.entered.promise, release: h.release.resolve }
  }
}

/** Reports a ledger conflict before a state conflict, an order `Store` allows. */
export function ledgerFirst(inner: Store): Store {
  return {
    load: (id) => inner.load(id),
    loadLedger: (p) => inner.loadLedger(p),
    commitLedger: (c) => inner.commitLedger(c),
    async commit(c) {
      if (((await inner.loadLedger(c.principal))?.version ?? null) !== c.expectedLedgerVersion) return "ledger_conflict"
      return inner.commit(c)
    },
  }
}

const state = async (store: Store, id: string) => JSON.parse((await store.load(id))!.state) as Record<string, any>
const utf8Bytes = (s: string) => new TextEncoder().encode(s).length

const webChatTrace = JSON.parse(readFileSync(join(repoRoot, "corpus/examples/web-chat.jsonl"), "utf8").split("\n")[0]!) as {
  policy: unknown
  events: { event: WritEvent; expect: Record<string, unknown> }[]
}

const openPolicy = JSON.stringify({
  writ: "0.1",
  approver_roles: ["owner"],
  limits: { approval_ttl_ms: 600000 },
  actions: {
    search: { consent: "none" },
    buy: { consent: "per_call", grantable: { scope: "session", max_uses: 5 } },
  },
})

export const callsPolicy = JSON.stringify({
  writ: "0.1",
  meters: { calls: { unit: "calls", cap: 1, scope: "principal", window_ms: 86400000 } },
  actions: { ping: { meters: ["calls"] } },
})

const spendPolicy = JSON.stringify({
  writ: "0.1",
  meters: { spend: { currency: "USD", cap: 5000, scope: "principal", window_ms: 86400000 } },
  actions: { buy: { meters: ["spend"] } },
})

const pingsPolicy = JSON.stringify({
  writ: "0.1",
  meters: { calls: { unit: "calls", cap: 10, scope: "principal", window_ms: 86400000 } },
  actions: { ping: { meters: ["calls"] } },
})

const lifetimePolicy = JSON.stringify({
  writ: "0.1",
  meters: { calls: { unit: "calls", cap: 1, scope: "principal" } },
  actions: { ping: { consent: "none", meters: ["calls"] } },
})

const retryPolicy = JSON.stringify({
  writ: "0.1",
  actions: { ping: { consent: "none", idempotent: true, retry_after_unknown: true, max_attempts: 3 } },
})

/** A store that reports a byte limit of its own. */
const limited = (inner: Store, maxStateBytes: number): Store => ({
  maxStateBytes,
  load: (id) => inner.load(id),
  loadLedger: (p) => inner.loadLedger(p),
  commit: (c) => inner.commit(c),
  commitLedger: (c) => inner.commitLedger(c),
})

const owner = { owner: { principal: "u2", kind: "human" as const, roles: ["owner"] } }

function gateFor(policyText: string, store: Store, over: Partial<GateOptions> = {}): Gate {
  let t = 1000
  return createGate({ kernel, policyText, store, clock: () => (t += 10), ...over })
}

async function opened(gate: Gate, sessionId: string, requester = "u1"): Promise<void> {
  const r = await gate.start({ sessionId, requester, permissions: [], approvers: owner, userInitiated: true })
  assert.equal(r.verdict.verdict, "accepted")
  assert.equal(r.stateVersion, 2)
}

async function viaGate(gate: Gate, e: WritEvent) {
  const sid = "s1"
  switch (e.type) {
    case "session_start":
      return gate.start({ sessionId: e.session_id, requester: e.requester, permissions: e.permissions, approvers: e.approvers })
    case "turn_start": return gate.turnStart(sid, e.user_initiated)
    case "turn_end": return gate.turnEnd(sid)
    case "step_start": return gate.stepStart(sid)
    case "propose":
      return gate.propose(sid, { callId: e.call_id, tool: e.tool, callDigest: e.call_digest, cost: e.cost, guards: e.guards, escalators: e.escalators })
    case "approve":
      return gate.approve(sid, { callId: e.call_id, requestId: e.request_id, approverId: e.approver, reviewedDigest: e.reviewed_digest, reviewedCost: e.reviewed_cost })
    case "dispatch":
      return gate.dispatch(sid, { callId: e.call_id, attempt: e.attempt, callDigest: e.call_digest, cost: e.cost, guards: e.guards, idempotencyKey: e.idempotency_key })
    case "result":
      return gate.result(sid, { callId: e.call_id, outcome: e.outcome, actualCost: e.actual_cost, noEffect: e.no_effect })
    default: throw new Error(`no gate method in this test for ${e.type}`)
  }
}

export function gateSuite(label: string, make: () => Store | Promise<Store>): void {
  const t = (name: string, fn: () => Promise<void>) => test(`${label}: ${name}`, fn)
  t("a full lifecycle gives the web-chat trace's verdicts", async () => {
    const store = await make()
    let now = 0
    const gate = createGate({ kernel, policyText: JSON.stringify(webChatTrace.policy), store, clock: () => now })
    for (const [i, { event: e, expect }] of webChatTrace.events.entries()) {
      now = e.time
      const r = await viaGate(gate, e)
      for (const [k, v] of Object.entries(expect)) assert.deepEqual((r.verdict as Record<string, unknown>)[k], v, `step ${i} ${k}`)
      assert.equal(r.stateVersion, i + 1)
    }
    const s = await state(store, "s1")
    assert.equal(s["last_seq"], webChatTrace.events.length)
    assert.equal(s["calls"]["c3"]["status"], "succeeded")
  })

  t("a clock that goes back still gives an accepted event at the last time", async () => {
    const store = await make()
    const times = [5000, 4000, 4000]
    const gate = createGate({ kernel, policyText: openPolicy, store, clock: () => times.shift()! })
    await gate.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: owner })
    const r = await gate.turnStart("s1", true)
    assert.equal(r.verdict.verdict, "accepted")
    assert.equal((await state(store, "s1"))["last_time"], 5000)
    assert.equal((await gate.stepStart("s1")).verdict.verdict, "accepted")
    assert.equal((await state(store, "s1"))["last_time"], 5000)
  })

  t("the default clock is integer milliseconds and a fractional clock is refused", async () => {
    const store = await make()
    const before = Date.now()
    await createGate({ kernel, policyText: openPolicy, store }).start({ sessionId: "s1", requester: "u1", permissions: [], approvers: owner })
    const t = (await state(store, "s1"))["last_time"] as number
    assert.ok(Number.isInteger(t) && t >= before && t <= Date.now())
    const bad = createGate({ kernel, policyText: openPolicy, store: await make(), clock: () => 1.5 })
    await assert.rejects(bad.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: owner }), TypeError)
  })

  t("a rejected event leaves the store byte-identical and does not commit", async () => {
    const probe = new Probe(await make())
    const gate = gateFor(openPolicy, probe)
    await opened(gate, "s1")
    const before = await probe.load("s1")
    const commits = probe.commits
    const r = await gate.dispatch("s1", { callId: "nope", attempt: 1, callDigest: "d", idempotencyKey: "k" })
    assert.equal(r.verdict.verdict, "rejected")
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "unknown_call")
    assert.equal(r.stateVersion, 2)
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s1"), before)
    assert.equal(await probe.loadLedger("u1"), null)
  })

  t("an event on a session that was never started is rejected without a commit", async () => {
    const probe = new Probe(await make())
    const r = await gateFor(openPolicy, probe).turnStart("missing", true)
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "not_started")
    assert.equal(probe.commits, 0)
    assert.equal(await probe.load("missing"), null)
  })

  t("a second start of a session is rejected and changes nothing", async () => {
    const probe = new Probe(await make())
    const gate = gateFor(openPolicy, probe)
    await opened(gate, "s1")
    const before = await probe.load("s1")
    const commits = probe.commits
    const r = await gate.start({ sessionId: "s1", requester: "u9", permissions: [], approvers: {} })
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "already_started")
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s1"), before)
  })

  t("a kernel input error leaves the store untouched", async () => {
    const probe = new Probe(await make())
    assert.throws(() => gateFor(fixture("policies/errors.json"), probe),
      (e: unknown) => e instanceof WritInputError && e.path === "policyText")
    assert.throws(() => gateFor("{", probe), (e: unknown) => e instanceof WritInputError && e.path === "policyText")
    assert.equal(probe.commits, 0)

    const gate = gateFor(spendPolicy, probe)
    await opened(gate, "s2")
    const before = await probe.load("s2")
    const commits = probe.commits
    const r = gate.propose("s2", { callId: "c1", tool: "buy", callDigest: "d", cost: { amount: "1.5", currency: "USD" } })
    await assert.rejects(r, (e: unknown) => e instanceof WritInputError && e.path === "event")
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s2"), before)
  })

  t("a WebAssembly trap surfaces as an error without a commit", async () => {
    const probe = new Probe(await make())
    await opened(gateFor(openPolicy, probe), "s1")
    const before = await probe.load("s1")
    const commits = probe.commits
    const trap = new Error("RuntimeError: unreachable")
    const trapping: Kernel = { ...kernel, step: () => { throw trap } }
    const gate = createGate({ kernel: trapping, policyText: openPolicy, store: probe })
    await assert.rejects(gate.stepStart("s1"), (e) => e === trap)
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s1"), before)
  })

  t("a session is never stepped under a different policy", async () => {
    const probe = new Probe(await make())
    await opened(gateFor(openPolicy, probe), "s1")
    const before = await probe.load("s1")
    const commits = probe.commits
    const other = gateFor(spendPolicy, probe)
    const changed = (e: unknown) =>
      e instanceof WritPolicyChangedError && e.sessionId === "s1" && e.policyDigest === kernel.digest(openPolicy)
    await assert.rejects(other.stepStart("s1"), changed)
    await assert.rejects(other.end("s1"), changed)
    await assert.rejects(other.kill("s1"), changed)
    await assert.rejects(other.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: {} }), changed)
    await assert.rejects(other.inspect("s1"), changed)
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s1"), before)
  })

  t("start puts the stored principal ledger and the policy digest in session_start", async () => {
    const store = await make()
    const gate = gateFor(callsPolicy, store)
    await opened(gate, "s1")
    await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    await gate.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: "k1" })
    const ledger = await store.loadLedger("u1")
    assert.ok(ledger !== null && ledger.version > 0)
    await opened(gate, "s2")
    const s2 = await state(store, "s2")
    assert.equal(JSON.stringify(s2["ledger"]), ledger.text)
    assert.equal(s2["policy_digest"], kernel.digest(callsPolicy))
    assert.equal(s2["requester"], "u1")
    const r = await gate.propose("s2", { callId: "c1", tool: "ping", callDigest: "d" })
    assert.equal(r.kind, "denied")
    assert.equal(r.verdict.verdict === "accepted" && r.verdict.decision === "denied" && r.verdict.reason, "meter_exceeded")
  })

  t("two gates proposing on one session both land, one after the other", async () => {
    const probe = new Probe(await make())
    const a = gateFor(openPolicy, probe)
    const b = gateFor(openPolicy, probe)
    await opened(a, "s1")
    const v0 = (await probe.load("s1"))!.stateVersion
    const hold = probe.holdNext()
    const pa = a.propose("s1", { callId: "ca", tool: "search", callDigest: "da" })
    await hold.entered
    const rb = await b.propose("s1", { callId: "cb", tool: "search", callDigest: "db" })
    hold.release()
    const ra = await pa
    assert.equal(rb.kind, "allowed")
    assert.equal(ra.kind, "allowed")
    assert.equal(rb.stateVersion, v0 + 1)
    assert.equal(ra.stateVersion, v0 + 2)
    const s = await state(probe, "s1")
    assert.deepEqual(Object.keys(s["calls"]).sort(), ["ca", "cb"])
    assert.equal(s["state_version"], v0 + 2)
    assert.equal((await probe.load("s1"))!.stateVersion, v0 + 2)
    // B's commit, A's lost commit, A's retried commit.
    assert.equal(probe.commits, 2 + 3)
  })

  t("two gates racing to dispatch one call claim it once", async () => {
    const probe = new Probe(await make())
    const a = gateFor(openPolicy, probe)
    const b = gateFor(openPolicy, probe)
    await opened(a, "s1")
    await a.propose("s1", { callId: "c1", tool: "search", callDigest: "d1" })
    const dispatch = { callId: "c1", attempt: 1, callDigest: "d1", idempotencyKey: "k-s1-c1" }
    const hold = probe.holdNext()
    const pa = a.dispatch("s1", dispatch)
    await hold.entered
    const rb = await b.dispatch("s1", dispatch)
    hold.release()
    const ra = await pa
    const claimed = (v: Verdict) => v.verdict === "accepted" && v.decision === "dispatch_claimed"
    assert.equal(claimed(rb.verdict), true)
    assert.equal(claimed(ra.verdict), false)
    const lost = ra.verdict
    assert.ok(
      lost.verdict === "rejected" || (lost.decision === "existing" && lost.status === "dispatched"),
      JSON.stringify(lost),
    )
    const s = await state(probe, "s1")
    assert.equal(s["calls"]["c1"]["attempts"], 1)
    assert.equal(s["calls"]["c1"]["status"], "dispatched")
  })

  t("two sessions of one principal share a calls meter of 1: one claim, then meter_exceeded after ledger_sync", async () => {
    const probe = new Probe(await make())
    const g1 = gateFor(callsPolicy, probe)
    const g2 = gateFor(callsPolicy, probe)
    await opened(g1, "s1")
    await opened(g2, "s2")
    assert.equal((await g1.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
    assert.equal((await g2.propose("s2", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
    const d = (sid: string) => ({ callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: `k-${sid}-c1` })
    const hold = probe.holdNext()
    const p1 = g1.dispatch("s1", d("s1"))
    await hold.entered
    const r2 = await g2.dispatch("s2", d("s2"))
    hold.release()
    const r1 = await p1
    assert.equal(r2.verdict.verdict === "accepted" && r2.verdict.decision, "dispatch_claimed")
    assert.equal(r1.verdict.verdict === "rejected" && r1.verdict.reason, "meter_exceeded")
    const ledger = (await probe.loadLedger("u1"))!
    const s1 = await state(probe, "s1")
    assert.equal(s1["ledger"]["version"], ledger.version)
    assert.equal(JSON.stringify(s1["ledger"]), ledger.text)
    assert.equal(s1["calls"]["c1"]["status"], "authorized")
    const claims = JSON.parse(ledger.text).entries as { session: string }[]
    assert.deepEqual(claims.map((e) => e.session), ["s2"])
  })

  t("a ledger that can no longer be reconciled ends the session", async () => {
    const store = await make()
    const gate = gateFor(callsPolicy, store)
    await opened(gate, "s1")
    await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    await gate.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: "k" })
    const stored = (await store.loadLedger("u1"))!
    // An out-of-band clear: a newer ledger without this session's entry.
    const cleared = { text: `{"version":${stored.version + 5}}`, version: stored.version + 5 }
    assert.equal(await store.commit({
      sessionId: "admin", state: "{}", stateVersion: 1, expectedStateVersion: null,
      principal: "u1", ledger: cleared, expectedLedgerVersion: stored.version,
    }), "ok")
    const r = await gate.result("s1", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "ledger_conflict")
    const s = await state(store, "s1")
    assert.equal(s["ended"], true)
    assert.equal(r.stateVersion, s["state_version"])
    assert.deepEqual(await store.loadLedger("u1"), cleared)
  })

  t("with ledgerScope none the gate never reads or writes principal ledgers", async () => {
    const inner = await make()
    let ledgerReads = 0
    const store: Store = {
      load: (id) => inner.load(id),
      loadLedger: (p) => { ledgerReads++; return inner.loadLedger(p) },
      commitLedger: () => { throw new Error("commitLedger under ledgerScope none") },
      commit: (c) => {
        assert.equal(c.ledger, undefined)
        assert.equal(c.expectedLedgerVersion, null)
        return inner.commit(c)
      },
    }
    const gate = gateFor(callsPolicy, store, { ledgerScope: "none" })
    for (const sid of ["s1", "s2"]) {
      await opened(gate, sid)
      await gate.propose(sid, { callId: "c1", tool: "ping", callDigest: "d" })
      const r = await gate.dispatch(sid, { callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: "k" })
      assert.equal(r.verdict.verdict === "accepted" && r.verdict.decision, "dispatch_claimed")
    }
    assert.equal(ledgerReads, 0)
    assert.equal(await inner.loadLedger("u1"), null)
  })

  t("with ledgerScope none a stored principal ledger fails closed", async () => {
    const store = await make()
    const full = gateFor(callsPolicy, store)
    await opened(full, "s1")
    await full.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    await full.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: "k" })
    const none = gateFor(callsPolicy, store, { ledgerScope: "none" })
    await assert.rejects(none.start({ sessionId: "s2", requester: "u1", permissions: [], approvers: {} }), WritConflictError)
    assert.equal(await store.load("s2"), null)
  })

  t("a store that always conflicts gives WritConflictError after 5 attempts", async () => {
    const inner = await make()
    await opened(gateFor(openPolicy, inner), "s1")
    let commits = 0
    const store: Store = {
      load: (id) => inner.load(id), loadLedger: (p) => inner.loadLedger(p), commitLedger: (c) => inner.commitLedger(c),
      commit: async () => { commits++; return "state_conflict" },
    }
    await assert.rejects(gateFor(openPolicy, store).stepStart("s1"), WritConflictError)
    assert.equal(commits, 5)
  })

  t("store errors propagate unchanged", async () => {
    const inner = await make()
    await opened(gateFor(openPolicy, inner), "s1")
    const boom = new Error("store down")
    const failing: Store = {
      load: (id) => inner.load(id), loadLedger: (p) => inner.loadLedger(p), commitLedger: async () => { throw boom },
      commit: async () => { throw boom },
    }
    await assert.rejects(gateFor(openPolicy, failing).stepStart("s1"), (e) => e === boom)
    const loadFails: Store = { ...failing, load: async () => { throw boom } }
    await assert.rejects(gateFor(openPolicy, loadFails).stepStart("s1"), (e) => e === boom)
    await assert.rejects(gateFor(openPolicy, failing).killPrincipal("u1"), (e) => e === boom)
  })

  t("an untrusted declined report is recorded as failed", async () => {
    const store = await make()
    const gate = gateFor(openPolicy, store)
    await opened(gate, "s1")
    for (const [id, trustedDecline, want] of [["c1", false, "failed"], ["c2", true, "declined"]] as const) {
      await gate.propose("s1", { callId: id, tool: "search", callDigest: id })
      await gate.dispatch("s1", { callId: id, attempt: 1, callDigest: id, idempotencyKey: `k-${id}` })
      const r = await gate.result("s1", { callId: id, outcome: "declined" }, { untrusted: true, trustedDecline })
      assert.equal(r.verdict.verdict, "accepted")
      assert.equal((await state(store, "s1"))["calls"][id]["status"], want)
    }
  })

  t("an untrusted report commits at least the reservation and never releases", async () => {
    const store = await make()
    const gate = gateFor(spendPolicy, store)
    await opened(gate, "s1")
    const cost = { amount: "1200", currency: "USD" }
    for (const id of ["c1", "c2"]) {
      await gate.propose("s1", { callId: id, tool: "buy", callDigest: id, cost })
      await gate.dispatch("s1", { callId: id, attempt: 1, callDigest: id, cost, idempotencyKey: `k-${id}` })
    }
    await gate.result("s1", { callId: "c1", outcome: "succeeded", actualCost: "100", noEffect: true }, { untrusted: true })
    await gate.result("s1", { callId: "c2", outcome: "succeeded", actualCost: "100", noEffect: true })
    const entries = JSON.parse((await store.loadLedger("u1"))!.text).entries as { call: string; amount: string; committed: boolean }[]
    assert.deepEqual(entries.map((e) => [e.call, e.amount, e.committed]), [["c1", "1200", true]])
  })

  t("propose kind maps each decision", async () => {
    const store = await make()
    const gate = gateFor(openPolicy, store)
    await opened(gate, "s1")
    const p = (callId: string, tool: string, callDigest = callId) => gate.propose("s1", { callId, tool, callDigest })
    assert.equal((await p("c1", "search")).kind, "allowed")
    const needs = await p("c2", "buy")
    assert.equal(needs.kind, "needs_approval")
    const waiting = await p("c2", "buy")
    assert.equal(waiting.kind, "needs_approval")
    assert.deepEqual(waiting.kind === "needs_approval" && waiting.requestId, needs.kind === "needs_approval" && needs.requestId)
    assert.equal((await p("c3", "wire_money")).kind, "denied")
    assert.equal((await p("c3", "wire_money")).kind, "denied")
    assert.equal((await p("c1", "buy")).kind, "rejected")
    const g = await gate.grantCreate("s1", { grantId: "g1", approverId: "owner", tool: "buy", callDigest: "dg", scope: "session", maxUses: 1, reviewedScopeDigest: "rs" })
    assert.equal(g.verdict.verdict, "accepted")
    const byGrant = await p("c4", "buy", "dg")
    assert.equal(byGrant.verdict.verdict === "accepted" && byGrant.verdict.decision, "allowed_by_grant")
    assert.equal(byGrant.kind, "allowed")
    await gate.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "c1", idempotencyKey: "k1" })
    const inFlight = await p("c1", "search")
    assert.equal(inFlight.verdict.verdict === "accepted" && inFlight.verdict.decision === "existing" && inFlight.verdict.status, "dispatched")
    assert.equal(inFlight.kind, "denied")
    await gate.result("s1", { callId: "c1", outcome: "succeeded" })
    assert.equal((await p("c1", "search")).kind, "denied")
    const rid = needs.verdict.verdict === "accepted" && needs.verdict.decision === "needs_approval" ? needs.verdict.request_id : undefined
    assert.ok(rid)
    await gate.approve("s1", { callId: "c2", requestId: rid, approverId: "owner", reviewedDigest: "c2" })
    const again = await p("c2", "buy")
    assert.equal(again.verdict.verdict === "accepted" && again.verdict.decision, "authorized")
    assert.equal(again.kind, "allowed")
  })

  t("the other gate methods build accepted events", async () => {
    const store = await make()
    const gate = gateFor(openPolicy, store)
    await gate.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: owner })
    const ok = async (r: Promise<{ verdict: Verdict }>) => assert.equal((await r).verdict.verdict, "accepted", JSON.stringify((await r).verdict))
    await ok(gate.turnStart("s1", true))
    await ok(gate.stepStart("s1"))
    await ok(gate.approverAttest("s1", { approverId: "bot", principal: "svc", kind: "automated", roles: ["owner"] }))
    await ok(gate.permissionAdd("s1", { permission: "p.x", approverId: "owner" }))
    await ok(gate.permissionRevoke("s1", "p.x"))
    await ok(gate.grantCreate("s1", { grantId: "g1", approverId: "owner", tool: "buy", callDigest: "dg", scope: "session", maxUses: 1, reviewedScopeDigest: "rs" }))
    await ok(gate.grantRevoke("s1", "g1"))
    const n = await gate.propose("s1", { callId: "c1", tool: "buy", callDigest: "d1" })
    const rid = n.verdict.verdict === "accepted" && n.verdict.decision === "needs_approval" ? n.verdict.request_id : undefined
    assert.ok(rid)
    await ok(gate.reject("s1", { callId: "c1", requestId: rid, approverId: "owner" }))
    const m = await gate.propose("s1", { callId: "c2", tool: "buy", callDigest: "d2" })
    const rid2 = m.verdict.verdict === "accepted" && m.verdict.decision === "needs_approval" ? m.verdict.request_id : undefined
    assert.ok(rid2)
    await ok(gate.approvalExpire("s1", { callId: "c2", requestId: rid2 }))
    await gate.propose("s1", { callId: "c3", tool: "search", callDigest: "d3" })
    await ok(gate.cancel("s1", "c3"))
    await gate.propose("s1", { callId: "c4", tool: "search", callDigest: "d4" })
    await gate.dispatch("s1", { callId: "c4", attempt: 1, callDigest: "d4", idempotencyKey: "k4" })
    await ok(gate.outcomeUnknown("s1", "c4"))
    await ok(gate.reconcile("s1", { callId: "c4", outcome: "succeeded" }))
    await ok(gate.turnEnd("s1"))
    await ok(gate.reset("s1"))
    await ok(gate.kill("s1"))
    await ok(gate.end("s1"))
    const s = await state(store, "s1")
    assert.equal(s["ended"], true)
    assert.equal(s["killed"], true)
    assert.equal(s["calls"]["c4"]["status"], "unknown")
  })

  t("escalation_ack goes through the gate", async () => {
    const policy = JSON.stringify({
      writ: "0.1", approver_roles: ["owner"], escalation_roles: ["owner"],
      limits: { max_consecutive_failures: 1 }, actions: { search: {} },
    })
    const store = await make()
    const gate = gateFor(policy, store)
    await opened(gate, "s1")
    await gate.propose("s1", { callId: "c1", tool: "search", callDigest: "d" })
    await gate.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: "k" })
    await gate.result("s1", { callId: "c1", outcome: "failed" })
    const s = await state(store, "s1")
    assert.ok(s["escalations"] > 0)
    const r = await gate.escalationAck("s1", { approverId: "owner", escalation: s["escalations"] })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    assert.equal((await state(store, "s1"))["escalated"], false)
  })

  t("a store that reports ledger_conflict before state_conflict still gives one claim and a live session", async () => {
    const probe = new Probe(ledgerFirst(await make()))
    const a = gateFor(callsPolicy, probe)
    const b = gateFor(callsPolicy, probe)
    await opened(a, "s1")
    await a.propose("s1", { callId: "c1", tool: "ping", callDigest: "d1" })
    const dispatch = { callId: "c1", attempt: 1, callDigest: "d1", idempotencyKey: "k-s1-c1" }
    const hold = probe.holdNext()
    const pa = a.dispatch("s1", dispatch)
    await hold.entered
    const rb = await b.dispatch("s1", dispatch)
    hold.release()
    const ra = await pa
    assert.equal(rb.verdict.verdict === "accepted" && rb.verdict.decision, "dispatch_claimed")
    const lost = ra.verdict
    assert.ok(
      lost.verdict === "rejected" || (lost.decision === "existing" && lost.status === "dispatched"),
      JSON.stringify(lost),
    )
    const s = await state(probe, "s1")
    assert.notEqual(s["ended"], true)
    assert.equal(s["calls"]["c1"]["status"], "dispatched")
    assert.equal(s["calls"]["c1"]["attempts"], 1)
    const entries = JSON.parse((await probe.loadLedger("u1"))!.text).entries as { call: string }[]
    assert.deepEqual(entries.map((e) => e.call), ["c1"])
  })

  t("killPrincipal stops a sibling session's dispatch", async () => {
    const store = await make()
    const gate = gateFor(pingsPolicy, store)
    await opened(gate, "A")
    await opened(gate, "B")
    assert.equal((await gate.propose("B", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
    assert.equal((await state(store, "B"))["calls"]["c1"]["status"], "authorized")
    assert.deepEqual(await gate.killPrincipal("u1"), { ledgerVersion: 1, changed: true })
    const d = await gate.dispatch("B", { callId: "c1", attempt: 1, callDigest: "d" })
    assert.equal(d.verdict.verdict === "rejected" && d.verdict.reason, "killed", JSON.stringify(d.verdict))
    const b = await state(store, "B")
    assert.equal(b["calls"]["c1"]["status"], "cancelled")
    assert.equal(b["ledger"]["tombstone"], true)
    const p = await gate.propose("A", { callId: "c1", tool: "ping", callDigest: "d" })
    assert.equal(p.verdict.verdict === "accepted" && p.verdict.decision === "denied" && p.verdict.reason, "killed")
    assert.equal(JSON.parse((await store.loadLedger("u1"))!.text).entries, undefined)
    assert.deepEqual(await gate.killPrincipal("u1"), { ledgerVersion: 1, changed: false })
  })

  t("killPrincipal on a principal without a ledger", async () => {
    const store = await make()
    const gate = gateFor(callsPolicy, store)
    assert.deepEqual(await gate.clearPrincipalKill("u9"), { ledgerVersion: 0, changed: false })
    assert.equal(await store.loadLedger("u9"), null)
    assert.deepEqual(await gate.killPrincipal("u9"), { ledgerVersion: 1, changed: true })
    const rec = await store.loadLedger("u9")
    assert.equal(rec?.version, 1)
    assert.equal(JSON.parse(rec.text).tombstone, true)
    await gate.start({ sessionId: "s1", requester: "u9", permissions: [], approvers: {}, userInitiated: true })
    const p = await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    assert.equal(p.verdict.verdict === "accepted" && p.verdict.decision === "denied" && p.verdict.reason, "killed")
  })

  t("killPrincipal and clearPrincipalKill refuse ledgerScope none and give up after 5 conflicts", async () => {
    const inner = await make()
    const none = gateFor(callsPolicy, inner, { ledgerScope: "none" })
    await assert.rejects(none.killPrincipal("u1"), WritInputError)
    await assert.rejects(none.clearPrincipalKill("u1"), WritInputError)
    assert.equal(await inner.loadLedger("u1"), null)
    let tries = 0
    const losing: Store = {
      load: (id) => inner.load(id), loadLedger: (p) => inner.loadLedger(p), commit: (c) => inner.commit(c),
      commitLedger: async () => { tries++; return "ledger_conflict" },
    }
    await assert.rejects(gateFor(callsPolicy, losing).killPrincipal("u1"), WritConflictError)
    assert.equal(tries, 5)
    assert.equal(await inner.loadLedger("u1"), null)
  })

  t("killPrincipal retries against a ledger that moved", async () => {
    const probe = new Probe(await make())
    const gate = gateFor(callsPolicy, probe)
    await opened(gate, "s1")
    await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    const outcomes: string[] = []
    const racing: Store = {
      load: (id) => probe.load(id), loadLedger: (p) => probe.loadLedger(p), commit: (c) => probe.commit(c),
      async commitLedger(c) {
        if (outcomes.length === 0) await gate.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d" })
        const out = await probe.commitLedger(c)
        outcomes.push(out)
        return out
      },
    }
    const r = await gateFor(callsPolicy, racing).killPrincipal("u1")
    assert.deepEqual(outcomes, ["ledger_conflict", "ok"])
    const stored = (await probe.loadLedger("u1"))!
    assert.deepEqual(r, { ledgerVersion: stored.version, changed: true })
    const ledger = JSON.parse(stored.text)
    assert.equal(ledger.tombstone, true)
    assert.deepEqual(ledger.entries.map((e: { call: string }) => e.call), ["c1"])
  })

  t("clearPrincipalKill ends live sessions", async () => {
    const store = await make()
    const gate = gateFor(pingsPolicy, store)
    await opened(gate, "A")
    await gate.killPrincipal("u1")
    const p = await gate.propose("A", { callId: "c1", tool: "ping", callDigest: "d" })
    assert.equal(p.verdict.verdict === "accepted" && p.verdict.decision === "denied" && p.verdict.reason, "killed")
    assert.deepEqual(await gate.clearPrincipalKill("u1"), { ledgerVersion: 2, changed: true })
    const r = await gate.propose("A", { callId: "c2", tool: "ping", callDigest: "d" })
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "ledger_conflict", JSON.stringify(r.verdict))
    assert.equal((await state(store, "A"))["ended"], true)
    await opened(gate, "B")
    assert.equal((await gate.propose("B", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
    assert.deepEqual(await gate.clearPrincipalKill("u1"), { ledgerVersion: 2, changed: false })
  })

  t("after clearPrincipalKill an ended session still settles its Unknown call", async () => {
    const store = await make()
    const gate = gateFor(lifetimePolicy, store)
    await opened(gate, "A")
    assert.equal((await gate.propose("A", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
    assert.equal((await gate.dispatch("A", { callId: "c1", callDigest: "d" })).claimed, true)
    await gate.killPrincipal("u1")
    assert.equal((await gate.outcomeUnknown("A", "c1")).verdict.verdict, "accepted")
    await gate.clearPrincipalKill("u1")
    const r = await gate.reconcile("A", { callId: "c1", outcome: "succeeded", noEffect: true })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    const a = await state(store, "A")
    assert.equal(a["ended"], true)
    assert.equal(a["calls"]["c1"]["reconciled"], "succeeded")
    const ledger = JSON.parse((await store.loadLedger("u1"))!.text)
    assert.equal(ledger.tombstone, undefined)
    assert.equal(ledger.entries, undefined)
    await opened(gate, "B")
    assert.equal((await gate.propose("B", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
  })

  /** Session A has `c1` claimed and sees the principal killed, then the kill is cleared. */
  const killedAndCleared = async (policyText: string, cost?: { amount: string; currency: string }) => {
    const store = await make()
    const gate = gateFor(policyText, store)
    await opened(gate, "A")
    const tool = cost === undefined ? "ping" : "buy"
    assert.equal((await gate.propose("A", { callId: "c1", tool, callDigest: "d", cost })).kind, "allowed")
    assert.equal((await gate.dispatch("A", { callId: "c1", callDigest: "d", cost })).claimed, true)
    await gate.killPrincipal("u1")
    const p = await gate.propose("A", { callId: "c2", tool, callDigest: "d", cost })
    assert.equal(p.kind === "denied" && p.reason, "killed", JSON.stringify(p.verdict))
    await gate.clearPrincipalKill("u1")
    return { store, gate }
  }

  t("after clearPrincipalKill a live session's result settles in one call", async () => {
    const { store, gate } = await killedAndCleared(pingsPolicy)
    const r = await gate.result("A", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    const a = await state(store, "A")
    assert.equal(a["ended"], true)
    assert.equal(a["calls"]["c1"]["reconciled"], "succeeded")
    const ledger = JSON.parse((await store.loadLedger("u1"))!.text)
    assert.equal(ledger.tombstone, undefined)
    assert.deepEqual(ledger.entries.map((e: { call: string; committed: boolean }) => [e.call, e.committed]), [["c1", true]])
  })

  t("the resent reconcile keeps the untrusted clamp", async () => {
    const { store, gate } = await killedAndCleared(spendPolicy, { amount: "1200", currency: "USD" })
    const r = await gate.result("A", { callId: "c1", outcome: "succeeded", actualCost: "100", noEffect: true }, { untrusted: true })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    assert.equal((await state(store, "A"))["ended"], true)
    const entries = JSON.parse((await store.loadLedger("u1"))!.text).entries as { call: string; amount: string; committed: boolean }[]
    assert.deepEqual(entries.map((e) => [e.call, e.amount, e.committed]), [["c1", "1200", true]])
  })

  t("a repeated reconcile after the resend is already_reconciled", async () => {
    const { store, gate } = await killedAndCleared(pingsPolicy)
    const input = { callId: "c1", outcome: "succeeded" as const }
    assert.equal((await gate.result("A", input)).verdict.verdict, "accepted")
    const version = (await store.loadLedger("u1"))!.version
    const r = await gate.reconcile("A", input)
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "already_reconciled", JSON.stringify(r.verdict))
    assert.equal((await store.loadLedger("u1"))!.version, version)
  })

  t("outcomeUnknown after clearPrincipalKill is not resent", async () => {
    const { store, gate } = await killedAndCleared(pingsPolicy)
    const u = await gate.outcomeUnknown("A", "c1")
    assert.equal(u.verdict.verdict === "rejected" && u.verdict.reason, "ledger_conflict", JSON.stringify(u.verdict))
    const a = await state(store, "A")
    assert.equal(a["ended"], true)
    assert.equal(a["calls"]["c1"]["status"], "unknown")
    const r = await gate.reconcile("A", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
  })

  t("after the gate ends a session, its other dispatched calls settle through result", async () => {
    const store = await make()
    const gate = gateFor(pingsPolicy, store)
    await opened(gate, "A")
    for (const callId of ["c1", "c2"]) {
      assert.equal((await gate.propose("A", { callId, tool: "ping", callDigest: "d" })).kind, "allowed")
      assert.equal((await gate.dispatch("A", { callId, callDigest: "d" })).claimed, true)
    }
    await gate.killPrincipal("u1")
    const p = await gate.propose("A", { callId: "c3", tool: "ping", callDigest: "d" })
    assert.equal(p.kind === "denied" && p.reason, "killed", JSON.stringify(p.verdict))
    await gate.clearPrincipalKill("u1")
    for (const callId of ["c1", "c2"]) {
      const r = await gate.result("A", { callId, outcome: "succeeded" })
      assert.equal(r.verdict.verdict, "accepted", `${callId}: ${JSON.stringify(r.verdict)}`)
    }
    const a = await state(store, "A")
    assert.equal(a["ended"], true)
    assert.equal(a["calls"]["c2"]["reconciled"], "succeeded")
    const ledger = JSON.parse((await store.loadLedger("u1"))!.text)
    assert.deepEqual(ledger.entries.map((e: { call: string; committed: boolean }) => [e.call, e.committed]), [["c1", true], ["c2", true]])
  })

  t("result on a host-ended session settles as reconcile", async () => {
    const store = await make()
    const gate = gateFor(pingsPolicy, store)
    await opened(gate, "A")
    assert.equal((await gate.propose("A", { callId: "c1", tool: "ping", callDigest: "d" })).kind, "allowed")
    assert.equal((await gate.dispatch("A", { callId: "c1", callDigest: "d" })).claimed, true)
    assert.equal((await gate.end("A")).verdict.verdict, "accepted")
    const r = await gate.result("A", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    const a = await state(store, "A")
    assert.equal(a["ended"], true)
    assert.equal(a["calls"]["c1"]["reconciled"], "succeeded")
    const ledger = JSON.parse((await store.loadLedger("u1"))!.text)
    assert.deepEqual(ledger.entries.map((e: { call: string; committed: boolean }) => [e.call, e.committed]), [["c1", true]])
  })

  t("a result resent after a forced end is not resent again", async () => {
    const { store } = await killedAndCleared(pingsPolicy)
    const steps: string[] = []
    // A reconcile is never session_ended in the real kernel, so the stub makes it one to show the resend stops.
    const stub: Kernel = {
      ...kernel,
      step(policyText, stateText, event) {
        steps.push(event.type)
        const r = kernel.step(policyText, stateText, event)
        if (event.type !== "reconcile") return r
        const verdict: Verdict = { verdict: "rejected", state_version: r.stateVersion, reason: "session_ended", retry: "never", message: "stub" }
        return { ...r, verdict, changed: false }
      },
    }
    const gate = gateFor(pingsPolicy, store, { kernel: stub })
    const r = await gate.result("A", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict === "rejected" && r.verdict.reason, "session_ended", JSON.stringify(r.verdict))
    assert.deepEqual(steps, ["result", "ledger_sync", "session_end", "reconcile"])
  })

  t("a full session can still be killed, ended and settled", async () => {
    const probe = new Probe(await make())
    const roomy = gateFor(openPolicy, probe)
    await opened(roomy, "s1")
    await roomy.propose("s1", { callId: "c1", tool: "search", callDigest: "d1" })
    await roomy.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d1" })
    const bytes = utf8Bytes((await probe.load("s1"))!.state)
    const limit = bytes + 128
    const headroom = Math.floor(limit * 7 / 8)
    assert.ok(bytes > headroom, `${bytes} > ${headroom}`)
    const full = gateFor(openPolicy, probe, { maxStateBytes: limit })
    const before = await probe.load("s1")
    const commits = probe.commits
    const isFull = (e: unknown) => e instanceof WritStateFullError && e.sessionId === "s1" && e.bytes === bytes && e.limit === headroom
    await assert.rejects(full.propose("s1", { callId: "c2", tool: "search", callDigest: "d2" }), isFull)
    await assert.rejects(full.permissionAdd("s1", { permission: "p.x", approverId: "owner" }), isFull)
    await assert.rejects(full.dispatch("s1", { callId: "c1", attempt: 2, callDigest: "d1" }), isFull)
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s1"), before)
    assert.equal((await full.result("s1", { callId: "c1", outcome: "succeeded" })).verdict.verdict, "accepted")
    assert.equal((await full.kill("s1")).verdict.verdict, "accepted")
    assert.equal((await full.end("s1")).verdict.verdict, "accepted")
    const s = await state(probe, "s1")
    assert.equal(s["calls"]["c1"]["status"], "succeeded")
    assert.equal(s["killed"], true)
    assert.equal(s["ended"], true)
    assert.ok(utf8Bytes((await probe.load("s1"))!.state) <= limit)
  })

  t("a step whose new state is over the budget is not committed", async () => {
    const probe = new Probe(await make())
    const roomy = gateFor(openPolicy, probe)
    await opened(roomy, "s1")
    await roomy.propose("s1", { callId: "c1", tool: "search", callDigest: "d1" })
    await roomy.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d1" })
    const limit = utf8Bytes((await probe.load("s1"))!.state) - 100
    const before = await probe.load("s1")
    const commits = probe.commits
    const tight = gateFor(openPolicy, probe, { maxStateBytes: limit })
    await assert.rejects(tight.result("s1", { callId: "c1", outcome: "succeeded" }),
      (e: unknown) => e instanceof WritStateFullError && e.sessionId === "s1" && e.bytes > limit && e.limit === limit)
    assert.equal(probe.commits, commits)
    assert.deepEqual(await probe.load("s1"), before)
    const tiny = gateFor(openPolicy, probe, { maxStateBytes: 64 })
    await assert.rejects(tiny.start({ sessionId: "s2", requester: "u1", permissions: [], approvers: {} }), WritStateFullError)
    assert.equal(await probe.load("s2"), null)
    assert.throws(() => gateFor(openPolicy, probe, { maxStateBytes: 0 }), WritInputError)
    assert.throws(() => gateFor(openPolicy, probe, { maxStateBytes: 1.5 }), WritInputError)
  })

  t("session_start counts the incoming ledger against the budget", async () => {
    const store = await make()
    const gate = gateFor(callsPolicy, store)
    await opened(gate, "s1")
    const initial = utf8Bytes(kernel.initial(callsPolicy).state)
    await gate.killPrincipal("u1")
    const ledger = utf8Bytes((await store.loadLedger("u1"))!.text)
    // Above seven eighths only with the ledger counted.
    const limit = Math.ceil((initial + ledger) * 8 / 7) - 1
    assert.ok(initial <= Math.floor(limit * 7 / 8))
    const tight = gateFor(callsPolicy, store, { maxStateBytes: limit })
    await assert.rejects(tight.start({ sessionId: "s2", requester: "u1", permissions: [], approvers: {} }),
      (e: unknown) => e instanceof WritStateFullError && e.bytes === initial + ledger)
    assert.equal(await store.load("s2"), null)
  })

  t("a retired policy settles but does not propose", async () => {
    const store = await make()
    const old = gateFor(callsPolicy, store)
    await opened(old, "s1")
    await old.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    await old.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d" })
    const committed = async () =>
      (JSON.parse((await store.loadLedger("u1"))!.text).entries as { call: string; committed: boolean }[]).map((e) => [e.call, e.committed])
    assert.deepEqual(await committed(), [["c1", false]])
    const next = gateFor(openPolicy, store, { retiredPolicyTexts: [callsPolicy] })
    const r = await next.result("s1", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    assert.deepEqual(await committed(), [["c1", true]])
    assert.equal((await state(store, "s1"))["calls"]["c1"]["status"], "succeeded")
    const changed = (e: unknown) =>
      e instanceof WritPolicyChangedError && e.sessionId === "s1" && e.policyDigest === kernel.digest(callsPolicy)
    const before = await store.load("s1")
    await assert.rejects(next.propose("s1", { callId: "c2", tool: "ping", callDigest: "d" }), changed)
    await assert.rejects(next.stepStart("s1"), changed)
    await assert.rejects(next.dispatch("s1", { callId: "c1", attempt: 2, callDigest: "d" }), changed)
    assert.deepEqual(await store.load("s1"), before)
    await assert.rejects(gateFor(openPolicy, store).end("s1"), changed)
    await assert.rejects(gateFor(openPolicy, store).inspect("s1"), changed)
    assert.deepEqual((await next.inspect("s1"))?.calls.map((c) => [c.call_id, c.status]), [["c1", "succeeded"]])
    assert.equal((await next.end("s1")).verdict.verdict, "accepted")
    assert.equal((await state(store, "s1"))["ended"], true)
    await opened(next, "s2")
    assert.equal((await next.propose("s2", { callId: "c1", tool: "search", callDigest: "d" })).kind, "allowed")
  })

  t("createGate refuses a failing policy", async () => {
    const store = await make()
    const bad = JSON.stringify({ writ: "0.1", actions: { ping: { meters: ["nope"] } } })
    assert.throws(() => createGate({ kernel, policyText: bad, store }),
      (e: unknown) => e instanceof WritInputError && e.path === "policyText" && /policy fails check: unknown_meter/.test(e.message))
    assert.throws(() => createGate({ kernel, policyText: openPolicy, store, retiredPolicyTexts: [callsPolicy, bad] }),
      (e: unknown) => e instanceof WritInputError && e.path === "retiredPolicyTexts[1]" && /unknown_meter/.test(e.message))
  })

  t("createGate refuses a retired policy whose shared principal meter has another window", async () => {
    const store = await make()
    const calls = (scope: string, window_ms?: number) => JSON.stringify({
      writ: "0.1",
      meters: { calls: { unit: "calls", cap: 3, scope, window_ms } },
      actions: { ping: { meters: ["calls"] } },
    })
    const refused = (i: number) => (e: unknown) =>
      e instanceof WritInputError && e.path === `retiredPolicyTexts[${i}]` && /calls/.test(e.message) && /window_ms/.test(e.message)
    assert.throws(() => createGate({ kernel, policyText: pingsPolicy, store, retiredPolicyTexts: [openPolicy, calls("principal")] }), refused(1))
    assert.throws(() => createGate({ kernel, policyText: pingsPolicy, store, retiredPolicyTexts: [calls("principal", 3600000)] }), refused(0))
    assert.throws(() => createGate({ kernel, policyText: calls("principal"), store, retiredPolicyTexts: [pingsPolicy] }), refused(0))
    createGate({ kernel, policyText: pingsPolicy, store, retiredPolicyTexts: [callsPolicy, calls("session", 1000), spendPolicy] })
    createGate({ kernel, policyText: calls("session"), store, retiredPolicyTexts: [pingsPolicy] })
    createGate({ kernel, policyText: calls("principal"), store, retiredPolicyTexts: [calls("principal")] })
  })

  t("createGate refuses two retired policies that disagree on a window", async () => {
    const store = await make()
    const hourly = JSON.stringify({
      writ: "0.1",
      meters: { calls: { unit: "calls", cap: 3, scope: "principal", window_ms: 3600000 } },
      actions: { ping: { meters: ["calls"] } },
    })
    assert.throws(() => createGate({ kernel, policyText: openPolicy, store, retiredPolicyTexts: [callsPolicy, hourly] }),
      (e: unknown) => e instanceof WritInputError && e.path === "retiredPolicyTexts[1]" &&
        /"calls"/.test(e.message) && /retiredPolicyTexts\[0\]/.test(e.message))
    createGate({ kernel, policyText: openPolicy, store, retiredPolicyTexts: [callsPolicy, pingsPolicy] })
  })

  const spendIn = (currency: string, scope = "principal", extra: Record<string, unknown> = {}) => JSON.stringify({
    writ: "0.1",
    meters: { spend: { currency, cap: 5000, scope, window_ms: 86400000, ...extra } },
    actions: { buy: { meters: ["spend"] } },
  })

  t("createGate refuses a retired policy whose shared principal meter has another currency", async () => {
    const store = await make()
    assert.throws(() => createGate({ kernel, policyText: spendPolicy, store, retiredPolicyTexts: [spendIn("EUR")] }),
      (e: unknown) => e instanceof WritInputError && e.path === "retiredPolicyTexts[0]" &&
        /"spend"/.test(e.message) && /money in "EUR"/.test(e.message) && /money in "USD"/.test(e.message) &&
        /policyText/.test(e.message) && /rename the meter/.test(e.message))
    createGate({ kernel, policyText: spendPolicy, store, retiredPolicyTexts: [spendIn("USD", "principal", { cap: 9000, max_per_call: 100 })] })
  })

  t("createGate refuses a retired policy whose shared principal meter is calls instead of money", async () => {
    const store = await make()
    const callsNamedSpend = (window_ms: number) => JSON.stringify({
      writ: "0.1",
      meters: { spend: { unit: "calls", cap: 3, scope: "principal", window_ms } },
      actions: { buy: { meters: ["spend"] } },
    })
    assert.throws(() => createGate({ kernel, policyText: spendPolicy, store, retiredPolicyTexts: [callsNamedSpend(86400000)] }),
      (e: unknown) => e instanceof WritInputError && e.path === "retiredPolicyTexts[0]" &&
        /"spend" is a calls meter here, but policyText makes it money in "USD";/.test(e.message))
    assert.throws(() => createGate({ kernel, policyText: spendPolicy, store, retiredPolicyTexts: [callsNamedSpend(3600000)] }),
      (e: unknown) => e instanceof WritInputError && e.path === "retiredPolicyTexts[0]" &&
        /"spend" is a calls meter with window_ms 3600000 here, but policyText makes it money in "USD" with window_ms 86400000;/
          .test(e.message))
  })

  t("createGate refuses two retired policies that disagree on a meter's currency", async () => {
    const store = await make()
    assert.throws(() => createGate({ kernel, policyText: openPolicy, store, retiredPolicyTexts: [spendIn("USD"), spendIn("EUR")] }),
      (e: unknown) => e instanceof WritInputError && e.path === "retiredPolicyTexts[1]" &&
        /"spend"/.test(e.message) && /retiredPolicyTexts\[0\]/.test(e.message) && /"EUR"/.test(e.message) && /"USD"/.test(e.message))
  })

  t("createGate accepts a retired policy whose same-named meter is session-scope with another currency", async () => {
    const store = await make()
    createGate({ kernel, policyText: spendPolicy, store, retiredPolicyTexts: [spendIn("EUR", "session")] })
  })

  t("a retired session meter never prunes a live principal meter", async () => {
    const store = await make()
    let time = 1000
    const clock = () => time
    const retiredText = JSON.stringify({
      writ: "0.1",
      meters: {
        spend: { currency: "USD", cap: 5000, window_ms: 10 },
        uses: { unit: "calls", cap: 10, scope: "principal" },
      },
      actions: { buy: { meters: ["spend"] }, use: { meters: ["uses"] } },
    })
    const old = gateFor(retiredText, store, { clock })
    await opened(old, "A")
    assert.equal((await old.propose("A", { callId: "c1", tool: "use", callDigest: "d" })).kind, "allowed")
    assert.equal((await old.dispatch("A", { callId: "c1", callDigest: "d" })).claimed, true)
    const live = gateFor(spendPolicy, store, { clock, retiredPolicyTexts: [retiredText] })
    await opened(live, "B")
    const cost = { amount: "5", currency: "USD" }
    assert.equal((await live.propose("B", { callId: "c1", tool: "buy", callDigest: "d", cost })).kind, "allowed")
    assert.equal((await live.dispatch("B", { callId: "c1", callDigest: "d", cost })).claimed, true)
    assert.equal((await live.result("B", { callId: "c1", outcome: "succeeded" })).verdict.verdict, "accepted")
    time += 10
    const r = await live.result("A", { callId: "c1", outcome: "succeeded" })
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    const entries = JSON.parse((await store.loadLedger("u1"))!.text).entries as { meter: string; session: string; committed: boolean }[]
    assert.deepEqual(entries.map((e) => [e.meter, e.session, e.committed]), [["uses", "A", true], ["spend", "B", true]])
  })

  t("dispatch reports claimed", async () => {
    const store = await make()
    const gate = gateFor(callsPolicy, store)
    await opened(gate, "s1")
    await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    await gate.propose("s1", { callId: "c2", tool: "ping", callDigest: "d" })
    const won = await gate.dispatch("s1", { callId: "c1", callDigest: "d" })
    assert.equal(won.claimed, true)
    assert.equal(won.reason, undefined)
    const lost = await gate.dispatch("s1", { callId: "c2", callDigest: "d" })
    assert.equal(lost.claimed, false, JSON.stringify(lost.verdict))
    assert.equal(lost.reason, "meter_exceeded")
    assert.equal((await state(store, "s1"))["calls"]["c2"]["status"], "authorized")
  })

  t("attempt defaults from state", async () => {
    const store = await make()
    const gate = gateFor(retryPolicy, store)
    await opened(gate, "s1")
    await gate.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    assert.equal((await gate.dispatch("s1", { callId: "c1", callDigest: "d" })).claimed, true)
    await gate.outcomeUnknown("s1", "c1")
    const again = await gate.dispatch("s1", { callId: "c1", callDigest: "d" })
    assert.equal(again.claimed, true, JSON.stringify(again.verdict))
    assert.equal((await state(store, "s1"))["calls"]["c1"]["attempts"], 2)
  })

  t("a defaulted attempt is fixed at the first read, so a retry another gate allowed meanwhile is not claimed", async () => {
    const probe = new Probe(await make())
    const a = gateFor(retryPolicy, probe)
    const b = gateFor(retryPolicy, probe)
    await opened(a, "s1")
    await a.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    const hold = probe.holdNext()
    const pa = a.dispatch("s1", { callId: "c1", callDigest: "d" })
    await hold.entered
    assert.equal((await b.dispatch("s1", { callId: "c1", callDigest: "d" })).claimed, true)
    await b.outcomeUnknown("s1", "c1")
    hold.release()
    const ra = await pa
    assert.equal(ra.claimed, false, JSON.stringify(ra.verdict))
    const s = await state(probe, "s1")
    assert.equal(s["calls"]["c1"]["attempts"], 1)
    assert.equal(s["calls"]["c1"]["status"], "unknown")
  })

  t("result reports overrun meters", async () => {
    const store = await make()
    const gate = gateFor(spendPolicy, store)
    await opened(gate, "s1")
    const cost = { amount: "1200", currency: "USD" }
    for (const id of ["c1", "c2"]) {
      await gate.propose("s1", { callId: id, tool: "buy", callDigest: id, cost })
      await gate.dispatch("s1", { callId: id, callDigest: id, cost })
    }
    const over = await gate.result("s1", { callId: "c1", outcome: "succeeded", actualCost: "1500" })
    assert.equal(over.verdict.verdict, "accepted", JSON.stringify(over.verdict))
    assert.deepEqual(over.overrun, ["spend"])
    const normal = await gate.result("s1", { callId: "c2", outcome: "succeeded", actualCost: "1000" })
    assert.equal(normal.verdict.verdict, "accepted", JSON.stringify(normal.verdict))
    assert.deepEqual(normal.overrun, [])
  })

  t("inspect lists calls for recovery", async () => {
    const store = await make()
    const crashed = gateFor(callsPolicy, store)
    await opened(crashed, "s1")
    await crashed.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
    assert.equal((await crashed.dispatch("s1", { callId: "c1", callDigest: "d" })).claimed, true)
    const before = await store.load("s1")
    const view = await gateFor(callsPolicy, store).inspect("s1")
    assert.ok(view !== null)
    assert.equal(view.session_id, "s1")
    assert.equal(view.state_version, before!.stateVersion)
    assert.deepEqual(view.calls.map((c) => [c.call_id, c.status, c.attempts]), [["c1", "dispatched", 1]])
    assert.deepEqual(await store.load("s1"), before)
    assert.equal(await gateFor(callsPolicy, store).inspect("missing"), null)
  })

  t("a store's own byte limit caps a larger maxStateBytes", async () => {
    const inner = await make()
    const roomy = gateFor(openPolicy, inner)
    await opened(roomy, "s1")
    await roomy.propose("s1", { callId: "c1", tool: "search", callDigest: "d1" })
    const bytes = utf8Bytes((await inner.load("s1"))!.state)
    const limit = bytes + 64
    const headroom = Math.floor(limit * 7 / 8)
    assert.ok(bytes > headroom, `${bytes} > ${headroom}`)
    const gate = gateFor(openPolicy, limited(inner, limit), { maxStateBytes: limit * 100 })
    await assert.rejects(gate.propose("s1", { callId: "c2", tool: "search", callDigest: "d2" }),
      (e: unknown) => e instanceof WritStateFullError && e.bytes === bytes && e.limit === headroom)
    const smaller = gateFor(openPolicy, limited(inner, limit * 100), { maxStateBytes: limit })
    await assert.rejects(smaller.propose("s1", { callId: "c2", tool: "search", callDigest: "d2" }),
      (e: unknown) => e instanceof WritStateFullError && e.limit === headroom)
  })

  t("killPrincipal and clearPrincipalKill refuse a malformed principal", async () => {
    const store = await make()
    const gate = gateFor(callsPolicy, store)
    const bad = [undefined, 7, "", "x".repeat(513), "\u00e9".repeat(257)] as unknown as string[]
    for (const p of bad) {
      for (const f of [gate.killPrincipal, gate.clearPrincipalKill]) {
        await assert.rejects(f(p), (e: unknown) => e instanceof WritInputError && e.path === "principal", String(p).slice(0, 20))
      }
    }
    assert.deepEqual(await gate.killPrincipal("x".repeat(512)), { ledgerVersion: 1, changed: true })
  })

  t("idempotency keys differ across principals", async () => {
    assert.notEqual(await defaultIdempotencyKey("u1", "s", "c"), await defaultIdempotencyKey("u2", "s", "c"))
    const store = await make()
    const gate = gateFor(openPolicy, store)
    await opened(gate, "s1", "u7")
    await gate.propose("s1", { callId: "c1", tool: "search", callDigest: "d" })
    await gate.dispatch("s1", { callId: "c1", attempt: 1, callDigest: "d" })
    assert.equal((await state(store, "s1"))["calls"]["c1"]["idempotency_key"], await defaultIdempotencyKey("u7", "s1", "c1"))
  })
}
