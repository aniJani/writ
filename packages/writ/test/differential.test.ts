import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { test } from "node:test"
import { nativeWrit, repoRoot } from "./helpers.js"
import { loadKernel } from "../src/index.js"
import type { Approver, Cost, RequestId, Verdict, WritEvent } from "../src/index.js"

const STREAMS = 300
const EVENTS = 30

function mulberry32(seed: number): () => number {
  let a = seed >>> 0
  return () => {
    a = (a + 0x6d2b79f5) >>> 0
    let t = a
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

const trace = JSON.parse(readFileSync(join(repoRoot, "corpus/examples/payments.jsonl"), "utf8").split("\n")[0]!) as {
  policy: unknown
  events: { event: Extract<WritEvent, { type: "session_start" }> }[]
}
const base = trace.policy as { actions: Record<string, unknown> }
// payments.jsonl plus one action that needs no approval, so the allowed decision is reachable.
const policyText = JSON.stringify({ ...base, actions: { ...base.actions, "report.read": { permission: "payments" } } })
const approvers: Record<string, Approver> = trace.events[0]!.event.approvers
const approverNames = Object.keys(approvers)
const tools = ["vendor.pay", "card.charge", "card.charge", "report.read", "report.read", "wire.unknown"]
const SUB_DIGEST = "d-sub-1000"
const SUB_COST = { amount: "1000", currency: "USD" }
const BIG_AMOUNTS = ["2147483648", "18446744073709551616", "9".repeat(78)]

interface Tracked { tool: string; digest: string; cost?: Cost; request: RequestId; state: "awaiting" | "authorized" | "dispatched" }

type Kind = "session_start" | "turn_start" | "turn_end" | "step_start" | "kill" | "propose" | "approve" | "reject" |
  "dispatch" | "result" | "reconcile" | "cancel" | "outcome_unknown" | "approval_expire" | "ledger_sync" | "permission_add" | "grant_create"

interface Gen {
  next(ver: number): WritEvent
  observe(e: WritEvent, v: Verdict): void
}

function generator(seed: number, digest: string): Gen {
  const rnd = mulberry32(seed)
  const pick = <T>(xs: readonly T[]): T => xs[Math.floor(rnd() * xs.length)]!
  const chance = (p: number): boolean => rnd() < p
  const tracked = new Map<string, Tracked>()
  let lastSeq = 0
  let lastTime = 0
  let nextCall = 1
  let n = 0

  // Amounts from 2^31 up are heap Nats on wasm32 and go through the runtime's own mpn code,
  // where native uses GMP. Most stay small so that calls still fit the meter. The swap draws
  // from its own stream, so the streams keep their shape and only some amounts grow.
  const bigRnd = mulberry32(seed ^ 0x5bd1e995)
  const amount = (big: number, small: readonly number[]): string => {
    const usual = String(pick(small))
    return bigRnd() < big ? BIG_AMOUNTS[Math.floor(bigRnd() * BIG_AMOUNTS.length)]! : usual
  }
  const cost = (): Cost => ({ amount: amount(0.1, [100, 500, 2000, 3000]), currency: chance(0.04) ? "EUR" : "USD" })
  const inState = (state: Tracked["state"]): [string, Tracked][] => [...tracked].filter(([, t]) => t.state === state)
  const target = (state: Tracked["state"], noise: number): [string, Tracked | undefined] => {
    const live = inState(state)
    if (live.length > 0 && !chance(noise)) return pick(live)
    return [`c${1 + Math.floor(rnd() * nextCall)}`, undefined]
  }
  const anyCall = (): string => (tracked.size > 0 && chance(0.7) ? pick([...tracked.keys()]) : `c${1 + Math.floor(rnd() * nextCall)}`)
  const requestFor = (call: string, t?: Tracked): RequestId => t?.request ?? { session: "s1", call, generation: 0 }

  return {
    next(ver) {
      const i = n++
      const head = {
        seq: chance(0.04) ? Math.max(1, lastSeq - Math.floor(rnd() * 2)) : lastSeq + 1,
        time: chance(0.03) ? Math.max(0, lastTime - 1 - Math.floor(rnd() * 20)) : lastTime + Math.floor(rnd() * 50),
        state_version: chance(0.05) ? Math.max(0, ver + pick([-1, 1, 2])) : ver,
      }
      let kind: Kind = i === 0 && chance(0.95) ? "session_start" : chance(0.008) ? "kill" : pick([
        "session_start", "turn_start", "turn_start", "turn_end", "step_start", "step_start", "step_start",
        "propose", "propose", "propose", "propose", "propose", "propose",
        "approve", "approve", "approve", "approve", "approve", "reject",
        "dispatch", "dispatch", "dispatch", "dispatch", "result", "result", "result", "result",
        "reconcile", "ledger_sync", "grant_create", "cancel", "outcome_unknown", "approval_expire",
        "permission_add",
      ])
      const needs: Partial<Record<Kind, Tracked["state"]>> = {
        approve: "awaiting", reject: "awaiting", approval_expire: "awaiting", dispatch: "authorized", result: "dispatched", reconcile: "dispatched",
      }
      // Without a live call these would only produce unknown_call, so mostly propose instead.
      const need = needs[kind]
      if (need && inState(need).length === 0 && !chance(0.08)) kind = "propose"
      switch (kind) {
        case "session_start":
          return {
            ...head, type: "session_start", session_id: "s1", policy_digest: chance(0.03) ? "sha256:" + "0".repeat(64) : digest,
            requester: "u1", permissions: chance(0.1) ? [] : ["payments"], approvers, ledger: {},
          }
        case "turn_start": return { ...head, type: "turn_start", user_initiated: chance(0.85) }
        case "turn_end": case "step_start": case "kill": return { ...head, type: kind }
        case "propose": {
          const call_id = chance(0.9) ? `c${nextCall++}` : `c${1 + Math.floor(rnd() * nextCall)}`
          const tool = pick(tools)
          const sub = tool === "card.charge" && chance(0.5)
          return {
            ...head, type: "propose", call_id, tool, call_digest: sub ? SUB_DIGEST : `d-${call_id}`,
            ...(chance(0.95) ? { cost: sub ? SUB_COST : cost() } : {}), guards: {}, escalators: {},
          }
        }
        case "approve": {
          const [call_id, t] = target("awaiting", 0.08)
          return {
            ...head, type: "approve", call_id, request_id: requestFor(call_id, t), approver: chance(0.97) ? pick(approverNames) : "nobody",
            reviewed_digest: t && !chance(0.05) ? t.digest : "d-other",
            ...(t?.cost && !chance(0.05) ? { reviewed_cost: t.cost } : chance(0.5) ? { reviewed_cost: cost() } : {}),
          }
        }
        case "reject": {
          const [call_id, t] = target("awaiting", 0.2)
          return { ...head, type: "reject", call_id, request_id: requestFor(call_id, t), approver: pick(approverNames) }
        }
        case "dispatch": {
          const [call_id, t] = target("authorized", 0.1)
          return {
            ...head, type: "dispatch", call_id, attempt: chance(0.95) ? 1 : 2, call_digest: t && !chance(0.05) ? t.digest : "d-other",
            ...(t?.cost && !chance(0.05) ? { cost: t.cost } : {}), guards: {}, idempotency_key: `k-s1-${call_id}`,
          }
        }
        case "result": case "reconcile": {
          const [call_id] = target("dispatched", 0.1)
          return {
            ...head, type: kind, call_id, outcome: pick(["succeeded", "succeeded", "succeeded", "succeeded", "declined", "failed"] as const),
            ...(chance(0.4) ? { actual_cost: amount(0.5, [50, 400, 1500]) } : {}), ...(chance(0.1) ? { no_effect: true } : {}),
          }
        }
        case "cancel": case "outcome_unknown": return { ...head, type: kind, call_id: anyCall() }
        case "approval_expire": {
          const [call_id, t] = target("awaiting", 0.3)
          return { ...head, type: "approval_expire", call_id, request_id: requestFor(call_id, t) }
        }
        case "ledger_sync": return { ...head, type: "ledger_sync", ledger: { version: Math.floor(rnd() * 4), ...(chance(0.05) ? { tombstone: true } : {}) } }
        case "permission_add": return { ...head, type: "permission_add", permission: "payments", approver: pick(approverNames) }
        case "grant_create":
          return {
            ...head, type: "grant_create", grant_id: `g${1 + Math.floor(rnd() * 3)}`, approver: pick(["mgr", "fin", "own"]), tool: "card.charge",
            ...(chance(0.8) ? { call_digest: SUB_DIGEST } : {}), scope: "session", max_uses: 1 + Math.floor(rnd() * 3),
            ...(chance(0.7) ? { max_cost: { amount: "2500", currency: "USD" } } : {}), expires_at: 3600000, reviewed_scope_digest: "scope-sub",
          }
      }
    },
    observe(e, v) {
      if (v.verdict !== "accepted") return
      lastSeq = e.seq
      lastTime = e.time
      if (e.type === "session_start" || e.type === "kill" || e.type === "reset") tracked.clear()
      const set = (id: string, state: Tracked["state"] | null) => {
        const t = tracked.get(id)
        if (!t) return
        if (state === null) tracked.delete(id)
        else t.state = state
      }
      switch (e.type) {
        case "propose": {
          const t: Omit<Tracked, "state" | "request"> = { tool: e.tool, digest: e.call_digest, ...(e.cost ? { cost: e.cost } : {}) }
          if (v.decision === "needs_approval") tracked.set(e.call_id, { ...t, request: v.request_id, state: "awaiting" })
          else if (v.decision === "authorized" || v.decision === "allowed" || v.decision === "allowed_by_grant") {
            tracked.set(e.call_id, { ...t, request: { session: "s1", call: e.call_id, generation: 0 }, state: "authorized" })
          }
          break
        }
        case "approve":
          if (v.decision === "authorized") set(e.call_id, "authorized")
          else if (e.edit) tracked.delete(e.call_id)
          break
        case "reject": case "cancel": case "approval_expire": set(e.call_id, null); break
        case "dispatch": if (v.decision === "dispatch_claimed") set(e.call_id, "dispatched"); break
        case "result": case "reconcile": set(e.call_id, null); break
        case "outcome_unknown": set(e.call_id, "dispatched"); break
        default: break
      }
    },
  }
}

const skip = existsSync(nativeWrit) ? false : `native binary ${nativeWrit} is missing: run "lake build writ"`
if (skip) console.warn(`differential test skipped: ${skip}`)

test(`${STREAMS} seeded streams of ${EVENTS} events agree with writ oracle`, { skip }, async () => {
  const kernel = await loadKernel()
  const dir = mkdtempSync(join(tmpdir(), "writ-diff-"))
  try {
    const policyFile = join(dir, "policy.json")
    writeFileSync(policyFile, policyText)
    const checked = kernel.check(policyText)
    assert.equal(checked.ok, true, JSON.stringify(checked.errors))
    const digest = checked.policy_digest
    const counts = new Map<string, number>()
    const count = (k: string) => counts.set(k, (counts.get(k) ?? 0) + 1)

    for (let seed = 1; seed <= STREAMS; seed++) {
      const gen = generator(seed, digest)
      let state = kernel.initial(policyText, digest).state
      let version = 0
      const events: WritEvent[] = []
      const got: string[] = []
      for (let i = 0; i < EVENTS; i++) {
        const e = gen.next(version)
        events.push(e)
        const r = kernel.step(policyText, state, e)
        state = r.state
        version = r.stateVersion
        gen.observe(e, r.verdict)
        count(`${r.verdict.verdict}:${e.type}`)
        if (r.verdict.verdict === "accepted" && r.verdict.decision) count(`decision:${r.verdict.decision}`)
        if (r.verdict.verdict === "rejected") count(`reason:${r.verdict.reason}`)
        if (r.ledgerChanged) count("ledgerChanged")
        if (r.verdict.verdict === "accepted" && BIG_AMOUNTS.some((a) => JSON.stringify(e).includes(`"${a}"`))) count("bigAmount:accepted")
        if (r.changed && BIG_AMOUNTS.some((a) => r.state.includes(`"${a}"`))) count("bigAmount:state")
        got.push(JSON.stringify(r.verdict))
      }

      const stateOut = join(dir, "state.json")
      const o = spawnSync(nativeWrit, ["oracle", policyFile, "--state-out", stateOut], {
        input: events.map((e) => JSON.stringify(e)).join("\n") + "\n",
        encoding: "utf8",
      })
      assert.equal(o.status, 0, `seed ${seed}: ${o.stderr}`)
      const want = o.stdout.split("\n").filter((l) => l !== "")
      assert.deepEqual(got, want, `seed ${seed}: verdicts differ`)
      assert.equal(state + "\n", readFileSync(stateOut, "utf8"), `seed ${seed}: final state differs`)
    }
    console.log(`differential counts: ${JSON.stringify(Object.fromEntries([...counts].sort()))}`)
    const minimums: [string, number][] = [
      ["decision:dispatch_claimed", 200], ["accepted:approve", 200], ["accepted:result", 150], ["ledgerChanged", 100],
      ["decision:needs_approval", 300], ["decision:denied", 50], ["decision:allowed", 100],
      ["decision:allowed_by_grant", 20], ["accepted:grant_create", 50],
      ["bigAmount:accepted", 200], ["bigAmount:state", 1000],
      ["reason:call_awaiting", 30], ["reason:call_authorized", 40], ["reason:call_dispatched", 25],
      ["reason:call_ended", 40], ["reason:call_unknown", 5], ["reason:killed", 100],
    ]
    for (const [key, min] of minimums) assert.ok((counts.get(key) ?? 0) >= min, `${key}: ${counts.get(key) ?? 0} < ${min}`)
    const rejectedTotal = [...counts].filter(([k]) => k.startsWith("rejected:")).reduce((a, [, v]) => a + v, 0)
    assert.ok(rejectedTotal >= 1000, `only ${rejectedTotal} rejected verdicts`)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})
