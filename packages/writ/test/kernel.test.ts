import assert from "node:assert/strict"
import { test } from "node:test"
import { fixture, sessionRunner } from "./helpers.js"
import { loadKernelWithMemory } from "../src/kernel.js"
import { loadKernel, MAX_INPUT_BYTES, WritInputError, WritKernelError } from "../src/index.js"
import type { WritEvent } from "../src/index.js"

const kernel = await loadKernel()
const shop = fixture("policies/formats-shop.json")
const shopDigest = fixture("formats-digest.out").trim()

test("version matches the native binary", () => {
  assert.equal(kernel.version(), fixture("version.out").trim())
})

test("check accepts a valid policy", () => {
  const r = kernel.check(shop)
  assert.equal(r.ok, true)
  assert.equal(r.policy_digest, shopDigest)
})

test("check reports an invalid policy", () => {
  const r = kernel.check(fixture("policies/errors.json"))
  assert.equal(r.ok, false)
  assert.ok(r.errors.some((e) => e.code === "unknown_meter"))
})

test("a lone surrogate throws WritInputError", () => {
  assert.throws(() => kernel.check('{"writ":"0.1","x":"\ud800"}'), WritInputError)
  assert.throws(() => kernel.initial(shop, "\udc00"), WritInputError)
  assert.throws(() => kernel.step(shop, "", { type: "turn_end", seq: 1, time: 0, state_version: 0, origin: "\ud800" }), WritInputError)
})

const inputError = (path: string) => (e: unknown) => {
  assert.ok(e instanceof WritInputError, String(e))
  assert.equal(e.path, path)
  return true
}

test("a bad policy gives WritInputError at policyText", () => {
  assert.throws(() => kernel.initial(fixture("policies/errors.json")), inputError("policyText"))
  assert.throws(() => kernel.initial("{"), inputError("policyText"))
  assert.throws(() => kernel.check("{"), inputError("policyText"))
})

test("each kernel input error names its argument", () => {
  assert.throws(() => kernel.digest("{"), inputError("jsonText"))
  assert.throws(() => kernel.canonical("{"), inputError("jsonText"))
  assert.throws(() => kernel.replay("{"), inputError("tracesText"))
  assert.throws(() => kernel.initial(shop, "sha256:0"), inputError("digest"))
  assert.throws(() => kernel.step(shop, "{", { type: "turn_end", seq: 1, time: 0, state_version: 0 }), inputError("stateText"))
  assert.throws(() => kernel.tombstone("{", true), inputError("ledgerText"))
  assert.throws(() => kernel.check("{\"writ\":\"0.1\"}\u0000"), inputError("policyText"))
  const state = kernel.initial(shop).state
  assert.throws(() => kernel.inspect(shop, state, -1), inputError("time"))
  assert.throws(() => kernel.inspect(shop, state, 1.5), inputError("time"))
  assert.throws(() => kernel.inspect(shop, "{", 0), inputError("stateText"))
})

const shopStart: WritEvent = {
  type: "session_start", seq: 1, time: 0, state_version: 0, session_id: "s1", policy_digest: shopDigest,
  requester: "u1", permissions: ["shop.read", "shop.buy"],
  approvers: { laptop: { principal: "u1", kind: "human", roles: ["owner"] } }, ledger: {},
}

test("malformed host input is an input error and the kernel lives on", () => {
  const started = kernel.step(shop, kernel.initial(shop).state, shopStart)
  const head = { seq: 2, time: 10, state_version: 1 }
  assert.throws(() => kernel.step(shop, started.state, {
    ...head, type: "result", call_id: "c1", outcome: "succeeded", actual_cost: "6.00",
  }), inputError("event"))
  assert.throws(() => kernel.step(shop, started.state, {
    ...head, type: "propose", call_id: "x".repeat(513), tool: "search", call_digest: "d", guards: {}, escalators: {},
  }), inputError("event"))
  const simple = fixture("policies/simple.json")
  assert.throws(() => kernel.step(simple, started.state, { ...head, type: "turn_end" }), inputError("stateText"))
  const next = kernel.step(shop, started.state, { ...head, type: "turn_start", user_initiated: true })
  assert.equal(next.verdict.verdict, "accepted")
  assert.equal(next.stateVersion, 2)
})

test("tombstone sets once", () => {
  const first = kernel.tombstone("", true)
  assert.equal(first.ledgerVersion, 1)
  assert.equal(first.changed, true)
  assert.deepEqual(JSON.parse(first.ledger), { tombstone: true, version: 1 })
  const again = kernel.tombstone(first.ledger, true)
  assert.equal(again.changed, false)
  assert.equal(again.ledgerVersion, 1)
  assert.equal(again.ledger, first.ledger)
  const cleared = kernel.tombstone(first.ledger, false)
  assert.equal(cleared.changed, true)
  assert.equal(cleared.ledgerVersion, 2)
})

test("inspect shows calls and meters", () => {
  const policy = JSON.stringify({
    writ: "0.1",
    meters: { spend: { currency: "USD", cap: 5000 } },
    actions: { buy: { meters: ["spend"] } },
  })
  const digest = kernel.digest(policy)
  const events: WritEvent[] = [
    { type: "session_start", seq: 1, time: 0, state_version: 0, session_id: "s1", policy_digest: digest, requester: "u1", permissions: [], approvers: {}, ledger: {} },
    { type: "turn_start", seq: 2, time: 10, state_version: 1, user_initiated: true },
    { type: "step_start", seq: 3, time: 20, state_version: 2 },
    { type: "propose", seq: 4, time: 30, state_version: 3, call_id: "c1", tool: "buy", call_digest: "d1", cost: { amount: "1200", currency: "USD" }, guards: {}, escalators: {} },
    { type: "dispatch", seq: 5, time: 40, state_version: 4, call_id: "c1", attempt: 1, call_digest: "d1", cost: { amount: "1200", currency: "USD" }, guards: {}, idempotency_key: "k1" },
  ]
  let state = kernel.initial(policy).state
  for (const e of events) {
    const r = kernel.step(policy, state, e)
    assert.equal(r.verdict.verdict, "accepted", JSON.stringify(r.verdict))
    state = r.state
  }
  const view = kernel.inspect(policy, state, 50)
  assert.equal(view.session_id, "s1")
  assert.equal(view.state_version, 5)
  assert.equal(view.started, true)
  assert.equal(view.killed, false)
  assert.equal(view.calls.length, 1)
  const call = view.calls[0]!
  assert.equal(call.call_id, "c1")
  assert.equal(call.status, "dispatched")
  assert.equal(call.attempts, 1)
  assert.deepEqual(call.cost, { amount: "1200", currency: "USD" })
  assert.equal(call.request_id, undefined)
  assert.deepEqual(view.meters, [{ meter: "spend", scope: "session", used: "1200", cap: "5000", remaining: "3800" }])
})

test("session_start then propose needs approval at state version 3", () => {
  const init = kernel.initial(shop, shopDigest)
  assert.equal(init.stateVersion, 0)
  const a = kernel.step(shop, init.state, shopStart)
  assert.equal(a.verdict.verdict, "accepted")
  assert.equal(a.stateVersion, 1)
  const turn = kernel.step(shop, a.state, { type: "turn_start", seq: 2, time: 10, state_version: 1, user_initiated: true })
  const b = kernel.step(shop, turn.state, {
    type: "propose", seq: 3, time: 20, state_version: 2, call_id: "c1", tool: "buy", call_digest: "d1",
    cost: { amount: "1200", currency: "USD" }, guards: { card_on_file: true }, escalators: {},
  })
  assert.equal(b.verdict.verdict, "accepted")
  assert.equal("decision" in b.verdict && b.verdict.decision, "needs_approval")
  assert.equal(b.stateVersion, 3)
})

test("the oracle fixture session gives the oracle verdicts and final state", () => {
  const run = sessionRunner(kernel)
  const { verdicts, state } = run()
  assert.deepEqual(verdicts, fixture("oracle-1.out").trimEnd().split("\n").filter((l) => !l.startsWith('{"error"')))
  assert.equal(state + "\n", fixture("states/after-1.json"))
})

test("amounts of 2^31 and up give the native oracle's verdicts and state", () => {
  const policy = fixture("policies/big-amounts.json")
  let state = kernel.initial(policy).state
  const verdicts = fixture("oracle-big-events.jsonl").trimEnd().split("\n").map((l) => {
    const r = kernel.step(policy, state, JSON.parse(l) as WritEvent)
    state = r.state
    return JSON.stringify(r.verdict)
  })
  assert.deepEqual(verdicts, fixture("oracle-big.out").trimEnd().split("\n"))
  assert.equal(state + "\n", fixture("states/after-big.json"))
})

test("10,000 steps on one kernel keep the heap flat and results unchanged", async () => {
  const { kernel: long, memoryBytes, heapUsed } = await loadKernelWithMemory()
  const run = sessionRunner(long)
  const perLoop = run().verdicts.length
  const warmup = Math.ceil(100 / perLoop)
  const loops = Math.ceil(10000 / perLoop)
  const tail: string[] = []
  let usedAfterWarmup = 0
  let memoryAfterWarmup = 0
  for (let i = 0; i < loops; i++) {
    const { results } = run()
    if (i === warmup - 1) {
      usedAfterWarmup = heapUsed()
      memoryAfterWarmup = memoryBytes()
    }
    if (i >= loops - 2) tail.push(...results)
  }
  const fresh = sessionRunner(await loadKernel())
  const want = [...fresh().results, ...fresh().results]
  assert.deepEqual(tail.slice(-10), want.slice(-10))
  assert.ok(memoryBytes() <= 2 * memoryAfterWarmup, `memory grew from ${memoryAfterWarmup} to ${memoryBytes()} bytes`)
  // Allocation accounting is exact and the steps are deterministic, so any difference is a leak.
  assert.equal(heapUsed(), usedAfterWarmup)
})

test("loadKernel accepts any ArrayBuffer view and cross-realm buffers", async () => {
  const { readFile } = await import("node:fs/promises")
  const { runInNewContext } = await import("node:vm")
  const buf = await readFile(new URL("../../wasm/writ.wasm", import.meta.url))
  const expected = kernel.version()
  assert.equal((await loadKernel({ wasm: buf })).version(), expected)
  assert.equal((await loadKernel({ wasm: new Uint8Array(buf) })).version(), expected)
  const padded = new Uint8Array(buf.length + 8)
  padded.set(buf, 4)
  assert.equal((await loadKernel({ wasm: padded.subarray(4, 4 + buf.length) })).version(), expected)
  const ab = runInNewContext(`new ArrayBuffer(${buf.length})`) as ArrayBuffer
  assert.equal(ab instanceof ArrayBuffer, false)
  new Uint8Array(ab).set(buf)
  assert.equal((await loadKernel({ wasm: ab })).version(), expected)
})

test("inputs over MAX_INPUT_BYTES in total throw WritInputError before calling in", () => {
  assert.throws(() => kernel.canonical(JSON.stringify({ a: "x".repeat(MAX_INPUT_BYTES) })), WritInputError)
  const half = "x".repeat(MAX_INPUT_BYTES / 2)
  assert.throws(() => kernel.step(half, half, { type: "turn_end", seq: 1, time: 0, state_version: 0 }), WritInputError)
  // Multi-byte characters count as their UTF-8 bytes.
  assert.throws(() => kernel.canonical(JSON.stringify({ a: "\u00e9".repeat(MAX_INPUT_BYTES / 2) })), WritInputError)
  assert.equal(kernel.version(), fixture("version.out").trim())
})

interface Memory { readonly buffer: ArrayBuffer; grow(pages: number): number }
type Exports = Record<string, unknown>
// The package compiles without DOM types, so the few WebAssembly names used here are typed locally.
const Wasm = (globalThis as unknown as {
  WebAssembly: {
    Memory: abstract new (...args: never[]) => Memory
    instantiate(bytes: Uint8Array, imports: unknown): Promise<{ instance: { exports: Exports } }>
  }
}).WebAssembly

/** A memory whose growth stops at `max` bytes, so the module runs out of memory early. */
function capped(memory: Memory, max: number): Memory {
  return new Proxy(memory, {
    get(target, key) {
      if (key === "grow") {
        return (pages: number) => {
          if (target.buffer.byteLength + pages * 65536 > max) throw new RangeError("test memory ceiling")
          return target.grow(pages)
        }
      }
      const v = Reflect.get(target, key, target) as unknown
      return typeof v === "function" ? (v as (...a: unknown[]) => unknown).bind(target) : v
    },
  })
}

test("an abort inside the module kills that kernel and leaves process.exitCode alone", async () => {
  const { readFile } = await import("node:fs/promises")
  const bytes = await readFile(new URL("../../wasm/writ.wasm", import.meta.url))
  const instantiateWasm = (imports: unknown, done: (i: { exports: Exports }) => void) => {
    void Wasm.instantiate(bytes, imports).then(({ instance }) => {
      const exports: Exports = { ...instance.exports }
      for (const [k, v] of Object.entries(exports)) {
        if (v instanceof Wasm.Memory) exports[k] = capped(v, 64 * 1024 * 1024)
      }
      done({ exports })
    })
    return {}
  }
  const stderr: string[] = []
  const { kernel: small } = await loadKernelWithMemory({ moduleOptions: { instantiateWasm, printErr: (s: string) => stderr.push(s) } })
  assert.equal(small.version(), kernel.version())
  const exitCode = process.exitCode
  // Parsing costs about 50 heap bytes per input byte, so 2 MB is far over a 64 MiB memory.
  const big = JSON.stringify({ a: "x".repeat(2_000_000) })
  const isAborted = (e: unknown) => {
    assert.ok(e instanceof WritKernelError, String(e))
    assert.equal(e.message, "kernel aborted; load a new kernel")
    assert.notEqual(e.cause, undefined)
    return true
  }
  assert.throws(() => small.canonical(big), isAborted)
  const seen = process.exitCode
  process.exitCode = exitCode
  assert.equal(seen, exitCode)
  assert.ok(stderr.join("\n").includes("out of memory"), stderr.join("\n"))
  assert.throws(() => small.version(), isAborted)
  assert.throws(() => small.check(shop), isAborted)
  assert.equal(kernel.canonical('{"b":1,"a":2}'), '{"a":2,"b":1}')
})
