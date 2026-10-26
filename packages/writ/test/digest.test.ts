import assert from "node:assert/strict"
import { readdirSync, readFileSync } from "node:fs"
import { join } from "node:path"
import { test } from "node:test"
import { fixture, repoRoot } from "./helpers.js"
import { callDigest, callPreimage, canonicalize, loadKernel, parseStrict, WritInputError } from "../src/index.js"
import type { WritEvent } from "../src/index.js"

interface Vector {
  id: string
  input: { server: string; tool: string; tool_digest: string; args_text?: string; args?: unknown; cost?: { amount: string; currency: string } | null }
  canonical?: string
  digest?: string
  error?: { path: string }
}

const vectors = readFileSync(join(repoRoot, "corpus/digests/call-v1.jsonl"), "utf8")
  .split("\n").filter((l) => l !== "").map((l) => JSON.parse(l) as Vector)

const callOf = (v: Vector) => ({
  server: v.input.server,
  tool: v.input.tool,
  toolDigest: v.input.tool_digest,
  ...(v.input.args_text !== undefined ? { args: parseStrict(v.input.args_text, "args") } : "args" in v.input ? { args: v.input.args } : {}),
  ...("cost" in v.input ? { cost: v.input.cost ?? null } : {}),
})

const kernel = await loadKernel()

// Raw argument text is spliced in as is, so Lean sees duplicate keys, escapes and spellings the parser saw.
const leanText = (v: Vector): string => {
  const args = v.input.args_text ?? JSON.stringify(v.input.args ?? {})
  return `{"t":"writ.call.v1","server":${JSON.stringify(v.input.server)},"tool":${JSON.stringify(v.input.tool)},` +
    `"tool_digest":${JSON.stringify(v.input.tool_digest)},"args":${args},"cost":${JSON.stringify(v.input.cost ?? null)}}`
}

// Lean reads -0 as the integer 0; the call digest rejects it on purpose.
// Lean counts depth over the whole preimage, so args nested 128 deep is 129 there; 1.0 and 1E2 are not integer spellings.
const leanSkips = new Set(["depth-128", "num-1.0", "num-1E2"])
const leanAccepts = new Set(["err-neg-zero"])

const integerOnly = (x: unknown): boolean =>
  typeof x === "number" ? Number.isInteger(x)
    : Array.isArray(x) ? x.every(integerOnly)
      : x !== null && typeof x === "object" ? Object.values(x).every(integerOnly) : true

for (const v of vectors) {
  if (v.error !== undefined) {
    test(`digest vector ${v.id} is rejected`, async () => {
      await assert.rejects(async () => callDigest(callOf(v)), (e: unknown) => {
        assert.ok(e instanceof WritInputError, String(e))
        assert.equal(e.path, v.error!.path)
        return true
      })
      if (v.input.args_text !== undefined && !leanAccepts.has(v.id)) {
        assert.throws(() => kernel.canonical(leanText(v)), v.id)
      }
    })
  } else {
    test(`digest vector ${v.id}`, async () => {
      const call = callOf(v)
      assert.equal(callPreimage(call), v.canonical)
      assert.equal(await callDigest(call), v.digest)
      const args = call.args ?? {}
      if (integerOnly(args) && !leanSkips.has(v.id)) {
        assert.equal(kernel.canonical(leanText(v)), v.canonical)
      }
    })
  }
}

const rejects = (f: () => unknown, path: string) =>
  assert.throws(f, (e: unknown) => {
    assert.ok(e instanceof WritInputError, String(e))
    assert.equal(e.path, path)
    return true
  })

test("hostile JS values throw WritInputError with a path", () => {
  const cyclic: Record<string, unknown> = {}
  cyclic["self"] = cyclic
  class Point { x = 1 }
  const cases: [string, unknown, string][] = [
    ["NaN", { n: Number.NaN }, "n"],
    ["Infinity", [1, Infinity], "[1]"],
    ["-Infinity", { a: { b: -Infinity } }, "a.b"],
    ["-0", { items: [0, 1, 2, -0] }, "items[3]"],
    ["2^53", { n: 2 ** 53 }, "n"],
    ["-2^53", [-(2 ** 53)], "[0]"],
    ["1e21", { n: 1e21 }, "n"],
    ["undefined in object", { items: [{ a: 1 }, { name: undefined }] }, "items[1].name"],
    ["undefined in array", [1, undefined], "[1]"],
    ["sparse array", { a: [1, , 3] }, "a"],
    ["BigInt", { n: 1n }, "n"],
    ["function", { f: () => 1 }, "f"],
    ["symbol", { s: Symbol("x") }, "s"],
    ["symbol key", { [Symbol("k")]: 1 }, ""],
    ["Date", { d: new Date(0) }, "d"],
    ["class instance", { p: new Point() }, "p"],
    ["Map", new Map(), ""],
    ["Number object", { n: new Number(1) }, "n"],
    ["lone surrogate", { s: "\ud800" }, "s"],
    ["lone surrogate key", { ["\udc00"]: 1 }, "\udc00"],
    ["undefined with omitUndefined off", { audit: undefined }, "audit"],
    ["cycle", cyclic, Array(128).fill("self").join(".")],
  ]
  for (const [name, value, path] of cases) {
    assert.throws(() => canonicalize(value), (e: unknown) => {
      assert.ok(e instanceof WritInputError, name)
      assert.equal(e.path, path, name)
      return true
    })
  }
})

test("canonicalize accepts depth 128 and rejects 129, for arrays and objects", () => {
  const nest = (n: number, leaf: unknown, wrap: (x: unknown) => unknown) => {
    let v = leaf
    for (let i = 0; i < n; i++) v = wrap(v)
    return v
  }
  assert.doesNotThrow(() => canonicalize(nest(128, 1, (x) => [x])))
  assert.doesNotThrow(() => canonicalize(nest(128, 1, (x) => ({ a: x }))))
  rejects(() => canonicalize(nest(129, 1, (x) => [x])), "[0]".repeat(128))
  rejects(() => canonicalize(nest(129, 1, (x) => ({ a: x }))), Array(128).fill("a").join("."))
})

test("canonicalize refuses arrays with extra properties", () => {
  const extra: unknown[] & { x?: number } = [1]
  extra.x = 2
  assert.throws(() => canonicalize(extra), /array has holes or extra properties/)
  assert.throws(() => canonicalize([1, , 3]), /array has holes or extra properties/)
  rejects(() => canonicalize({ list: extra }), "list")
  assert.equal(canonicalize([1, 2]), "[1,2]")
})

test("canonicalize prefixes error paths with the root", () => {
  rejects(() => canonicalize({ a: [undefined] }, "event"), "event.a[0]")
})

test("canonicalize output for plain values", () => {
  assert.equal(canonicalize({ b: [1, "x", null, true], a: { d: 0.5, c: "" } }), '{"a":{"c":"","d":0.5},"b":[1,"x",null,true]}')
  assert.equal(canonicalize(Object.create(null, { k: { value: 1, enumerable: true } })), '{"k":1}')
  assert.equal(canonicalize(1e-7), "1e-7")
  assert.equal(canonicalize(123456789.125), "123456789.125")
})

test("parseStrict keeps a __proto__ key as data", () => {
  const v = parseStrict('{"__proto__":{"x":1}}') as Record<string, unknown>
  assert.equal(Object.getPrototypeOf(v), Object.prototype)
  assert.equal(canonicalize(v), '{"__proto__":{"x":1}}')
})

test("parseStrict rejects non-string input and lone surrogates in the text", () => {
  rejects(() => parseStrict(5 as unknown as string, "args"), "args")
  rejects(() => parseStrict('"\ud800"', "args"), "args")
})

test("callDigest normalizes undefined args to {} and validates its fields", async () => {
  const base = { server: "s", tool: "t", toolDigest: "d" }
  assert.equal(await callDigest(base), await callDigest({ ...base, args: undefined }))
  assert.equal(await callDigest(base), await callDigest({ ...base, args: {}, cost: null }))
  await assert.rejects(callDigest({ ...base, args: { n: Number.NaN } }), (e: unknown) => e instanceof WritInputError && e.path === "args.n")
  await assert.rejects(callDigest({ ...base, server: "\ud800" }), (e: unknown) => e instanceof WritInputError && e.path === "server")
  await assert.rejects(callDigest({ ...base, cost: { amount: "1" } as never }), (e: unknown) => e instanceof WritInputError && e.path === "cost.currency")
  await assert.rejects(callDigest({ ...base, cost: { amount: "1", currency: "USD", extra: 1 } as never }), (e: unknown) => e instanceof WritInputError && e.path === "cost.extra")
})

test("kernel.step drops undefined event fields like JSON.stringify but keeps undefined in arrays an error", () => {
  const policy = fixture("policies/simple.json")
  const [first, second] = fixture("oracle-events.jsonl").split("\n").slice(0, 2).map((l) => JSON.parse(l) as WritEvent)
  const state = kernel.step(policy, kernel.initial(policy).state, first!).state
  const turn = second!
  const base = kernel.step(policy, state, turn)
  const withUndef = kernel.step(policy, state, { ...turn, audit: undefined, cost: undefined } as WritEvent)
  assert.deepEqual(withUndef, base)
  assert.throws(() => kernel.step(policy, state, { ...turn, audit: [undefined] } as never),
    (e: unknown) => e instanceof WritInputError && e.path === "event.audit[0]")
  assert.equal(canonicalize({ a: undefined, b: 1 }, "", { omitUndefined: true }), '{"b":1}')
})

test("callDigest and callPreimage reject a null or non-object call", async () => {
  for (const bad of [null, undefined, 5, "x"]) {
    await assert.rejects(callDigest(bad as never), WritInputError)
    assert.throws(() => callPreimage(bad as never), WritInputError)
  }
})

test("kernel.step serializes events with canonicalize", () => {
  const policy = '{"writ":"0.1"}'
  const state = kernel.initial(policy).state
  const bad = { type: "session_start", n: 1n } as never
  assert.throws(() => kernel.step(policy, state, bad), (e: unknown) => e instanceof WritInputError && e.path === "event.n")
  const cyc: Record<string, unknown> = {}
  cyc["c"] = cyc
  assert.throws(() => kernel.step(policy, state, cyc as never), WritInputError)
})

test("canonicalize equals kernel.canonical on every integer-only CLI policy", () => {
  const dir = join(repoRoot, "tests/cli/policies")
  let compared = 0
  for (const f of readdirSync(dir).filter((n) => n.endsWith(".json"))) {
    const text = readFileSync(join(dir, f), "utf8")
    let want: string
    try { want = kernel.canonical(text) } catch { continue }
    assert.equal(canonicalize(parseStrict(text)), want, f)
    compared++
  }
  assert.ok(compared >= 10, `compared ${compared}`)
})

test("parseStrict reports a raw lone surrogate at its nested path", () => {
  rejects(() => parseStrict('{"a":{"s":"\ud800"}}', "args"), "args.a.s")
})

test("parseStrict handles a 1 MB number literal with an inner zero run in linear time", () => {
  for (const text of ["0.1" + "0".repeat(1_000_000) + "1", "1" + "0".repeat(1_000_000), "0." + "0".repeat(1_000_000)]) {
    const t0 = performance.now()
    try { parseStrict(text, "args") } catch (e) { assert.ok(e instanceof WritInputError) }
    assert.ok(performance.now() - t0 < 200, `took ${performance.now() - t0} ms`)
  }
})

test("a number that does not round-trip is refused with advice to carry it as a string", () => {
  for (const text of ["0.10000000000000001", "0.1000000000000000055511151231257827021181583404541015625", "9007199254740991.2"]) {
    assert.throws(() => parseStrict(`[${text}]`, "args"), (e: unknown) => {
      assert.ok(e instanceof WritInputError, String(e))
      assert.equal(e.message, "args[0]: number has more precision than a double holds or does not round-trip; carry it as a string")
      return true
    }, text)
  }
  assert.deepEqual(parseStrict("[1.0, 1E2, 100e-2, 4.50]"), [1, 100, 1, 4.5])
})
