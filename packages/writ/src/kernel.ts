import { canonicalize } from "./canonical.js"
import { WritInputError, WritKernelError } from "./errors.js"
import type { CallStatus, CheckResult, ProfileResult, ReplayResult, SessionView, Verdict, WritEvent } from "./types.js"

export interface StateEnvelope { state: string; stateVersion: number; ledgerVersion: number }
export interface StepResult extends StateEnvelope {
  verdict: Verdict
  ledger: string
  changed: boolean
  ledgerChanged: boolean
}
export interface TombstoneResult { ledger: string; ledgerVersion: number; changed: boolean }

export interface Kernel {
  version(): string
  check(policyText: string): CheckResult
  digest(jsonText: string): string
  canonical(jsonText: string): string
  initial(policyText: string, digest?: string): StateEnvelope
  step(policyText: string, stateText: string, event: WritEvent): StepResult
  replay(tracesText: string): ReplayResult
  /** Sets or clears the ledger's tombstone; the version moves only when the flag changes. "" is the empty ledger. */
  tombstone(ledgerText: string, set: boolean): TombstoneResult
  /** A read-only view of a session, with meter usage counted at `time` (milliseconds). */
  inspect(policyText: string, stateText: string, time: number): SessionView
  /** A standards profile's view of a verdict (its envelope) or of a call status (its disposition). */
  profile(id: string, input: { verdict: Verdict } | { status: CallStatus }): ProfileResult
}

interface Module {
  HEAPU8: Uint8Array
  HEAPU32: Uint32Array
  _malloc(n: number): number
  _free(p: number): void
  _writ_init(): number
  _writ_call(fn: number, a: number, an: number, b: number, bn: number, c: number, cn: number, out: number): number
  _writ_free(p: number): void
  _writ_heap_used(): number
}

type Factory = (opts: Record<string, unknown>) => Promise<Module>

const FN = { check: 1, digest: 2, canonical: 3, initial: 4, step: 5, replay: 6, version: 7, tombstone: 8, inspect: 9, profile: 10 } as const

/** The kernel's `input` name of each argument, mapped to the wrapper's parameter name. */
const INPUT_PATHS: Record<string, string> = {
  policy: "policyText", state: "stateText", event: "event", ledger: "ledgerText",
  traces: "tracesText", json: "jsonText", digest: "digest", time: "time",
}

/** `profile` sends one JSON document built from its two parameters. */
const PROFILE_PATHS: Record<string, string> = { profile: "id", json: "input" }

/**
 * The most UTF-8 bytes one kernel call takes, summed over its inputs. The heap stops at 2 GiB.
 * At 8 MiB the WebAssembly memory peaked at 500 MB (about 60 bytes per input byte, the
 * memory's growth steps included), under a quarter of the ceiling, which leaves room for the
 * result, for fragmentation and for a long-lived heap.
 */
export const MAX_INPUT_BYTES = 8 * 1024 * 1024

// dist/src/kernel.js sits two levels below the package root, which holds wasm/.
const wasmDir = new URL("../../wasm/", import.meta.url)

async function readBytes(source: URL | string): Promise<ArrayBuffer> {
  const url = typeof source === "string" ? new URL(source, import.meta.url) : source
  if (url.protocol === "file:") {
    const { readFile } = await import("node:fs/promises")
    const buf = await readFile(url)
    return buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength) as ArrayBuffer
  }
  const res = await fetch(url)
  if (!res.ok) throw new Error(`cannot load ${url.href}: ${res.status}`)
  return res.arrayBuffer()
}

function text(s: string, name: string): Uint8Array {
  if (!s.isWellFormed()) throw new WritInputError("string contains a lone surrogate", name)
  return new TextEncoder().encode(s)
}

const decoder = new TextDecoder("utf-8", { fatal: true })

const EMPTY = new Uint8Array(0)

const own = (e: unknown): boolean => e instanceof WritKernelError || e instanceof WritInputError

function makeKernel(m: Module): Kernel {
  if (m._writ_init() !== 0) throw new Error("writ_init failed")
  // Set once the module throws: after a trap or an abort its memory is in an unknown state.
  let dead: { cause: unknown } | undefined
  const aborted = (cause: unknown) => new WritKernelError("kernel aborted; load a new kernel", { cause })

  const callIn = (fn: number, a: Uint8Array, b: Uint8Array, c: Uint8Array): string => {
    const bufs = [a, b, c]
    const ptrs: number[] = []
    let outLen = 0
    let result = 0
    let failure: { error: unknown } | undefined
    // ALLOW_MEMORY_GROWTH makes malloc return 0 instead of aborting
    const alloc = (n: number): number => {
      const p = m._malloc(n)
      if (p === 0) throw new WritKernelError("out of WebAssembly memory")
      return p
    }
    try {
      outLen = alloc(4)
      for (const buf of bufs) ptrs.push(alloc(Math.max(buf.length, 1)))
      // malloc can grow memory, so the view is read only after the last one
      bufs.forEach((buf, i) => m.HEAPU8.set(buf, ptrs[i]!))
      result = m._writ_call(fn, ptrs[0]!, a.length, ptrs[1]!, b.length, ptrs[2]!, c.length, outLen)
      if (result === 0) throw new WritKernelError(`writ_call(${fn}) returned NULL`)
      const n = m.HEAPU32[outLen >> 2]!
      return decoder.decode(m.HEAPU8.slice(result, result + n))
    } catch (e) {
      failure = { error: e }
      throw e
    } finally {
      // Freeing into a heap the module abandoned could trap again and hide the first error.
      if (failure === undefined || own(failure.error)) {
        if (result !== 0) m._writ_free(result)
        for (const p of ptrs) m._free(p)
        if (outLen !== 0) m._free(outLen)
      }
    }
  }

  const call = (fn: number, a: Uint8Array, b: Uint8Array = EMPTY, c: Uint8Array = EMPTY): string => {
    if (dead !== undefined) throw aborted(dead.cause)
    const total = a.length + b.length + c.length
    if (total > MAX_INPUT_BYTES) {
      throw new WritInputError(`inputs total ${total} UTF-8 bytes, over the limit of ${MAX_INPUT_BYTES}`)
    }
    try {
      return callIn(fn, a, b, c)
    } catch (e) {
      if (own(e)) throw e
      dead = { cause: e }
      throw aborted(e)
    }
  }

  const envelope = (out: string, paths: Record<string, string> = INPUT_PATHS): Record<string, unknown> => {
    const env = JSON.parse(out) as Record<string, unknown>
    if ("error" in env) {
      const input = env["input"]
      if (typeof input === "string") {
        throw new WritInputError(String(env["error"]), Object.hasOwn(paths, input) ? paths[input]! : input)
      }
      throw new WritKernelError(String(env["error"]))
    }
    return env
  }

  const stateEnvelope = (env: Record<string, unknown>): StateEnvelope => ({
    state: env["state"] as string,
    stateVersion: env["state_version"] as number,
    ledgerVersion: env["ledger_version"] as number,
  })

  return {
    version: () => call(FN.version, EMPTY),
    check: (policyText) => envelope(call(FN.check, text(policyText, "policyText"))) as unknown as CheckResult,
    digest: (jsonText) => envelope(call(FN.digest, text(jsonText, "jsonText")))["digest"] as string,
    canonical: (jsonText) => envelope(call(FN.canonical, text(jsonText, "jsonText")))["canonical"] as string,
    initial: (policyText, digest) =>
      stateEnvelope(envelope(call(FN.initial, text(policyText, "policyText"), text(digest ?? "", "digest")))),
    step(policyText, stateText, event) {
      const env = envelope(call(
        FN.step, text(policyText, "policyText"), text(stateText, "stateText"), text(canonicalize(event, "event", { omitUndefined: true }), "event"),
      ))
      return {
        ...stateEnvelope(env),
        verdict: env["verdict"] as Verdict,
        ledger: env["ledger"] as string,
        changed: env["changed"] as boolean,
        ledgerChanged: env["ledger_changed"] as boolean,
      }
    },
    replay: (tracesText) => envelope(call(FN.replay, text(tracesText, "tracesText"))) as unknown as ReplayResult,
    tombstone(ledgerText, set) {
      const env = envelope(call(FN.tombstone, text(ledgerText, "ledgerText"), text(set ? "1" : "0", "set")))
      return {
        ledger: env["ledger"] as string,
        ledgerVersion: env["ledger_version"] as number,
        changed: env["changed"] as boolean,
      }
    },
    inspect(policyText, stateText, time) {
      if (!Number.isSafeInteger(time) || time < 0) {
        throw new WritInputError("expected a non-negative integer of milliseconds", "time")
      }
      return envelope(call(
        FN.inspect, text(policyText, "policyText"), text(stateText, "stateText"), text(String(time), "time"),
      )) as unknown as SessionView
    },
    profile(id, input) {
      if (typeof id !== "string") throw new WritInputError("expected a string", "id")
      const doc = canonicalize({ ...input, profile: id }, "input", { omitUndefined: true })
      return envelope(call(FN.profile, text(doc, "input")), PROFILE_PATHS) as ProfileResult
    },
  }
}

export type WasmSource = ArrayBuffer | ArrayBufferView | URL | string

// Tag checks, not instanceof, so buffers from another realm (vm, worker, iframe) work.
function asBytes(wasm: WasmSource): ArrayBuffer | undefined {
  if (ArrayBuffer.isView(wasm)) {
    return new Uint8Array(wasm.buffer, wasm.byteOffset, wasm.byteLength).slice().buffer
  }
  if (Object.prototype.toString.call(wasm) === "[object ArrayBuffer]") return wasm as ArrayBuffer
  return undefined
}

/** `moduleOptions` go to the Emscripten factory as they are; tests use them to shape the instance. */
export async function loadKernelWithMemory(opts: { wasm?: WasmSource; moduleOptions?: Record<string, unknown> } = {}):
  Promise<{ kernel: Kernel; memoryBytes(): number; heapUsed(): number }> {
  const wasm = opts.wasm
  const wasmBinary = (wasm !== undefined && asBytes(wasm)) ||
    await readBytes((wasm ?? new URL("writ.wasm", wasmDir)) as URL | string)
  const glue = new URL("writ.mjs", wasmDir).href
  const factory = (await import(glue) as { default: Factory }).default
  // The default quit sets process.exitCode in Node, which would outlive an abort the caller caught.
  const m = await factory({
    ...opts.moduleOptions, wasmBinary, quit: (_status: number, toThrow: unknown) => { throw toThrow },
  })
  return { kernel: makeKernel(m), memoryBytes: () => m.HEAPU8.length, heapUsed: () => m._writ_heap_used() }
}

export async function loadKernel(opts: { wasm?: WasmSource } = {}): Promise<Kernel> {
  return (await loadKernelWithMemory(opts)).kernel
}
