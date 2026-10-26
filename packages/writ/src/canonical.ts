import { WritInputError } from "./errors.js"

export const MAX_DEPTH = 128

const child = (path: string, key: string): string => (path === "" ? key : `${path}.${key}`)

function checkNumber(n: number, path: string): void {
  if (!Number.isFinite(n)) throw new WritInputError("number is not finite", path)
  if (Object.is(n, -0)) throw new WritInputError("negative zero is not allowed", path)
  if (Number.isInteger(n) && Math.abs(n) > Number.MAX_SAFE_INTEGER) {
    throw new WritInputError("integer outside plus or minus 2^53 - 1 (carry it as a string)", path)
  }
}

const ESCAPES: Record<string, string> = {
  '"': '\\"', "\\": "\\\\", "\b": "\\b", "\f": "\\f", "\n": "\\n", "\r": "\\r", "\t": "\\t",
}

function quote(s: string, path: string, what: string): string {
  if (!s.isWellFormed()) throw new WritInputError(`${what} contains a lone surrogate`, path)
  return `"${s.replace(/["\\\u0000-\u001f]/g, (c) =>
    ESCAPES[c] ?? `\\u${c.charCodeAt(0).toString(16).padStart(4, "0")}`)}"`
}

/** Prints a number, or throws `WritInputError` at `path`. */
export type NumberRule = (n: number, path: string) => string

const callNumber: NumberRule = (n, path) => {
  checkNumber(n, path)
  return String(n)
}

function write(value: unknown, path: string, depth: number, omitUndefined: boolean, num: NumberRule): string {
  switch (typeof value) {
    case "string": return quote(value, path, "string")
    case "number": return num(value, path)
    case "boolean": return value ? "true" : "false"
    case "undefined": throw new WritInputError("undefined is not a JSON value", path)
    case "bigint": throw new WritInputError("BigInt is not a JSON value (carry it as a string)", path)
    case "function": throw new WritInputError("function is not a JSON value", path)
    case "symbol": throw new WritInputError("symbol is not a JSON value", path)
  }
  if (value === null) return "null"
  const obj = value as object
  const proto = Object.getPrototypeOf(obj) as unknown
  if (Array.isArray(obj)) {
    if (proto !== Array.prototype) throw new WritInputError("array subclass is not a plain array", path)
    if (depth >= MAX_DEPTH) throw new WritInputError(`nesting deeper than ${MAX_DEPTH} levels`, path)
    // The loop reads only indices, so it would drop a named property from what is signed; holes are refused here too.
    if (Object.keys(obj).length !== obj.length) throw new WritInputError("array has holes or extra properties", path)
    const parts: string[] = []
    for (let i = 0; i < obj.length; i++) parts.push(write(obj[i], `${path}[${i}]`, depth + 1, omitUndefined, num))
    return `[${parts.join(",")}]`
  }
  if (proto !== Object.prototype && proto !== null) {
    throw new WritInputError("only plain objects are JSON values (no Date, Map or class instances)", path)
  }
  if (Object.getOwnPropertySymbols(obj).length > 0) throw new WritInputError("object has a symbol key", path)
  if (depth >= MAX_DEPTH) throw new WritInputError(`nesting deeper than ${MAX_DEPTH} levels`, path)
  const record = obj as Record<string, unknown>
  const parts: string[] = []
  // Default string order is by UTF-16 code unit, which is what RFC 8785 requires.
  for (const k of Object.keys(record).sort()) {
    const value = record[k]
    if (value === undefined && omitUndefined) continue
    const p = child(path, k)
    parts.push(`${quote(k, p, "object key")}:${write(value, p, depth + 1, omitUndefined, num)}`)
  }
  return `{${parts.join(",")}}`
}

/**
 * RFC 8785 canonical JSON with I-JSON checks. Error paths look like `items[3].name`; `root` prefixes them.
 * `omitUndefined` drops object properties that are undefined, as JSON.stringify does; it is for events, not tool arguments.
 */
export function canonicalize(value: unknown, root = "", opts: { omitUndefined?: boolean } = {}): string {
  return write(value, root, 0, opts.omitUndefined === true, callNumber)
}

/** `canonicalize` with another number rule, for digests other than `writ-call-v1`. */
export function canonicalizeWith(value: unknown, num: NumberRule, root = ""): string {
  return write(value, root, 0, false, num)
}

const LITERAL = /^(-?)([0-9]+)(?:\.([0-9]+))?(?:[eE]([+-]?[0-9]+))?$/

// value = digits * 10^exp with no leading or trailing zeros in digits
function decimal(text: string): string {
  const m = LITERAL.exec(text)!
  const digits = m[2]! + (m[3] ?? "")
  let exp = Number(m[4] ?? 0) - (m[3] ?? "").length
  let start = 0
  while (start < digits.length && digits[start] === "0") start++
  let end = digits.length
  while (end > start && digits[end - 1] === "0") end--
  exp += digits.length - end
  const trimmed = digits.slice(start, end)
  return trimmed === "" ? "0" : `${m[1]}${trimmed}e${exp}`
}

const SIMPLE_ESCAPES: Record<string, string> = {
  '"': '"', "\\": "\\", "/": "/", b: "\b", f: "\f", n: "\n", r: "\r", t: "\t",
}

const NUMBER = /-?(?:0|[1-9][0-9]*)(\.[0-9]+)?(?:[eE][+-]?[0-9]+)?/y

class Parser {
  i = 0
  constructor(readonly s: string, readonly root: string) {}

  fail(msg: string, path: string = this.root): never {
    throw new WritInputError(`${msg} at offset ${this.i}`, path)
  }

  ws(): void {
    while (this.i < this.s.length) {
      const c = this.s.charCodeAt(this.i)
      if (c === 0x20 || c === 0x09 || c === 0x0a || c === 0x0d) this.i++
      else break
    }
  }

  literal(word: string, v: unknown): unknown {
    if (!this.s.startsWith(word, this.i)) this.fail("invalid JSON")
    this.i += word.length
    return v
  }

  value(path: string, depth: number): unknown {
    this.ws()
    const c = this.s[this.i]
    if (c === "{") return this.object(path, depth)
    if (c === "[") return this.array(path, depth)
    if (c === '"') return this.string(path, "string")
    if (c === "t") return this.literal("true", true)
    if (c === "f") return this.literal("false", false)
    if (c === "n") return this.literal("null", null)
    if (c === "-" || (c !== undefined && c >= "0" && c <= "9")) return this.number(path)
    return this.fail(c === undefined ? "unexpected end of input" : "invalid JSON")
  }

  number(path: string): number {
    NUMBER.lastIndex = this.i
    const m = NUMBER.exec(this.s)
    if (m === null) this.fail("invalid number", path)
    const text = m[0]
    this.i += text.length
    const n = Number(text)
    checkNumber(n, path)
    if (decimal(text) !== decimal(String(n))) {
      throw new WritInputError("number has more precision than a double holds or does not round-trip; carry it as a string", path)
    }
    return n
  }

  string(path: string, what: string | null): string {
    this.i++
    let out = ""
    for (;;) {
      const c = this.s[this.i]
      if (c === undefined) this.fail("unterminated string", path)
      if (c === '"') { this.i++; break }
      if (c < " ") this.fail("unescaped control character in string", path)
      if (c !== "\\") { out += c; this.i++; continue }
      const e = this.s[this.i + 1]
      if (e !== undefined && e in SIMPLE_ESCAPES) { out += SIMPLE_ESCAPES[e]; this.i += 2; continue }
      if (e !== "u") this.fail("invalid escape", path)
      const hex = this.s.slice(this.i + 2, this.i + 6)
      if (!/^[0-9a-fA-F]{4}$/.test(hex)) this.fail("invalid \\u escape", path)
      out += String.fromCharCode(parseInt(hex, 16))
      this.i += 6
    }
    if (what !== null && !out.isWellFormed()) this.fail(`${what} contains a lone surrogate`, path)
    return out
  }

  array(path: string, depth: number): unknown[] {
    if (depth >= MAX_DEPTH) this.fail(`nesting deeper than ${MAX_DEPTH} levels`, path)
    this.i++
    const out: unknown[] = []
    this.ws()
    if (this.s[this.i] === "]") { this.i++; return out }
    for (;;) {
      out.push(this.value(`${path}[${out.length}]`, depth + 1))
      this.ws()
      const c = this.s[this.i++]
      if (c === "]") return out
      if (c !== ",") { this.i--; this.fail("expected , or ]") }
    }
  }

  object(path: string, depth: number): Record<string, unknown> {
    if (depth >= MAX_DEPTH) this.fail(`nesting deeper than ${MAX_DEPTH} levels`, path)
    this.i++
    const out: Record<string, unknown> = {}
    const seen = new Set<string>()
    this.ws()
    if (this.s[this.i] === "}") { this.i++; return out }
    for (;;) {
      this.ws()
      if (this.s[this.i] !== '"') this.fail("expected an object key")
      const keyStart = this.i
      const key = this.string(path, null)
      const p = child(path, key)
      if (!key.isWellFormed()) { this.i = keyStart; this.fail("object key contains a lone surrogate", p) }
      if (seen.has(key)) { this.i = keyStart; this.fail("duplicate key", p) }
      seen.add(key)
      this.ws()
      if (this.s[this.i++] !== ":") { this.i--; this.fail("expected :") }
      const v = this.value(p, depth + 1)
      // defineProperty so a key named __proto__ stays an own property
      Object.defineProperty(out, key, { value: v, enumerable: true, writable: true, configurable: true })
      this.ws()
      const c = this.s[this.i++]
      if (c === "}") return out
      if (c !== ",") { this.i--; this.fail("expected , or }") }
    }
  }
}

/** Parses raw argument text under the same limits as `canonicalize`, and rejects duplicate keys and trailing data. */
export function parseStrict(text: string, root = ""): unknown {
  if (typeof text !== "string") throw new WritInputError("expected JSON text", root)
  const p = new Parser(text, root)
  const v = p.value(root, 0)
  p.ws()
  if (p.i < text.length) p.fail("trailing data")
  return v
}
