import { parseStrict } from "./canonical.js"
import { WritInputError } from "./errors.js"
import { MAX_INPUT_BYTES } from "./kernel.js"

// base64url of the 32-byte HMAC-SHA256 tag, unpadded
const MAC_CHARS = 43

/** The longest sealed text `open` reads: a MAC, a dot and the base64url of a state up to `MAX_INPUT_BYTES`. */
export const MAX_SEALED_CHARS = Math.ceil(MAX_INPUT_BYTES * 4 / 3) + 44

/** The session and version the server holds as current; `open` refuses a sealed state that names others. */
export interface OpenExpect { sessionId: string; stateVersion: number }

// Spelled through globalThis so it resolves to the consumer's own WebCrypto types (DOM or Node).
export type HmacKey = Parameters<typeof globalThis.crypto.subtle.sign>[1]

function b64u(bytes: Uint8Array): string {
  let bin = ""
  for (let i = 0; i < bytes.length; i += 0x8000) bin += String.fromCharCode(...bytes.subarray(i, i + 0x8000))
  return btoa(bin).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "")
}

function fromB64u(s: string, what: string): Uint8Array {
  if (!/^[A-Za-z0-9_-]*$/.test(s) || s.length % 4 === 1) throw new WritInputError(`${what} is not base64url`)
  const bin = atob(s.replace(/-/g, "+").replace(/_/g, "/"))
  const bytes = Uint8Array.from(bin, (c) => c.charCodeAt(0))
  // Refuses other spellings of the same bytes, so each sealed value has exactly one valid text.
  if (b64u(bytes) !== s) throw new WritInputError(`${what} is not canonical base64url`)
  return bytes
}

function hmacKey(key: HmacKey): HmacKey {
  const alg = key?.algorithm as { name?: string; hash?: { name?: string } } | undefined
  if (alg?.name !== "HMAC" || alg.hash?.name !== "SHA-256") throw new WritInputError("expected an HMAC SHA-256 key")
  return key
}

/** `base64url(HMAC-SHA256(state)) + "." + base64url(utf8(state))`. */
export async function seal(stateText: string, key: HmacKey): Promise<string> {
  if (typeof stateText !== "string" || !stateText.isWellFormed()) {
    throw new WritInputError("state must be a string without lone surrogates")
  }
  const body = new TextEncoder().encode(stateText)
  if (body.length > MAX_INPUT_BYTES) {
    throw new WritInputError(`state is ${body.length} UTF-8 bytes, over the limit of ${MAX_INPUT_BYTES}`)
  }
  const mac = new Uint8Array(await globalThis.crypto.subtle.sign("HMAC", hmacKey(key), body))
  return `${b64u(mac)}.${b64u(body)}`
}

/**
 * Verifies and decodes a sealed state. Sealing gives integrity, not freshness: pass `expect` with the
 * session's latest `state_version` from the server to refuse a replayed older state. A null `expect`
 * counts as absent.
 */
export async function open(sealed: string, key: HmacKey, expect?: OpenExpect): Promise<string> {
  if (expect != null && (typeof expect !== "object" || Array.isArray(expect))) {
    throw new WritInputError("expected an object with sessionId and stateVersion, or nothing", "expect")
  }
  if (typeof sealed !== "string") throw new WritInputError("sealed state is malformed")
  // Bounded before split or decode so a forged blob costs nothing before the MAC check.
  if (sealed.length > MAX_SEALED_CHARS) {
    throw new WritInputError(`sealed state is ${sealed.length} characters, over the limit of ${MAX_SEALED_CHARS}`)
  }
  const dot = sealed.indexOf(".")
  if (dot < 0 || sealed.indexOf(".", dot + 1) >= 0) throw new WritInputError("sealed state is malformed")
  if (dot !== MAC_CHARS) throw new WritInputError("sealed MAC has the wrong length")
  const mac = fromB64u(sealed.slice(0, dot), "sealed MAC")
  const body = fromB64u(sealed.slice(dot + 1), "sealed state")
  // subtle.verify compares in constant time.
  if (!await globalThis.crypto.subtle.verify("HMAC", hmacKey(key), mac, body)) {
    throw new WritInputError("sealed state does not match its MAC")
  }
  let text: string
  try {
    text = new TextDecoder("utf-8", { fatal: true }).decode(body)
  } catch {
    throw new WritInputError("sealed state is not UTF-8")
  }
  if (expect != null) checkFresh(text, expect)
  return text
}

function checkFresh(text: string, expect: OpenExpect): void {
  const v = parseStrict(text, "state")
  const state = typeof v === "object" && v !== null && !Array.isArray(v) ? v as Record<string, unknown> : {}
  if (state["session_id"] !== expect.sessionId) {
    throw new WritInputError(
      `sealed state is for session ${JSON.stringify(state["session_id"])}, expected ${JSON.stringify(expect.sessionId)}`)
  }
  if (state["state_version"] !== expect.stateVersion) {
    throw new WritInputError(
      `sealed state has state_version ${JSON.stringify(state["state_version"])}, expected ${expect.stateVersion}; it is stale or replayed`)
  }
}
