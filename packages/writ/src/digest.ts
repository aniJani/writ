import { canonicalize } from "./canonical.js"
import { WritInputError } from "./errors.js"

export interface CallInput {
  server: string
  tool: string
  toolDigest: string
  args?: unknown
  cost?: { amount: string; currency: string } | null
}

function str(v: unknown, path: string): string {
  if (typeof v !== "string") throw new WritInputError("expected a string", path)
  return v
}

/** The canonical `writ-call-v1` preimage. Execute these bytes, not the original arguments. */
export function callPreimage(call: CallInput): string {
  if (call === null || typeof call !== "object") throw new WritInputError("expected a call object")
  let cost: { amount: string; currency: string } | null = null
  if (call.cost !== undefined && call.cost !== null) {
    const c = call.cost as Record<string, unknown>
    if (typeof c !== "object" || Array.isArray(c)) throw new WritInputError("expected an object", "cost")
    for (const k of Object.keys(c)) {
      if (k !== "amount" && k !== "currency") throw new WritInputError("unknown field", `cost.${k}`)
    }
    cost = { amount: str(c["amount"], "cost.amount"), currency: str(c["currency"], "cost.currency") }
  }
  const args = canonicalize(call.args === undefined ? {} : call.args, "args")
  const rest = canonicalize({
    t: "writ.call.v1",
    server: str(call.server, "server"),
    tool: str(call.tool, "tool"),
    tool_digest: str(call.toolDigest, "toolDigest"),
    cost,
  })
  // "args" sorts before every other key, and the depth limit counts from args itself.
  return `{"args":${args},${rest.slice(1)}`
}

/** `"sha256:"` plus the lowercase hex SHA-256 of the UTF-8 bytes of `text`. */
export async function sha256(text: string): Promise<string> {
  const hash = new Uint8Array(await globalThis.crypto.subtle.digest("SHA-256", new TextEncoder().encode(text)))
  return "sha256:" + Array.from(hash, (b) => b.toString(16).padStart(2, "0")).join("")
}

export async function callDigest(call: CallInput): Promise<string> {
  return sha256(callPreimage(call))
}
