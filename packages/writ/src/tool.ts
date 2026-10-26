import { canonicalizeWith } from "./canonical.js"
import type { NumberRule } from "./canonical.js"
import { sha256 } from "./digest.js"
import { WritInputError } from "./errors.js"

const MAX_SIGNIFICANT_DIGITS = 15

function significantDigits(printed: string): number {
  const mantissa = printed.replace(/^-/, "").split("e")[0]!.replace(".", "")
  return mantissa.replace(/^0+/, "").replace(/0+$/, "").length
}

// A double that came from a literal of at most 15 significant digits prints as that literal, normalized,
// so these checks refuse exactly what the Lean parser refuses for such literals.
const toolNumber: NumberRule = (n, path) => {
  if (Number.isNaN(n)) throw new WritInputError("NaN is not a JSON value", path)
  if (n === 0) return "0"
  const printed = String(n)
  // Digits before range, in Lean's order, so a number breaking both rules gets the same error.
  if (Number.isFinite(n) && significantDigits(printed) > MAX_SIGNIFICANT_DIGITS) {
    throw new WritInputError(`number has more than ${MAX_SIGNIFICANT_DIGITS} significant digits`, path)
  }
  const abs = Math.abs(n)
  if (abs > 1e300 || abs < 1e-300) throw new WritInputError("number is outside 1e-300 to 1e300 in magnitude", path)
  return printed
}

/** The canonical `writ.tool.v1` preimage of an MCP tool definition, every member included. */
export function toolPreimage(tool: unknown): string {
  if (tool === null || typeof tool !== "object" || Array.isArray(tool)) throw new WritInputError("expected a tool object")
  if (!Object.hasOwn(tool, "name")) throw new WritInputError("missing field", "name")
  if (typeof (tool as Record<string, unknown>)["name"] !== "string") throw new WritInputError("expected a string", "name")
  const body = canonicalizeWith(tool, toolNumber)
  // "t" sorts before "tool", and the tool's own error paths stay rooted at the tool.
  return `{"t":"writ.tool.v1","tool":${body}}`
}

/** `writ-tool-v1`: `"sha256:"` plus the lowercase hex SHA-256 of `toolPreimage(tool)`. */
export async function toolDigest(tool: unknown): Promise<string> {
  return sha256(toolPreimage(tool))
}
