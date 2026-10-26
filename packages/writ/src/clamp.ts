import type { WritEvent } from "./types.js"

const amount = /^(0|[1-9][0-9]*)$/

/**
 * Spec sections 6 and 10: a report from an untrusted executor never releases a reservation,
 * never commits less than it, and cannot claim a decline that did not come through the
 * trusted approval renderer. `reservation` is the call's current cost amount in state.
 */
export function clampUntrusted(event: WritEvent, opts: { trustedDecline: boolean; reservation?: string }): WritEvent {
  if (event.type !== "result" && event.type !== "reconcile") return event
  const out = { ...event, no_effect: false }
  if (out.outcome === "declined" && !opts.trustedDecline) out.outcome = "failed"
  const r = opts.reservation
  // A malformed amount is left for the kernel to reject.
  if (r !== undefined && out.actual_cost !== undefined && amount.test(r) && amount.test(out.actual_cost) &&
    BigInt(out.actual_cost) < BigInt(r)) {
    out.actual_cost = r
  }
  return out
}
