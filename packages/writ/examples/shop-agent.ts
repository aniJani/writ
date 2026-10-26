import { randomUUID } from "node:crypto"
import { callDigest, createGate, loadKernel, MemoryStore } from "@anijani/writ"

const policyText = JSON.stringify({
  writ: "0.1",
  approver_roles: ["owner"],
  meters: { spend: { currency: "USD", cap: 5000, scope: "principal", window_ms: 86_400_000 } },
  limits: { approval_ttl_ms: 600_000 },
  actions: {
    "shop.search": { consent: "none" },
    "shop.buy": { consent: "per_call", meters: ["spend"] },
  },
})
const gate = createGate({ kernel: await loadKernel(), policyText, store: new MemoryStore() })
const s = randomUUID()
const show = (what: string, r: { verdict: { verdict: string; decision?: string } }) =>
  console.log(`${what}: ${r.verdict.verdict} ${r.verdict.decision ?? ""}`.trimEnd())

show("start", await gate.start({
  sessionId: s, requester: "user:alice", permissions: [], userInitiated: true,
  approvers: { "alice-laptop": { principal: "user:alice", kind: "human", roles: ["owner"] } },
}))
show("step", await gate.stepStart(s))

const call = (tool: string, args: object, cost?: { amount: string; currency: string }) =>
  ({ server: "shop", tool, toolDigest: "sha256:tool-v1", args, cost })
const searchDigest = await callDigest(call("shop.search", { q: "tea" }))
const search = await gate.propose(s, { callId: "c1", tool: "shop.search", callDigest: searchDigest })
console.log(`propose search: ${search.kind}`)
const d1 = await gate.dispatch(s, { callId: "c1", callDigest: searchDigest })
show("dispatch search", d1)
if (!d1.claimed) throw new Error("dispatch refused, do not run the tool")
show("result search", await gate.result(s, { callId: "c1", outcome: "succeeded" }))

// "1999" is 19.99 USD: amounts are integer minor units, written as decimal strings.
const cost = { amount: "1999", currency: "USD" }
const buyDigest = await callDigest(call("shop.buy", { sku: "tea-100", qty: 2 }, cost))
const buy = await gate.propose(s, { callId: "c2", tool: "shop.buy", callDigest: buyDigest, cost })
console.log(`propose buy: ${buy.kind}`)
if (buy.kind !== "needs_approval") throw new Error("no approval request")
show("approve buy", await gate.approve(s, {
  callId: "c2", requestId: buy.requestId, approverId: "alice-laptop", reviewedDigest: buyDigest, reviewedCost: cost,
}))
const d2 = await gate.dispatch(s, { callId: "c2", callDigest: buyDigest, cost })
show("dispatch buy", d2)
if (!d2.claimed) throw new Error("dispatch refused, do not run the tool")
show("result buy", await gate.result(s, { callId: "c2", outcome: "succeeded", actualCost: "1999" }))
