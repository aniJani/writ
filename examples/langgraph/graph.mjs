import { Annotation, END, interrupt, MemorySaver, START, StateGraph } from "@langchain/langgraph"
import { ToolMessage } from "@langchain/core/messages"

const replace = (_, next) => next

const State = Annotation.Root({
  /** The tool calls of this step: `{ callId, tool, args?, callDigest }`. */
  calls: Annotation({ reducer: replace, default: () => [] }),
  /** The calls to dispatch, or null for the calls the gate allowed. */
  dispatch: Annotation({ reducer: replace, default: () => null }),
  messages: Annotation({ reducer: (a, b) => a.concat(b), default: () => [] }),
})

const message = (call, content, status) =>
  new ToolMessage({ tool_call_id: call.callId, name: call.tool, content, status })

const RAN = new Set(["dispatched", "succeeded", "failed", "declined", "unknown"])

/** The message a recorded call status gives the model, or null while the call is still undecided. */
function statusLabel(status) {
  if (status === undefined || status === "awaiting" || status === "authorized") return null
  if (typeof status === "object") return [`not run: ${status.status} ${status.reason}`, "error"]
  if (RAN.has(status)) return [`already dispatched: ${status}`, status === "succeeded" ? "success" : "error"]
  return [`not run: ${status}`, "error"]
}

/**
 * A graph whose `tools` node gates every tool call. The node proposes each call. If any call needs
 * approval it interrupts with `{ pending: [{ callId, requestId, callDigest }, ...] }` before running
 * anything, and the caller approves through the gate before resuming. LangGraph re-runs the whole node
 * on resume, so every call is proposed again; the node pauses again while any call still awaits
 * approval. Only in a pass where nothing awaits approval does it dispatch the calls the gate allowed,
 * and a tool runs only when its dispatch is claimed.
 */
export function buildGraph(gate, sessionId, { tools = {} } = {}) {
  async function gated(state) {
    const proposed = []
    for (const call of state.calls) {
      const p = await gate.propose(sessionId, { callId: call.callId, tool: call.tool, callDigest: call.callDigest })
      proposed.push({ call, p })
    }
    const pending = proposed
      .filter(({ p }) => p.kind === "needs_approval")
      .map(({ call, p }) => ({ callId: call.callId, requestId: p.requestId, callDigest: call.callDigest }))
    // A pass that pauses loses its messages, so it runs nothing. interrupt() matches resume values by
    // position: on a re-run the first calls return the answers to earlier pauses, and the first
    // position without an answer throws, which pauses the graph again.
    if (pending.length > 0) for (;;) interrupt({ pending })
    // One message per call id, the latest winning, so a pass never contradicts itself. A refusal is
    // labelled from the call's recorded status: the same refusal reason covers calls that ran and calls
    // that never did.
    const messages = new Map()
    const say = (call, content, status) => messages.set(call.callId, message(call, content, status))
    const sayRecorded = async (call, fallback) => {
      const view = await gate.inspect(sessionId)
      const label = statusLabel(view?.calls.find((c) => c.call_id === call.callId)?.status)
      say(call, ...(label ?? [fallback, "error"]))
    }
    for (const { call, p } of proposed) {
      if (p.kind !== "allowed") await sayRecorded(call, `not run: ${p.kind} ${p.reason ?? p.verdict.reason ?? ""}`.trim())
    }
    const allowed = new Map()
    for (const { call, p } of proposed) if (p.kind === "allowed" && !allowed.has(call.callId)) allowed.set(call.callId, call)
    for (const call of state.dispatch ?? [...allowed.values()]) {
      const tool = tools[call.tool]
      if (tool === undefined) {
        say(call, `not run: no tool ${call.tool}`, "error")
        continue
      }
      const d = await gate.dispatch(sessionId, { callId: call.callId, callDigest: call.callDigest })
      if (!d.claimed) {
        await sayRecorded(call, `not run: dispatch ${d.verdict.verdict} ${d.reason ?? ""}`.trim())
        continue
      }
      let out
      try {
        out = await tool(call.args ?? {})
      } catch (e) {
        // A throw does not prove the tool had no effect, so the call goes Unknown: its reservation stays
        // and `reconcile` settles it once the outcome is known. If this report fails too, the call stays
        // dispatched for `outcomeUnknown` or `reconcile` later, and the model still gets the tool's error.
        await gate.outcomeUnknown(sessionId, call.callId).catch(() => {})
        say(call, `outcome unknown: ${e instanceof Error ? e.message : String(e)}`, "error")
        continue
      }
      await gate.result(sessionId, { callId: call.callId, outcome: "succeeded" })
      say(call, String(out), "success")
    }
    return { messages: [...messages.values()], dispatch: null }
  }

  return new StateGraph(State)
    .addNode("tools", gated)
    .addEdge(START, "tools")
    .addEdge("tools", END)
    .compile({ checkpointer: new MemorySaver() })
}
