# LangGraph replay

This is an example, not a published adapter: it drives the `langgraph-resume` corpus traces
(`corpus/examples/langgraph-resume.jsonl`) through a real LangGraph.js graph gated by `@anijani/writ`,
and checks that the gate answers each event as the trace pins it.

`graph.mjs` exports `buildGraph(gate, sessionId, { tools })`, a compiled `StateGraph` with a
`MemorySaver` checkpointer and one `tools` node. The node proposes every tool call of the step through
the gate. If any call needs approval, it calls `interrupt({ pending: [{ callId, requestId, callDigest
}, ...] })` before running anything: the calls of a step wait until every approval in it is answered,
because LangGraph discards the messages of a pass that pauses, and the model would never learn that a
tool ran. The caller approves through the gate (`gate.approve` or `gate.reject`), as an approval plane
would, and resumes with `graph.invoke(new Command({ resume }), config)`. LangGraph restarts the node
from its start, so every call is proposed again, and the node pauses again while any call still awaits
approval. In a pass where nothing awaits approval, the node dispatches the calls the gate allowed, at
most once per call id; a tool runs only when its dispatch is claimed, and the node reports its result. A
tool that throws is reported `outcomeUnknown`, not `result failed`, because a throw does not prove the
tool had no effect: the call keeps its reservation until a `reconcile` settles it, and the model gets
the tool's error as `outcome unknown: <message>`. A call whose tool is missing is not dispatched. A call
that is refused, at propose or at dispatch, is reported from the status the gate recorded for it:
`already dispatched: succeeded` for a call that ran, `not run: cancelled` or `not run: rejected` for one
that never did, with one message per call id. The trade-off of waiting: an approved call held back by its
siblings' approvals can pass its authorized TTL and then be denied `authorization_expired`.

There are two kinds of test.

`test/graph.test.mjs` resumes with a plain `new Command({ resume })`, so the re-run proposes the calls
LangGraph checkpointed. `a resume without an update re-proposes the checkpointed call` shows the repeat
answered `authorized`, one claim and one tool run, and `the graph pauses again while a second call
awaits approval` approves one of two calls and gets a second interrupt listing the other, with
neither run until both are answered. `a tool that throws after its dispatch is claimed is reported outcome
unknown` shows the `outcomeUnknown` report and the Unknown status, and `a tool error survives an outcome
report that throws` keeps the tool's error in the message when that report fails too.

`test/replay.test.mjs` replays the four `langgraph-resume` traces and compares each gate answer with the
trace's `expect`. It sends the control events (`session_start`, `turn_start`, `turn_end`, `step_start`,
`approve`, `reject`) through the gate itself; `propose`, `dispatch` and `result` come only from the
graph. Here every resume carries the trace's next step as a state update (`new Command({ resume,
update })`), so the calls proposed on resume are supplied by the trace, not read from the checkpoint.
The update also lists the calls to dispatch when the trace dispatches something other than the allowed
calls. The gate's clock returns each event's time.

What the replay shows:

- **The re-run on resume.** The resumed node proposes the deploy again, the kernel answers
  `authorized`, and the deploy runs once (`approval-hours-later`).
- **A resume delivered twice.** A second worker resumes from the same interrupted checkpoint while the
  deploy runs. Its propose answers `existing`, so a node that trusts it would not dispatch; the test
  forces the dispatch anyway, the gate refuses it `call_dispatched`, and the tool runs once.
- **The argument swap.** If the arguments of an approved call are swapped before the resume
  (Loopjacking, arXiv 2609.21081), the re-run proposes the same call id with another digest, which the
  kernel rejects `duplicate_call`. The trace dispatches the swapped digest anyway, to show that the
  dispatch check holds on its own when an adapter ignores the propose answer: it is refused
  `digest_mismatch`, so nothing runs that the reviewer did not see (`argument-swap`).

## Run it

Node 20 or later. Build the package first; the WebAssembly kernel must already be in
`packages/writ/wasm/` (see `build/wasm/README.md`).

```sh
cd packages/writ && npm run build
cd ../../examples/langgraph && npm install && npm test
```

The dependencies are pinned to `@langchain/langgraph` 1.4.19, `@langchain/core` 1.2.14 and `zod`
3.25.76, and the lockfile was resolved with `npm install --before=2026-10-06T00:00:00Z`. This directory
is not part of the `@anijani/writ` package and is not run in CI, which cannot build the kernel.
