# Vercel AI SDK

This example drives the real AI SDK (`ai` 7.0.135, with zod 4.6.5) through `@anijani/writ/ai-sdk`,
with `MockLanguageModelV4` from `ai/test` standing in for the model, so it needs no API key. Each test
gets a gate with a `MemoryStore`, a policy where `deleteFile` needs the user's approval, `readFile`, `progress`,
`count` and `schedule` need none, and `shell` is not listed, and a session started for `user:alice`. The tools are passed to `generateText` as
`writ.tools`, with `toolApproval: writ.toolApproval`.

`test/ai-sdk.test.mjs`:

- `approval flow`: the first `generateText` returns a `tool-approval-request` and runs nothing;
  `writ.pending()` lists the call with its input, `writ.approve` approves it in Writ, and after the app
  appends the `tool-approval-response` the next `generateText` runs the tool once.
- `control: without Writ the SDK runs the edited input`: plain SDK tools with
  `toolApproval: { deleteFile: "user-approval" }`. The approver is shown `/tmp/a.txt`, the history is
  edited to `/etc/passwd` before resuming, and the SDK deletes `/etc/passwd`. This is the attack the
  next tests stop.
- `an edited tool-call input before resuming does not run`: the same edit through Writ. The SDK runs
  `toolApproval` again on resume, the re-proposal of the approved call id with another digest is
  refused `duplicate_call`, and the SDK records `execution-denied` without running the tool. The call
  stays authorized for its original input.
- `an edited input fails at dispatch with digest_mismatch when the resume drops toolApproval`: the
  resume passes no `toolApproval`, which the SDK accepts for an already approved call. The wrapped
  `execute` still dispatches, the dispatch is refused `digest_mismatch`, and the model gets that as a
  tool error.
- `a replayed approved history runs the tool once`: the same approved history sent again is denied
  `writ: call already succeeded` at the approval re-check, and with `toolApproval` dropped it is refused
  `call_ended` at dispatch.
- `an SDK approval with no Writ approval runs nothing`: the app answers `approved: true` without calling
  `writ.approve`. The SDK goes on to execute, the dispatch is refused `call_awaiting`, and the call is
  still awaiting approval in Writ.
- `a streaming tool's yields reach the SDK` and `streamText passes every yield ... as a preliminary
  result`: an `async function*` tool runs after a claimed dispatch, every yield reaches the SDK (as
  preliminary `tool-result` parts in `streamText`), the call is still `dispatched` between yields, and it
  is `succeeded` only after the last.
- `an input that is not plain JSON is denied invalid_input and the turn goes on`: an integer above 2^53
  on `z.number()` and a schema transform that produces a `Date` are denied with
  `writ: invalid_input: <path>: ...` instead of aborting `generateText`.
- `two tool calls in one step each dispatch once`: the SDK runs both under `Promise.all`; each call is
  dispatched once and succeeds.
- `a server that rebuilds writTools per request approves with the input it showed`: three `writTools`
  instances on one gate and session, one per request. The approving instance has no pending entry and
  passes the stored `{ tool, input }` as `shown`; the resuming instance runs the tool once.
- `a tool the policy does not list is refused unknown_tool`: the model calls `shell`, `toolApproval`
  denies it with the kernel's `unknown_tool` message, and the tool never runs.

Run it after building the package and its WebAssembly (`scripts/build-wasm.sh`, then `npm run build`
in `packages/writ`):

```sh
npm install
npm test
```

The lockfile was installed with `npm install --before=2026-10-09T00:00:00Z`, so every dependency was
published on or before 2026-10-08.
