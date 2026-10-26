# @anijani/writ

TypeScript package for Writ, the policy kernel for tool-using AI agents. The kernel decides whether a proposed tool call may run, needs people to approve it, or is refused, and it records what happened afterwards: dispatch, results, retries, meters, grants, kill and escalation. It is the Lean kernel compiled to WebAssembly. Theorems 1 to 12 of the spec are proved over that kernel in Lean, within the limits the repository README's proof status gives; the WebAssembly build and this package's own code are tested, not proved. This package adds a typed wrapper, call digests, a gate that persists sessions through a store, sealed state for client-carried sessions, and a Firestore store. It has no runtime dependencies and works with any agent framework, because it only decides what a tool call may do and records what happened.

This page is enough to use the package. For depth, the repository has the spec (`docs/design.md`) and the JSON formats (`docs/formats.md`).

## Install

```sh
npm install @anijani/writ
```

Until the package is published on npm, build it from the repository instead, then use it there or install the tarball elsewhere:

1. Build the WebAssembly from the repository root: `scripts/build-wasm.sh`. It needs `emcc` 6.0.12, the Lean toolchain from `lean-toolchain`, node, git with sparse-checkout, network access to github.com, and a path without spaces. `build/wasm/README.md` in the repository has the details.
2. Build the package:

```sh
cd packages/writ
npm install
npm run build
```

3. To use it in another project, pack it and install the tarball. The tarball carries the compiled code and the kernel (`wasm/writ.wasm` and `wasm/writ.mjs`); `scripts/pack-check.sh` in the repository checks its file list and installs it into an empty project.

```sh
npm pack                     # in packages/writ, after npm run build; writes anijani-writ-0.1.0-preview.1.tgz
cd /path/to/my-agent && npm install /path/to/writ/packages/writ/anijani-writ-0.1.0-preview.1.tgz
```

Node 20 or later is required. `npm test` stops with a message if `wasm/writ.mjs` or `wasm/writ.wasm` is missing. In the repository it also stops when `wasm/writ.source`, the hash of the kernel sources the build wrote, does not match the current tree, so a stale build is never tested.

Size and speed, measured on 2026-10-25 on an arm64 Mac with Node 26: `writ.wasm` is 2,215,471 bytes raw and 392,943 bytes gzipped (the build is deterministic and fails above 3 MB). The npm tarball, measured by `scripts/pack-check.sh` on 2026-10-25 with Node 26, is 510,292 bytes (2,640,996 bytes unpacked; the packed size varies a little with the zlib of the Node that packs it). A kernel step takes about 0.2 ms for a small state, including parsing the policy and the state, and the time grows linearly with the size of the state; see [Limits](#limits).

## Quick start

`@anijani/writ/simple` is the shortest way in: name your tools, say which need the user's approval, and run them. It is a convenience over a normal policy and a normal gate, not a different kernel or policy format, so the kernel's checks and proved theorems apply to it unchanged. `examples/hello.ts` is this program; after `npm run build`, run `node dist/examples/hello.js`.

```ts
import { simpleGate } from "@anijani/writ/simple"

const askUser = async (question: string) => { console.log(`ask: ${question}`); return true }
const w = await simpleGate({ user: "user:alice", tools: { web_search: "none", send_email: "per_call" } })
const s = await w.session()

const search = await s.propose("web_search", { q: "tea" })
console.log("search:", await s.run(search, async () => "3 results"))

let email = await s.propose("send_email", { to: "bob@example.com", body: "Tea at four?" })
if (email.status === "needs_approval" && await askUser("Email bob@example.com?")) email = await s.approve(email)
console.log("email:", await s.run(email, async () => "sent"))
```

The tool map becomes an ordinary layer-1 policy. For this example `w.policyText` is:

```json
{"writ":"0.1","approver_roles":["user"],"limits":{"approval_ttl_ms":600000},"actions":{"web_search":{"consent":"none"},"send_email":{"consent":"per_call"}}}
```

`simplePolicy(tools, { approvalTtlMs })` returns that text on its own. Each `session()` starts a gate session for `user` with no permissions, the user as its only approver (approver id `"user"`, role `"user"`) and a user-initiated first turn. `propose` mints a call id and digests `{ server: "local", tool, toolDigest: "unversioned", args }`; `status` is `allowed`, `needs_approval` or `denied`, with the kernel's `reason` when there is one (a tool missing from the map is denied `unknown_tool`). `approve` and `reject` answer for the user and return the updated call. When the kernel refuses the answer, the call keeps the refusal's `reason` and reports where it really stands: still `needs_approval` with its `requestId` (a wrong digest, `digest_mismatch`), `allowed` (already approved, `call_authorized`) or `denied` (ended, rejected, or expired: an answer after the TTL also ends the request). `requestId` is opaque; `JSON.parse` gives the gate's `RequestId`. `run` dispatches the call and runs your function only if the dispatch is claimed: it then reports `succeeded` and returns `{ ran: true, value }`, or, if the function throws, reports the outcome unknown and rethrows. A call that was not claimed returns `{ ran: false, reason }` without running, for example `call_awaiting` before approval and `call_ended` once the call has run or been rejected.

`w.gate` is a normal `Gate`: `kill`, `inspect`, `end` and the other methods work on simple sessions as they are. Meters, quorums and grants are policy fields, so for those edit `w.policyText`, build your own gate with `createGate`, and pass the old text as `retiredPolicyTexts` (see [Policy changes](#policy-changes)); the rest of this page then applies. Keep in mind that the simple path's approver id is `"user"` and its call digests use `server: "local"` and `toolDigest: "unversioned"`.

## Load the kernel and check a policy

```ts
import { loadKernel } from "@anijani/writ"

const kernel = await loadKernel()
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
const report = kernel.check(policyText)
if (!report.ok) throw new Error(report.errors.map((e) => `${e.code}: ${e.message}`).join("; "))
for (const w of report.warnings) console.warn(`${w.code}: ${w.message}`)
console.log(report.policy_digest)
```

A policy is JSON. Tools not listed in `actions` are denied. Each action can name a `permission`, a `consent` (`"none"` by default), `meters`, `guards` (host-checked preconditions), retry settings, TTLs and more; `docs/formats.md` lists every field. `check` returns `{ ok, errors, warnings, policy_digest }`. Errors make the policy unusable; warnings flag settings that do less than they seem to, among them `meter_without_cap`, `principal_meter_without_window`, `per_call_above_cap` and `retry_without_attempts`.

`loadKernel()` reads `wasm/writ.wasm` and imports `wasm/writ.mjs`, both found relative to the compiled `dist/src/kernel.js`. `loadKernel({ wasm })` takes the module bytes as an `ArrayBuffer` or typed array, or a `URL` or string to fetch them from. Besides `check`, a `Kernel` has `digest` and `canonical` (of any JSON text), `initial`, `step`, `replay` (of conformance traces), `tombstone(ledgerText, set)`, `inspect(policyText, stateText, time)` and `profile(id, input)` ([The MCP SEP-2848 profile](#the-mcp-sep-2848-profile)). State crosses the boundary as an opaque string, the canonical `writ.state/1` text. The gate below is the usual way to drive `step`.

## Run a gate

A gate steps one session at a time against a `Store` and commits every accepted step before it returns. `examples/shop-agent.ts` is this walk-through as a runnable program; after `npm run build`, run `node dist/examples/shop-agent.js`.

```ts
import { randomUUID } from "node:crypto"
import { callDigest, createGate, loadKernel, MemoryStore } from "@anijani/writ"

const gate = createGate({ kernel: await loadKernel(), policyText, store: new MemoryStore() })
const sessionId = randomUUID()

await gate.start({
  sessionId,
  requester: "user:alice",           // the principal the session acts for
  permissions: [],
  approvers: {
    "alice-laptop": { principal: "user:alice", kind: "human", roles: ["owner"] },
  },
  userInitiated: true,               // also starts the first turn
})
await gate.stepStart(sessionId)      // one per model response

// A free call: propose, dispatch, run, report.
const search = { server: "shop", tool: "shop.search", toolDigest: "sha256:tool-v1", args: { q: "tea" } }
const searchDigest = await callDigest(search)
const p1 = await gate.propose(sessionId, { callId: "c1", tool: "shop.search", callDigest: searchDigest })
if (p1.kind === "allowed") {
  const d = await gate.dispatch(sessionId, { callId: "c1", callDigest: searchDigest })
  if (d.claimed) {
    // run the tool now, then report what happened
    await gate.result(sessionId, { callId: "c1", outcome: "succeeded" })
  }
}

// A call that needs approval and spends money.
const cost = { amount: "1999", currency: "USD" }  // 19.99 USD
const buy = { server: "shop", tool: "shop.buy", toolDigest: "sha256:tool-v1", args: { sku: "tea-100", qty: 2 }, cost }
const buyDigest = await callDigest(buy)
const p2 = await gate.propose(sessionId, { callId: "c2", tool: "shop.buy", callDigest: buyDigest, cost })
if (p2.kind === "needs_approval") {
  // show the call to the approver in a trusted renderer, then:
  await gate.approve(sessionId, {
    callId: "c2", requestId: p2.requestId, approverId: "alice-laptop",
    reviewedDigest: buyDigest, reviewedCost: cost,
  })
  const d = await gate.dispatch(sessionId, { callId: "c2", callDigest: buyDigest, cost })
  if (d.claimed) {
    // run the tool, then report what it actually charged
    await gate.result(sessionId, { callId: "c2", outcome: "succeeded", actualCost: "1999" })
  }
}
```

Three kinds of name appear here, and they are different things:

- **Principal** (`"user:alice"`): the human or system identity. The session's `requester` is a principal, and so is each approver's `principal`. Principal meters, the principal ledger and `killPrincipal` are keyed by it. Quorum counts distinct principals.
- **Approver id** (`"alice-laptop"`): the session's name for one attested approver, the key of `approvers`. Approval methods take it as `approverId`. Once attested, an id can never be pointed at another principal, kind or roles in the same session (rejected `approver_changed`).
- **Role** (`"owner"`): what an approver may approve. Roles come from the policy's `approver_roles`, and consent clauses name them.

The gate's input fields are camelCase; the events it builds keep the kernel's snake_case names (`approverId` becomes `approver`).

`call_id`s are yours to mint, unique within the session; do not reuse the model's tool-call id, which can change on retry.

### Gate methods

| Method | Event | Use |
|---|---|---|
| `start({ sessionId, requester, permissions, approvers, userInitiated? })` | `session_start` | starts a session; with `userInitiated` also its first turn |
| `turnStart(id, userInitiated)`, `turnEnd(id)` | `turn_start`, `turn_end` | a turn is one user message and the agent's work on it |
| `stepStart(id)` | `step_start` | one per model response |
| `propose(id, { callId, tool, callDigest, cost?, guards?, escalators? })` | `propose` | asks whether a call may run; returns `ProposeResult` |
| `approve(id, { callId, requestId, approverId, reviewedDigest, reviewedCost?, edit? })` | `approve` | one approver's approval; `edit` (`{ newDigest, newCost?, escalators? }`) changes the arguments and restarts the tally |
| `reject(id, { callId, requestId, approverId })` | `reject` | a veto: the call ends rejected |
| `approvalExpire(id, { callId, requestId })` | `approval_expire` | ends a request early |
| `grantCreate(id, {...})`, `grantRevoke(id, grantId)` | `grant_create`, `grant_revoke` | standing grants for `grantable` actions |
| `dispatch(id, { callId, callDigest, cost?, guards?, attempt?, idempotencyKey? })` | `dispatch` | claims the call immediately before it runs; returns `DispatchResult` |
| `result(id, { callId, outcome, actualCost?, noEffect? }, opts?)` | `result` | the outcome of a claimed call; returns `ReportResult` |
| `outcomeUnknown(id, callId)` | `outcome_unknown` | the outcome cannot be known |
| `reconcile(id, report, opts?)` | `reconcile` | the outcome of an Unknown call, learned later; returns `ReportResult` |
| `cancel(id, callId)` | `cancel` | withdraws a call that has not been dispatched |
| `escalationAck(id, { approverId, escalation })` | `escalation_ack` | clears an escalation |
| `permissionAdd(id, { permission, approverId })`, `permissionRevoke(id, permission)` | `permission_add`, `permission_revoke` | changes the session's permissions |
| `approverAttest(id, { approverId, principal, kind, roles })` | `approver_attest` | adds an approver mid-session |
| `reset(id)` | `reset` | starts a new epoch: awaiting and authorized calls are cancelled, dispatched calls become Unknown (settle them with `reconcile`; a retry `dispatch` is rejected `already_reconciled` once the call is reconciled, else `retry_not_allowed` when the action does not allow a retry after Unknown, else `stale_request`, because the epoch changed), and turn and session grants die |
| `kill(id)`, `end(id)` | `kill`, `session_end` | see [Kill](#kill) |
| `killPrincipal(principal)`, `clearPrincipalKill(principal)` | none (ledger only) | see [Kill](#kill) |
| `inspect(id)` | none (read only) | see [Crash recovery](#crash-recovery-with-inspect) |

Every method that steps returns at least a `GateResult`, `{ verdict, stateVersion, reason? }`. `verdict` is the kernel's verdict object; `stateVersion` is the version of the stored state after the call.

How it commits:

- The gate commits through a store that does compare-and-swap on the state version and on the version of the principal ledger the step read. Commit happens before effect: a method resolves only after its commit, so run a tool after `dispatch` resolves with `claimed: true`, never before.
- Refusals resolve; they do not throw. A rejected verdict comes back in the result and writes nothing. A denial is an accepted step: it is committed, and the call keeps its denied status. A propose of a tool the policy does not define is denied `unknown_tool` and counts against the proposal limits, but leaves no call record, so its call id stays unknown to later events.
- When two writers race on one session, one commit wins; the other reloads and steps again. After 5 conflicting commits in one call the call throws `WritConflictError`.
- A ledger conflict (another session of the same principal moved the ledger) makes the gate send a `ledger_sync` and retry. If the kernel refuses that sync with `ledger_conflict`, the gate commits a `session_end` and returns that rejected verdict: the session's state can no longer be reconciled with the ledger.
- The gate commits only an accepted step, or that forced `session_end`, even if the kernel reports `changed`.
- The gate sends `max(last_time, now)` as the event time, so a clock that goes backwards does not fail a step. `clock` (default `Date.now`) must return integer milliseconds; anything else throws `TypeError`.
- `dispatch` sends `idempotencyKey`, or else `defaultIdempotencyKey(principal, sessionId, callId)`, which is `H(principal, session_id, call_id)`: `"sha256:"` plus the hex SHA-256 of `canonicalize({ principal, session: sessionId, call: callId })`. It is the same on every attempt of a call, so pass it to the tool as its idempotency key. An explicit key must stay the same across attempts, or the retry is rejected `idempotency_key_mismatch`.

## What `kind`, `reason`, `claimed` and `overrun` mean

`propose` returns a `ProposeResult`, a `GateResult` with a `kind`:

| `kind` | Verdict it covers | What the host does |
|---|---|---|
| `allowed` | decision `allowed`, `allowed_by_grant` or `authorized`; or `existing` with status `authorized` | `dispatch`, then run the tool only if the dispatch is claimed |
| `needs_approval` | decision `needs_approval`; the result carries `requestId` | show the call to an approver, then `approve` or `reject` with that `requestId` |
| `denied` | decision `denied`; `existing` with any other status, `dispatched` included; any other decision | do not run the tool. `reason` says why; `status` is the call's status when the verdict is `existing` |
| `rejected` | a rejected verdict: the kernel refused the event itself | do not run the tool; `reason` says why |

A repeated `propose` of the same call (same `callId`, tool, digest and cost) changes nothing and reports where the call stands: `needs_approval` with the current `requestId` while it awaits approval, `allowed` once it is approved and not yet dispatched (`denied` instead if the authorization has since lapsed or the session was killed), `denied` once it has been dispatched or has ended. So a host that lost track of a call can simply propose it again. A `dispatched` call cannot be dispatched again; it is settled with `result`, `outcomeUnknown` or `reconcile`.

`reason` on any `GateResult` is the rejected verdict's reason, else a `denied` or `dispatch_denied` decision's reason, else the reason inside an `existing` status of `denied` or `denied_at_dispatch`. It is absent otherwise. The verdict also carries `retry`, which tells the model what to do next (`fix_request`, `never`, `after_user_action`, `next_turn`, `after_escalation`), and `message`, model-facing text written to stop retry loops. `REASONS` lists every reason code at run time, in the order of `schema/reasons.json`, and `RETRY_CLASSES` lists every retry class. `docs/formats.md` gives each code's retry class.

`dispatch` returns a `DispatchResult` with `claimed`, which is true only for a `dispatch_claimed` decision. Run the tool when `claimed` is true, and only then. A dispatch can be rejected for a transient reason (a guard that is now false, `meter_exceeded`), in which case the call is still authorized and may be dispatched later. A dispatch rejected `killed` is final (retry `never`): the kill cancelled the call if it was still authorized, and an Unknown call stays Unknown and can only be reconciled. A dispatch can also end the call with a `dispatch_denied` decision (the permission was revoked, the grant is no longer valid), in which case the call is over.

`result` and `reconcile` return a `ReportResult` with `overrun`: the meters on which an accepted report committed more than the reservation, in the order the action lists them, else `[]`.

## Turns and steps

Call `stepStart` once per model response, however many tool calls that response contains. The policy's `limits.max_steps_per_turn` counts these; past it `stepStart` is rejected `step_limit` (retry `next_turn`), and the host should stop calling the model for this turn. `turnStart` resets the per-turn counters. A turn started with `userInitiated: true` also clears the session's rejection memory: once a call is rejected, proposing the same tool with the same digest is denied `previously_rejected` until the user starts a turn, so the model cannot shop for a tired approver.

## Money

Amounts are integer minor units of the currency, written as decimal strings: `"1999"` is 19.99 USD, and `"500"` JPY is 500 yen. No sign, no leading zero, no fraction and no JSON number; at most 78 digits. `"6.00"` or `19.99` throws `WritInputError`. A cost is `{ amount, currency }`; `actualCost` on a report is an amount alone, in the cost's currency. In the policy, a meter's `cap` and `max_per_call` are plain JSON integers in the same minor units (`cap: 5000` is 50.00 USD). A `"unit": "calls"` meter counts one per dispatched call instead. Meter usage from `inspect` is in decimal strings too.

An action with a money meter must declare its cost on `propose` (else `cost_missing`), and the same cost on `dispatch`; every money meter of one action shares one currency.

## What a report does

Meters are reserved at dispatch and settled by the report. Failures are counted per tool (consecutive) and per session (total); when the policy's `max_consecutive_failures` or `max_failures_per_session` is reached, the session or tool is escalated and its proposals and dispatches are denied `escalated` until an `escalationAck`.

| Report | Meters | Failure counters |
|---|---|---|
| `result succeeded` | commit `actual_cost` (else the reservation); calls meters commit 1 | resets the tool's consecutive count |
| `result failed` | commit as above | tool +1, session +1 |
| `result declined` | release | unchanged |
| any report with `no_effect: true` | release | by its outcome |
| actual cost above the reservation | commit all of it, the excess dated at the report; decision `overrun` | counts as a failure |
| `outcome_unknown` | keep the reservation | tool +1, session +1 |
| `reconcile` on an Unknown call | as `result`, status stays `unknown` | only an overrun counts |

- A commit below the reservation is a partial capture and frees the difference. A release reports no overrun, whatever `actualCost` it carries.
- `declined` means a person stopped or declined the call after dispatch and before it took effect. Report it only when the tool had no effect; otherwise report the outcome you observed.
- A `result` on an Unknown call is rejected `call_unknown`: use `reconcile`, which is accepted once per call (a second is rejected `already_reconciled`). After `end`, `reconcile` is the only report the session accepts, and the gate resends a `result` there as `reconcile`, so either settles the call.
- Releases and partial captures trust the report. When the executor is not trusted (a user's device, a browser), pass `{ untrusted: true, trustedDecline }` to `result` or `reconcile`: the gate drops `noEffect`, commits at least the reservation, and turns `declined` into `failed` unless `trustedDecline` is true, meaning the decline came through your trusted approval renderer.

## Meters at propose and at dispatch

Meters are checked at propose and reserved at dispatch. `propose` denies a call whose cost would not fit (`meter_exceeded`) or is above `max_per_call` (`cost_above_per_call`), but it reserves nothing. The reservation happens at `dispatch`, all or nothing over the action's meters. So an approved call can still be refused `meter_exceeded` at dispatch when other calls reserved the room in between: the dispatch is rejected, the refusal is transient, and the call stays authorized, so it can be dispatched once there is room again. No reservation ever brings usage above a cap; usage can pass the cap only through a reported overrun. A meter without a `cap` never denies. A `principal` meter is shared by every session of the requester through the principal ledger; give it a `window_ms`, or its cap is a lifetime limit.

## Retries

A call that was dispatched can be dispatched again only after `outcomeUnknown`, and only if its action sets `idempotent: true`, `retry_after_unknown: true` and `max_attempts` of 2 or more (`writ check` warns when `retry_after_unknown` has `max_attempts` below 2). A failure is final: a `failed` result ends the call, and trying again means a new `propose` with a new `callId`, which is checked and approved afresh. A retry keeps the call's approval and idempotency key, reuses its reservation while that reservation is inside the meter's window, and must still be within the action's `authorized_ttl_ms`.

`attempt` on `dispatch` is optional. It defaults to the stored call's `attempts` plus one, read once per `dispatch` call: if the commit loses a race and the gate steps again, it keeps the attempt it first read, so it never claims a retry that another writer allowed in the meantime.

## Consent

`"per_call"` means one approval, from a human approver holding any of the policy's `approver_roles`, unless `roles` narrows it: `{ "quorum": 1, "roles": ["owner"] }` takes one approval from an owner. A clause can also ask for more people (`quorum: 2`), allow automated approvers (`human_only: false`), or exclude the requester (`exclude_requester: true`; by default the requester may approve their own call, as in the walk-through). `{ "all": [clause, ...], "distinct": true }` needs every clause met by different people. Any single eligible `reject` is a veto.

## Digests and costs are never defaulted

`approve` needs `reviewedDigest` (and `reviewedCost` on a metered action): the digest and cost of what the approver was shown. `dispatch` needs `callDigest` and `cost`: the digest and cost of what is about to run. The gate never fills these from the stored state. They are your evidence, from outside the kernel, of what was seen and what will execute; the kernel checks that they match the call, and that check catches arguments swapped between approval and execution. Copied from state, they would compare the state with itself and catch nothing. Compute them from the bytes your renderer showed and the bytes you are about to execute.

### Call digests

`callDigest` is the `writ-call-v1/RFC8785-JCS+SHA-256` digest of a call; `callPreimage` returns the canonical text that was hashed. The cost is part of the digest, so a changed price needs a new approval.

```ts
import { callDigest, callPreimage, canonicalize } from "@anijani/writ"

const call = { server: "shop", tool: "shop.buy", toolDigest: "sha256:tool-v1", args: { sku: "tea-100", qty: 2 }, cost: { amount: "1200", currency: "USD" } }
const digest = await callDigest(call)
const bytes = callPreimage(call)
// Send the tool the canonical args text, the "args" value inside `bytes`, never a re-serialized object:
const argsText = canonicalize(call.args ?? {})
const executed = bytes.startsWith(`{"args":${argsText},`) // true
```

`toolDigest` is your digest of the tool's definition, so a changed tool definition invalidates earlier approvals. Hostile input throws `WritInputError` and never produces a digest:

- JS values: `NaN`, `Infinity`, `-0`, a number whose magnitude is above 2^53 - 1 (so `1e21` too), `undefined` inside an object or array, an array with holes or extra properties, `BigInt`, functions, symbols, objects that are not plain (such as `Map`, `Date`, class instances and array subclasses), lone surrogates, and nesting deeper than 128.
- Raw text (`parseStrict`): all of those, plus duplicate keys, trailing data, and numbers whose exact decimal value differs from that of their shortest round-trip form (`0.10000000000000001` is refused; `1.0`, `1E2` and `100e-2` are accepted).

Carry large numbers and fractions you need exactly as strings. When the arguments arrive as text, for example the arguments string of a model's tool call, run that text through `parseStrict` and pass the result to `callDigest`. Do not use `JSON.parse`: it keeps the last of two duplicate keys and rounds numbers a double cannot hold, without an error, so the digest would cover other arguments than the ones the model sent.

```ts
import { callDigest, parseStrict } from "@anijani/writ"

const args = parseStrict(argumentsText, "args") // throws WritInputError on duplicate keys or lossy numbers
const digest = await callDigest({ server: "shop", tool: "shop.buy", toolDigest, args })
```

The test vectors for other languages are in `corpus/digests/call-v1.jsonl` in the repository.

### Tool digests

`toolDigest` is the `writ-tool-v1` digest of an MCP tool definition: the SHA-256 of the canonical JSON of `{"t": "writ.tool.v1", "tool": tool}`, with every member of the tool object as the server lists it. Pass it as `toolDigest` in each call. It is also what a policy records as an action's `source.tool_digest`, so a server that changes a tool's description or schema under the same name no longer matches the policy or the approvals given for the old definition. `toolPreimage` returns the canonical text that was hashed.

```ts
import { toolDigest } from "@anijani/writ"

const { tools } = await client.listTools() // an MCP tools/list result
const digests = new Map(await Promise.all(tools.map(async (t) => [t.name, await toolDigest(t)] as const)))
```

Key order and whitespace do not change the digest. Numbers follow RFC 8785 with two limits, which keep the TypeScript and Lean digests equal: a number is printed only when its shortest form has at most 15 significant digits and its magnitude is 0 or within 1e-300 to 1e300. Any other number throws `WritInputError` with its path, as do `NaN`, `Infinity`, lone surrogates, values that are not plain JSON, nesting deeper than 128, and a tool that is not an object with a string `name`. `toolDigest` counts the 128 levels from the tool, while the `writ` command counts them from the tools.json document, so there a tool inside a `tools/list` result has two levels fewer.

`toolDigest` receives an object that is already parsed, so it cannot see what `JSON.parse` loses: a duplicate key keeps its last value, and a literal with 16 or more significant digits that rounds to a double with a shorter form is digested as that shorter form. The `writ` command reads the tools.json text and refuses both, so a tool whose number literals need more than 15 significant digits cannot be digested by writ's CLI, and its digest from `toolDigest` will not match anything `writ` writes. The test vectors are in `corpus/digests/tool-v1.jsonl` in the repository.

## Crash recovery with `inspect`

`inspect(sessionId)` returns the stored session as the kernel sees it at the gate's clock, or `null` when none is stored. It reads only, and it works under a retired policy too. A `SessionView` has `session_id`, `state_version`, `ledger_version`, `started`, `ended`, `killed`, `tombstone`, `escalated`, `escalations`, `blocked_tools`, `calls` and `meters`. Each call is `{ call_id, tool, status, digest, cost, attempts, generation, epoch }`, plus `request_id` while the call awaits approval; each meter is `{ meter, scope, used, cap, remaining }`.

After a crash, inspect each live session and settle its calls by status:

- `dispatched`: the call was claimed, so the tool may or may not have run. If the tool's own records (looked up by the idempotency key) tell you the outcome, report it with `result`; otherwise report `outcomeUnknown`. Never run it a second time on a guess.
- `authorized`: approved and not dispatched; it can be dispatched now.
- `awaiting`: propose the same call again; it answers `needs_approval` with the current `requestId`, to show the approver again.
- `unknown`: `reconcile` when you learn the outcome, or dispatch a retry if the action allows one.
- Anything else has ended; there is nothing to do.

`inspect` shows a call's digest, not its arguments. Dispatching or reporting after a crash needs the exact bytes to execute, so keep the canonical argument bytes (`callPreimage`) by call id in your own storage before you dispatch, and recompute the digest from them.

## Kill

- `kill(sessionId)` kills the session. Awaiting and authorized calls are cancelled. Afterwards the session accepts only `propose` (answered `denied killed`), `kill`, `end`, `result`, `outcomeUnknown` and `reconcile`; everything else, every `dispatch` included, is rejected `killed`. Dispatched calls still settle. With the policy's `kill_scope: "principal"`, a `kill` also sets the principal's tombstone. Deliver a kill with priority, and abort tools in flight where you can, then report their outcomes.
- `killPrincipal(principal)` sets the tombstone in the principal's stored ledger, without a session. Every live session of that principal learns of it at its next commit, through the gate's forced `ledger_sync`: its awaiting and authorized calls are cancelled and its next `dispatch` is rejected `killed`. New sessions of the principal start killed. It returns `{ ledgerVersion, changed }`; `changed` is false when the tombstone was already set.
- `clearPrincipalKill(principal)` clears the tombstone. Live sessions that saw it set are ended at their next commit: their sync fails with `ledger_conflict`, the gate commits `session_end`, which makes their dispatched calls Unknown, and returns that rejected verdict. When that commit was a `result` or `reconcile`, the gate then sends the same report once more as `reconcile` on the ended session (with the same `untrusted` clamp, computed from the ended session's state) and returns its verdict, so the call settles in one call. Once a session has ended, whether the gate ended it this way or you called `end`, the gate reports a `result` on it as `reconcile` in the same way, so keep calling `result` for the session's other dispatched calls (or call `reconcile` directly) and they settle. An `outcomeUnknown` is not resent, since the end already made the call Unknown; settle it later with `reconcile`, which syncs the cleared ledger and commits. Settle the remaining calls before you rely on the budget they free, and start new sessions.
- The ledger theorem (theorem 9) covers a clear: no session claims while the stored ledger carries the tombstone, and a session that saw it never claims again.
- Both take a principal that is a non-empty string of at most 512 UTF-8 bytes (else `WritInputError` with path `principal`), need `ledgerScope: "principal"` (else `WritInputError` with path `ledgerScope`), and throw `WritConflictError` after 5 conflicting ledger commits in a row.

`kill` and `end` have headroom in the state budget and run under a retired policy, but `kill` can still throw: a store error, a `WritConflictError`, a `WritKernelError`, a `WritPolicyChangedError` for a policy the gate does not list, or a `WritStateFullError` when the principal ledger the gate must sync in grew by more than the session's remaining headroom since the session last synced (or a `WritInputError` when the state, that ledger and the policy together pass `MAX_INPUT_BYTES`). If it throws, call `killPrincipal` with the session's principal (the `requester` you passed to `start`), which writes only the ledger record and so works whatever state the session is in, then `end(sessionId)`. `end` may itself throw `WritStateFullError` for the same reason; that is safe, because the tombstone already stops every dispatch of every session of that principal until you clear it.

## The state budget

Session state grows with every call, so the gate gives each session a byte budget, `maxStateBytes`. It defaults to the store's `maxStateBytes` if it has one, else `MAX_INPUT_BYTES / 2` (4 MiB), and is never set above the store's own limit (`FirestoreStore` has 900,000). Growth events (`start`, `propose`, `approve`, `grantCreate`, `approverAttest`, `permissionAdd` and `dispatch`) are refused once the stored state is above seven eighths of the budget; for `start`, the incoming principal ledger counts too. Everything else, `kill`, `end`, `result`, `outcomeUnknown`, `reconcile` and `cancel` among them, keeps the remaining eighth as headroom. A step whose new state would be above the whole budget is not committed.

Both refusals throw `WritStateFullError`, which carries `sessionId`, `bytes` (the size that did not fit) and `limit`: seven eighths of the budget when a growth event was refused before stepping, or the budget itself when a stepped state was too large. Nothing is committed. Settle the session's dispatched calls, `end` it, and start a new session with a new id; principal meters and the tombstone carry over through the ledger. Rotating sessions well before they fill up, for example every few hundred calls, avoids the error.

## Policy changes

A session runs under the policy it started with. `createGate` checks `policyText` and every entry of `retiredPolicyTexts` and throws `WritInputError` (path `policyText` or `retiredPolicyTexts[i]`) on the first policy with an error. A gate refuses to step a stored session whose policy digest is not its own with `WritPolicyChangedError`, which carries `sessionId` and the session's `policyDigest`.

To deploy a new policy, build the gate with the new `policyText` and pass the old texts as `retiredPolicyTexts`. A session started under a retired policy runs under that policy, but accepts only `end`, `kill`, `result`, `outcomeUnknown`, `reconcile` and `inspect`, so its dispatched calls still settle their meters; every other method throws `WritPolicyChangedError`. A session whose policy is neither current nor retired throws `WritPolicyChangedError` on every method, `inspect` included. End the old sessions and start new ones under the new policy; drop an old text from `retiredPolicyTexts` once no session uses it. Principal meters and tombstones carry over, because they live in the ledger; rejection memory, escalation and grants are per session and start empty.

Policies that share a principal ledger (the live policy and its retired ones, or two gates during a rolling deploy) must give each shared principal meter the same kind (money or calls), the same currency for a money meter, and the same `window_ms`. A ledger entry holds only the meter name and an amount, so a `spend` meter that is USD in one policy and EUR in another would add euros to dollars in one total. And each session prunes the ledger by its own policy's window: with different windows, one policy's sessions drop entries the other's still count. A session prunes the ledger only by its policy's principal meters, so a policy that has a session meter of the same name, or no meter of that name, never drops the entry; session meters share no ledger, so a session meter may reuse the name with any kind, currency or window. To change any of them, rename the meter (or, for a window, drain the old sessions first). `createGate` compares every pair among `policyText` and `retiredPolicyTexts`, and throws `WritInputError` (path `retiredPolicyTexts[j]`, the later policy of the pair, with a message naming the meter, the other policy and each property that differs) when two of them give a principal meter a different kind, currency or `window_ms` (no window and a window count as different); it cannot see a policy that another gate runs.

The ledger theorem (theorem 9) covers sessions of a live policy and retired ones, and of two gates' policies, that share a ledger, as long as their shared principal meters agree as above and every session stamps each commit from one trusted, monotone clock. `createGate` checks the meter agreement; the clock is the theorem's assumption, and a skewed clock can overspend (see the clock line of [the trust boundary](#the-trust-boundary)).

## Stores

A `Store` has four methods, all required, and an optional `maxStateBytes`:

- `load(sessionId)` and `loadLedger(principal)` read a record, or return `null`.
- `commit(c)` is one atomic compare-and-swap over the session record and the principal's ledger record: it writes only if the session's stored version equals `c.expectedStateVersion` and the ledger's equals `c.expectedLedgerVersion` (`null` means the record must not exist yet). It returns `"ok"`, `"state_conflict"` or `"ledger_conflict"`, and writes nothing unless it returns `"ok"`.
- `commitLedger(c)` is the same compare-and-swap over the ledger record alone, for `killPrincipal` and `clearPrincipalKill`. It must be atomic with `commit`.
- `maxStateBytes`, when present, is the most UTF-8 bytes of session state the store can hold.

Stores in the package:

- `MemoryStore`: in process, for tests and single-process tools.
- `FirestoreStore` from `@anijani/writ/firestore`: one transaction per commit.
- Your own: implement `Store` and run the shared contract in `test/store-suite.ts` of the repository against it.

`ledgerScope: "principal"` (the default) shares one ledger between the live sessions of a principal. `ledgerScope: "none"` never reads or writes principal ledgers, so principal meters and kills see one session only: run one live session per principal. If a ledger is stored for the principal anyway, a gate with `"none"` fails closed with `WritConflictError`.

### Firestore

```ts
import { Firestore } from "@google-cloud/firestore"
import { FirestoreStore, firestoreDocId } from "@anijani/writ/firestore"

const db = new Firestore()
const store = new FirestoreStore(db, { sessions: "writ_sessions", ledgers: "writ_ledgers" }) // the defaults
const gate = createGate({ kernel, policyText, store })
const docId = firestoreDocId(sessionId) // the document id of this session
```

- Session documents are `{ state, state_version, principal, updated_at }` in `writ_sessions`. Ledger documents are `{ ledger, version }` in `writ_ledgers`. Change the names with `{ sessions, ledgers }`; they must differ.
- Ids are encoded with `firestoreDocId`. Code that reads, clears or pre-seeds these documents must address them with it. An empty id, one with a lone surrogate, or one whose encoded form is over 1,500 bytes throws `WritStoreError`. Encoding can triple an id's size, so a session id or principal within the gate's 512-byte limit can still be refused this way; keep them short (UUIDs).
- State and ledger text over 900,000 UTF-8 bytes are refused with `WritStoreError`, to stay inside the 1 MiB document limit. `maxStateBytes` is 900,000, so the gate's budget keeps state below that.
- The store types its own minimal Firestore interface, so the package needs no Firestore dependency. It is tested against an in-memory fake, and was type-checked once against `@google-cloud/firestore` 9.3.1; that check is not part of the repository. The emulator test runs only when `FIRESTORE_EMULATOR_HOST` is set and `@google-cloud/firestore` is installed.

## Client-carried state

Keep state on the server when you can. If a client must carry it (a browser, a desktop app), seal it with `seal` and verify it with `open`; without a MAC the client could edit its own state.

Sealing gives integrity, not freshness: a client can hand back an older sealed state that is still validly signed. So keep a version record on the server: each session's latest `state_version`, compare-and-swapped on every step. Pass it to `open` as `expect`, and `open` refuses a sealed state whose `session_id` or `state_version` differs. Without `expect` (or with `null`) `open` checks only the MAC; an `expect` that is not an object throws `WritInputError` with path `expect`.

```ts
import { open, seal } from "@anijani/writ"

const key = await crypto.subtle.importKey("raw", secret, { name: "HMAC", hash: "SHA-256" }, false, ["sign", "verify"])
const sealed = await seal(stateText, key) // base64url(HMAC-SHA256(state)) + "." + base64url(state)
const latest = await versions.get(sessionId) // your server-side record
const back = await open(sealed, key, { sessionId, stateVersion: latest }) // throws WritInputError on a bad MAC or a stale state
```

Never take the principal ledger from client-carried state; load it from the server. `seal` and `open` use WebCrypto, so they run in Node 20 and in browsers. `open` refuses text longer than `MAX_SEALED_CHARS` before decoding it, and `seal` refuses a state over `MAX_INPUT_BYTES`.

## Session ids

Make every session id a random UUID (`crypto.randomUUID()`). A session id must be unique per principal and, wherever sessions of different principals share a store, unique in that store. The kernel refuses a `session_start` whose id already has entries in the principal's ledger, but it cannot see two concurrent starts, so uniqueness is the host's job. Never derive a session id from something the agent controls: a fresh session would shed escalation and rejection memory.

## Vercel AI SDK

`@anijani/writ/ai-sdk` puts a gate in front of the AI SDK's tool execution (written against `ai` 7.0.135; the package does not depend on `ai`). `writTools` wraps your tools and gives you a `toolApproval` function for `generateText`, `streamText` or `ToolLoopAgent`:

```ts
import { generateText } from "ai"
import { writTools } from "@anijani/writ/ai-sdk"

const writ = writTools({ gate, sessionId, tools: { deleteFile, searchDocs } })
const result = await generateText({ model, tools: writ.tools, toolApproval: writ.toolApproval, messages })
messages.push(...result.responseMessages)

// In your trusted approval UI, render the input Writ will hold the call to:
for (const p of writ.pending()) {
  if (await askUser(p.tool, p.input)) await writ.approve(p.toolCallId, approverId)
  else await writ.reject(p.toolCallId, approverId)
}
// Then answer the SDK's tool-approval-request parts with tool-approval-response parts as usual and call
// generateText again; the SDK runs the approved tools at the start of that call.
```

The Writ call id is the SDK's `toolCallId`, and the digest is `callDigest({ server, tool, toolDigest, args: input, cost })` with `server` defaulting to `"ai-sdk"`, each tool's `toolDigest` to `"unversioned"` (set `toolDigests`), and `cost` from the optional per-tool `cost(input)` functions. `toolApproval` proposes the call: an allowed call is `"not-applicable"`, a call that needs approval is `{ type: "user-approval" }` and appears in `pending()` with the exact input to show, and a denied or rejected call is `{ type: "denied", reason }` with `writ: <reason>: <message>`, the kernel's model-facing text. The SDK runs `toolApproval` again when it resumes, and a repeated proposal answers from where the call stands. `approve` and `reject` answer the recorded request with its digest and cost; `pending()` follows the stored call, so a quorum keeps a call listed until it is decided.

`pending()` is process-local and not durable: an instance lists only the calls its own `toolApproval` saw. A server that rebuilds `writTools` per request keeps the call it showed the approver (`{ tool, input }`) in its own trusted store and passes it as `shown`: `approve(toolCallId, approverId, shown)` then computes the reviewed digest from `shown` and reads the request id and cost from `gate.inspect`, and a `shown` input that differs from the proposed one is refused `digest_mismatch` by the kernel. Without a pending entry and without `shown`, `approve` throws `WritInputError` (path `toolCallId`). When `shown` is passed it always supplies the digest, since it is what the approver reviewed. `reject(toolCallId, approverId)` needs no `shown`: rejecting runs nothing, so it reads the request from `gate.inspect` when the instance has no entry. `reject` works only while a call awaits approval; to stop an approved call that has not run, use `gate.cancel(sessionId, toolCallId)`.

Tool inputs, after the tool's schema has parsed and transformed them, must be plain JSON: no `Date` or class instances, and integers within plus or minus 2^53 - 1 (carry larger ones as strings). Writ digests exactly that value. An input that is not is denied `writ: invalid_input: <path>: <message>` at `toolApproval`, and a wrapped `execute` given one throws the same text without dispatching; the turn goes on either way. Put side effects only in `execute`: the SDK runs a tool's `onInputStart`, `onInputDelta` and `onInputAvailable` before `toolApproval`, outside the gate. Starting the session, turns and steps stays with you (`gate.start`, `gate.turnStart`, `gate.stepStart`).

Every wrapped `execute` runs the tool only after `gate.dispatch` claims the call with the digest of the input the SDK is actually executing. It then reports `succeeded`, or, if the tool throws, reports the outcome unknown and rethrows. An `async function*` execute keeps streaming: the wrapper is an async generator that dispatches, re-yields every item (the SDK's preliminary results), and reports `succeeded` after the last one, or the outcome unknown if iteration throws or stops early. The SDK streams only when `execute` returns an AsyncIterable synchronously, which a wrapper that awaits dispatch cannot do for a plain function, so a plain function that returns an AsyncIterable is drained by the wrapper and its last item returned, which is the output the SDK would have kept. An unclaimed dispatch throws `Error("writ: <reason>: <message>")` without running the tool, which the SDK hands the model as a tool error. That check is what makes the adapter safe against the client's message history: the SDK executes whatever input the history holds for an approved `toolCallId`, so a client can edit the input after the approver saw it (Loopjacking), replay an approved history to run the tool again, or answer `approved: true` itself. Each of these fails in Writ whatever the SDK does: an edited input is refused `digest_mismatch` (or denied `duplicate_call` when `toolApproval` re-proposes it), a replay finds the call already ended, and an SDK approval without a Writ approval is refused `call_awaiting`. A `toolCallId` Writ never saw is refused `unknown_call`.

`toolApproval` never returns `"approved"`: that is the SDK's auto-approval, which executes in the same call without any approval record. Approval is the policy's job, so `writTools` throws `WritInputError` (path `tools.<name>`) for a tool that sets the deprecated `needsApproval`, or that has no `execute`, which would bypass dispatch, and throws it (path `toolDigests.<name>` or `cost.<name>`) for a `toolDigests` value that is not a non-empty string or a `cost` value that is not a function, so a misconfiguration reaches you rather than the model. `approve` and `reject` throw `WritInputError` (path `toolCallId`) for a call that is not pending. Still set `experimental_toolApprovalSecret`: the SDK then refuses an edited history itself, before Writ has to. `examples/ai-sdk` in the repository runs these cases against the real SDK.

## The MCP SEP-2848 profile

`mcpToolApproval` gives the terms of two MCP drafts for a server that gates `tools/call` on Writ: SEP-2848, asynchronous approval for tool calls, and SEP-2643, structured authorization denials. Both functions ask the kernel, which holds the only copy of the tables, so the package keeps none. `docs/formats.md` (MCP SEP-2848 profile) and `docs/sep-2848.md` in the repository describe the profile and the drafts it follows.

```ts
import { loadKernel, mcpToolApproval } from "@anijani/writ"

const kernel = await loadKernel()
mcpToolApproval.disposition(kernel, "unknown")     // "outcome-unknown"
mcpToolApproval.disposition(kernel, "authorized")  // undefined: the call can still move
mcpToolApproval.envelope(kernel, { verdict: "accepted", state_version: 4, decision: "denied", reason: "killed" })
// { reason: "insufficient_authorization", remediation: "unavailable", code: "killed", retry: "never",
//   message: "The session has been stopped. Do not retry this or any other call." }
```

- `mcpToolApproval.disposition(kernel, status)` is the SEP-2848 disposition (`Disposition`) of a terminal call status, as `inspect` reports it: `approved-executed` for `succeeded`; `denied-not-executed` for `rejected`, `expired`, `declined`, `denied` and `denied_at_dispatch`; `execution-error` for `failed`; `outcome-unknown` for `unknown`; and `cancelled` for `cancelled`, which SEP-2848 reports as the SEP-2663 task status rather than a disposition. It is `undefined` for `awaiting`, `authorized` and `dispatched`.
- `mcpToolApproval.envelope(kernel, verdict)` is the SEP-2643 envelope (`ProfileEnvelope`) a server puts under `io.modelcontextprotocol/authorization`. A `needs_approval` verdict gets `remediation: "available"` with one `task` hint and its `requestId`. A `denied` or `dispatch_denied` decision or a rejected verdict gets `remediation: "unavailable"` with the reason `code`, its `retry` class and the reason's reviewed model `message`, never the verdict's own `message` and nothing else, so an envelope is the same for every verdict with that reason. Any other verdict gives `undefined`. Never forward the envelope of a rejected `result`, `outcomeUnknown` or `reconcile`: that call may have run, and SEP-2643 forbids the envelope on a partly executed operation.
- `kernel.profile(id, { status })` and `kernel.profile(id, { verdict })` return the raw `ProfileResult`, `{ disposition?, envelope? }`. `mcpToolApproval.id` is `"mcp-tool-approval"`, the only profile; another id throws `WritInputError` with path `id`, and a malformed status or verdict with path `input`.

`writ check --profile mcp-tool-approval` in the repository flags the policy settings SEP-2848 forbids: `retry_after_unknown` on an action is an error, since a call whose outcome is unknown must never run again.

## The trust boundary

Writ's guarantees hold only if the code around the kernel does these things. The gate cannot do them for you.

- Map raw tool calls to Writ tool names in trusted code, and send every side effect through the gate (complete mediation).
- Keep the agent from causing approval-plane or control-plane events, and from writing the policy. The agent may cause only `propose` (through your mapping of its tool calls) and `stepStart`. The rest are yours:
  - approval plane: `approve`, `reject`, `grantCreate`, `grantRevoke`, `escalationAck`;
  - control plane: `start`, `end`, `turnStart`, `turnEnd`, `reset`, `kill`, `killPrincipal`, `clearPrincipalKill`, `permissionAdd`, `permissionRevoke`, `approverAttest`, `approvalExpire`, and the execution reports (`dispatch`, `result`, `outcomeUnknown`, `reconcile`, `cancel`) from your executor.

  The policy comes from outside the agent's reach, for example a pinned file or a config service; loosening it should itself require approval.
- Compute call digests with `callDigest`, and execute the exact `callPreimage` bytes. On an approver edit, recompute `newDigest` from the edited arguments and `newCost`; a host that relays an end user's edit must not let that user lower the declared cost of their own call without the policy's consent.
- Render approvals from the canonical arguments in a trusted renderer, not the agent, without truncation, flagging confusable and invisible characters.
- Authenticate approver identities, kinds and roles.
- Use a trusted, monotone server clock (`clock` in `createGate`, default `Date.now`), and one such clock for every gate whose sessions share a ledger: the ledger theorem assumes it, and a gate whose clock runs ahead can prune entries that a session on a slower clock still counts.
- Make every store a compare-and-swap on the session state version and on the ledger version the step read, atomic over both when several sessions of a principal are live, with post-dispatch state stored before execution. `MemoryStore` and `FirestoreStore` do this; a custom `Store` must too.
- Seal client-carried state and check its freshness against a server-side version record, as above; never take the principal ledger from it.
- Call `dispatch` immediately before execution. Deliver kill with priority, and abort in-flight tools where possible.
- Report guard values, escalator values (on `propose` and on approver edits; they decide whether a session grant may stand in for a call), declared and actual costs, and outcomes (`declined`, `noEffect`) from trusted code, or relay them through the untrusted-report clamp.

## Limits

Measured on 2026-10-18 on an arm64 Mac with Node 26, through the gate with `MemoryStore`, on a policy with one principal calls meter without a window; each call is `propose`, `dispatch` and `result`, with 71-character digests and idempotency keys and a UUID session id.

- **Input size.** One kernel call takes at most `MAX_INPUT_BYTES` (8 MiB) of UTF-8 input, summed over the policy, state and event; more throws `WritInputError` before the kernel runs. At that size a step peaks at about 500 MB of WebAssembly memory, under a quarter of its 2 GiB ceiling.
- **Event fields.** Every string in an event (ids, digests, tool names, roles, permissions, map keys) is at most 512 UTF-8 bytes, amounts at most 78 digits, integers within plus or minus 2^53 - 1 and nesting at most 128 deep. More throws `WritInputError` with path `event`.
- **State grows with every call.** The kernel keeps a record of each call for the life of the session, plus the principal ledger: about 810 bytes per call here (243,203 bytes after 300 calls, 1,623,910 after 2,000). A step parses the whole state, so its time is linear in the state size: about 0.2 ms for a small state, 16.5 ms per gate step at 150 KB and 184 ms at 1.6 MB. At this rate the default budget of 4 MiB refuses growth after about 4,500 calls, and `FirestoreStore`'s 900,000 bytes after about 970.
- **Windowless ledger entries are never pruned.** A principal meter without `window_ms` keeps one ledger entry per dispatched call for the life of the principal, about 125 bytes each here (36,820 bytes after 300, 248,622 after 2,000), and every session of the principal carries the whole ledger in its state. Entries of meters with a window are pruned once they leave it, so the ledger holds about one window of traffic.
- **A large ledger can block a session.** The gate's forced `ledger_sync` is not a growth event, and it replaces the session's ledger snapshot with the stored one, so it pushes a state over the whole budget when the stored ledger grew by more than the session's remaining headroom since the session last synced. The session then cannot step (it throws `WritStateFullError` and commits nothing, which is safe) and relies on ledger pruning to keep the ledger small; `killPrincipal` still works. If the state, the synced ledger and the policy together pass `MAX_INPUT_BYTES`, the step throws `WritInputError` instead, also committing nothing. Give principal meters a window.
- **`inspect` reads the session's own ledger snapshot.** Principal meter usage in `inspect` comes from the ledger the session last synced, not from the store's current ledger, so it can understate spend that sibling sessions made since then. `remaining` is never below `"0"`; `used` may exceed `cap` after an overrun.
- **Large policies are slow.** Every step decodes and checks the policy, in time that grows with the square of the number of actions: negligible for tens of actions, 34 ms per step at 2,000 and 0.5 s at 8,000.
- **Firestore refuses large records.** `FirestoreStore` refuses state or ledger text over 900,000 bytes with `WritStoreError`; the gate's budget keeps state under that, with room left for `kill` and `end`.

## Errors

Refusals are verdicts, not exceptions: a rejected or denied call resolves normally. These are thrown:

| Error | When |
|---|---|
| `WritInputError` | Input the kernel or the package cannot use. `path` names the argument: a kernel argument (`policyText`, `stateText`, `event`, `ledgerText`, `tracesText`, `jsonText`, `digest`, `time`, and `id` or `input` for `profile`), `policyText` or `retiredPolicyTexts[i]` for a policy that fails `check` in `createGate`, `retiredPolicyTexts[j]` for a retired policy whose shared principal meter has another kind, currency or `window_ms` than the live policy or an earlier retired policy, `maxStateBytes` for a budget that is not a positive integer, `principal` or `ledgerScope` for `killPrincipal` and `clearPrincipalKill`. Also inputs over `MAX_INPUT_BYTES`, lone surrogates, hostile values in `canonicalize`, `parseStrict` and `callDigest`, and every `seal` and `open` failure (bad MAC, malformed or oversize text, a stale or foreign state, a key that is not HMAC SHA-256). Nothing is committed, and the kernel stays usable. |
| `WritKernelError` | A kernel failure that is not the input's fault. After a trap or an abort inside the WebAssembly (running out of memory, for example) it is `"kernel aborted; load a new kernel"` with the original exception as `cause`, and that kernel throws it on every later call: load a new kernel and build a new gate. `process.exitCode` is not touched. |
| `WritConflictError` | 5 commits in a row lost a compare-and-swap race (or 5 ledger commits, for `killPrincipal` and `clearPrincipalKill`), or a gate with `ledgerScope: "none"` found a stored ledger. Nothing is committed. |
| `WritStoreError` | `FirestoreStore` refused a record over 900,000 bytes or an id it cannot encode, found a malformed document, or was given the same collection for sessions and ledgers. |
| `WritStateFullError` | The session has no room for the step ([The state budget](#the-state-budget)). Carries `sessionId`, `bytes` and `limit`. |
| `WritPolicyChangedError` | The stored session runs under a policy this gate does not run, or runs only to settle ([Policy changes](#policy-changes)). Carries `sessionId` and `policyDigest`. |
| `TypeError` | `clock` returned something other than integer milliseconds. |

`loadKernel` throws a plain `Error` when it cannot load the module: `"cannot load <url>: <status>"` when fetching the bytes fails, `"writ_init failed"` when the module does not initialize, and the file system's own error when `wasm/writ.wasm` cannot be read.

Errors from your own store propagate unchanged, and a store whose `commit` or `commitLedger` returns anything but its documented values makes the gate throw `Error`.

## Not yet supported

- Browser bundlers: the glue `wasm/writ.mjs` is imported as `../../wasm/writ.mjs` relative to `dist/src/kernel.js`, so it must be served at that path next to the code; `loadKernel({ wasm })` only supplies the `.wasm` bytes.
- The gate does not pass `audit` or `origin` through to events yet.
- The gate keeps no verdict log, so each call is a new event with a fresh `seq`. Give each delivery its own event id, keep `(event id, content) -> verdict` in the host, and return the stored verdict for an identical redelivery. Do not key on `callId` or `idempotencyKey`: approvals and dispatch retries share them. A repeated `propose` is idempotent in the kernel.
