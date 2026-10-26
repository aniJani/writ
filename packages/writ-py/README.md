# writ-kernel

Python package for Writ, the policy kernel for tool-using AI agents. The kernel decides whether a proposed tool call may run, needs people to approve it, or is refused, and it records what happened afterwards: dispatch, results, retries, meters, grants, kill and escalation. It is the Lean kernel compiled to WebAssembly and run in [wasmtime](https://pypi.org/project/wasmtime/), the package's only runtime dependency. Theorems 1 to 12 of the spec are proved over that kernel in Lean, within the limits the repository README's proof status gives; the WebAssembly build and this package's own code are tested, not proved.

The distribution is `writ-kernel` and the import package is `writ`. It mirrors the TypeScript package `@anijani/writ` (`packages/writ`) module by module, in snake_case and synchronously. For depth, the repository has the spec (`docs/design.md`) and the JSON formats (`docs/formats.md`).

## Install

The package is not on PyPI yet; the release workflow publishes it from the first tagged release. Until then, build it from the repository:

1. Build the WebAssembly from the repository root: `scripts/build-wasm.sh` (it needs `emcc` 6.0.12 and the Lean toolchain; `build/wasm/README.md` has the details). It writes `src/writ/wasm/writ.wasm`, a standalone module for wasmtime, and stamps it with `writ.source` once its smoke test passes.
2. Build the wheel and the sdist in `packages/writ-py`: `uv build`. Both carry `writ.wasm`, so installing the wheel needs no emcc, no Lean and no network beyond the `wasmtime` wheel. Without `writ.wasm` the build fails (`hatch_build.py`) rather than make a package with no kernel.

Python 3.10 or later is required. The version is the CLI's in PEP 440 form: `0.1.0-preview.1` is written `0.1.0a1`.

## Quick start

`simple_gate` is the shortest way in: name your tools, say which need the user's approval, and run them. It is a convenience over a normal policy and a normal gate, not a different kernel or policy format, so the kernel's checks and proved theorems apply to it unchanged. `examples/minimal.py` is this program; in `packages/writ-py`, run `uv run python examples/minimal.py`.

```python
from writ import simple_gate


def ask_user(question: str) -> bool:
    print(f"ask: {question}")
    return True


w = simple_gate({"web_search": "none", "send_email": "per_call"}, user="user:alice")
s = w.session()

search = s.propose("web_search", {"q": "tea"})
print("search:", s.run(search, lambda: "3 results"))

email = s.propose("send_email", {"to": "bob@example.com", "body": "Tea at four?"})
if email.status == "needs_approval" and ask_user("Email bob@example.com?"):
    email = s.approve(email)
print("email:", s.run(email, lambda: "sent"))
```

The tool map becomes an ordinary layer-1 policy. For this example `w.policy_text` is:

```json
{"writ":"0.1","approver_roles":["user"],"limits":{"approval_ttl_ms":600000},"actions":{"web_search":{"consent":"none"},"send_email":{"consent":"per_call"}}}
```

- `simple_policy(tools, approval_ttl_ms=None)` returns that text on its own; the TTL defaults to 600000 ms, and a float with an integral value is taken as that int. A consent other than `"none"` or `"per_call"`, an empty map, a key that is not a str and a TTL that is not a non-negative integer (a fractional float or a bool) raise `WritInputError`.
- `simple_gate(tools, *, user, approval_ttl_ms=None, kernel=None, store=None, clock=None)` loads a kernel and uses a new `MemoryStore` unless you pass them.
- `session(session_id=None)` starts a gate session for `user`, with a new `uuid4` id unless you give one, no permissions, the user as its only approver (approver id `"user"`, role `"user"`) and a user-initiated first turn. An id that is already started raises `WritInputError`.
- `propose(tool, args)` mints a call id, digests `{"server": "local", "tool": tool, "tool_digest": "unversioned", "args": args}`, and returns a `SimpleCall(call_id, tool, call_digest, status, reason, request_id)`. `status` is `allowed`, `needs_approval` or `denied`, with the kernel's `reason` when there is one (a tool missing from the map is denied `unknown_tool`). `request_id` is an opaque str; `json.loads` gives the gate's request id.
- `approve(call)` and `reject(call)` answer for the user and return the updated call. When the kernel refuses the answer, the call keeps the refusal's `reason` and reports where it really stands: still `needs_approval` with its `request_id` (a wrong digest, `digest_mismatch`), `allowed` (already approved, `call_authorized`) or `denied` (ended, rejected, or expired: an answer after the TTL also ends the request).
- `run(call, fn)` dispatches the call and calls `fn()` only if the dispatch is claimed. It then reports `succeeded` and returns `RunResult(ran=True, value=...)`; if `fn` raises, it reports the outcome unknown and re-raises. A call that was not claimed returns `RunResult(ran=False, reason=...)` without running, for example `call_awaiting` before approval and `call_ended` once the call has run or been rejected.

`w.gate` is a normal `Gate`: `kill`, `inspect`, `end` and the other methods work on simple sessions as they are. Meters, quorums and grants are policy fields, so for those edit `w.policy_text`, build your own gate with `create_gate`, and pass the old text in `retired_policy_texts` (see [Policy changes](#policy-changes)). The simple path's approver id is `"user"`, and its call digests use `server: "local"` and `tool_digest: "unversioned"`.

## The kernel

```python
import writ

kernel = writ.load_kernel()
policy = '{"writ":"0.1","approver_roles":["owner"],"actions":{"search":{},"buy":{"consent":"per_call"}}}'
checked = kernel.check(policy)
assert checked.ok
state = kernel.initial(policy).state
r = kernel.step(policy, state, {
    "type": "session_start", "seq": 1, "time": 0, "state_version": 0, "session_id": "s1",
    "policy_digest": checked.policy_digest, "requester": "u1", "permissions": [],
    "approvers": {"laptop": {"principal": "u1", "kind": "human", "roles": ["owner"]}}, "ledger": {},
})
print(r.verdict)  # {'verdict': 'accepted', 'state_version': 1}
```

`load_kernel(wasm=None)` instantiates the bundled `writ.wasm`, or the module's bytes or a path. The compiled module is shared within a process, so a second kernel costs only an instantiation. Each `Kernel` is one WebAssembly instance; its calls are serialized by a lock.

| Method | Returns |
|---|---|
| `version()` | the `writ --version` line |
| `check(policy_text)` | `CheckResult(ok, errors, warnings, policy_digest)`, each finding a `Finding(code, message, action)` |
| `digest(json_text)`, `canonical(json_text)` | the kernel's digest and canonical form of any JSON text it reads |
| `initial(policy_text, digest=None)` | `StateEnvelope(state, state_version, ledger_version)` |
| `step(policy_text, state_text, event)` | `StepResult`: the envelope plus `verdict`, `ledger`, `changed`, `ledger_changed` |
| `replay(traces_text)` | `ReplayResult(traces)`, each `TraceReplay(id, ok, mismatches)` |
| `tombstone(ledger_text, set)` | `TombstoneResult(ledger, ledger_version, changed)`; `""` is the empty ledger |
| `inspect(policy_text, state_text, time)` | `SessionView`, with meter usage counted at `time` in milliseconds |
| `profile(id, input)` | `ProfileResult(disposition, envelope)` for `{"verdict": ...}` or `{"status": ...}` |

Results are frozen dataclasses (`writ.types`). Values that are also event or verdict JSON (verdicts, request ids, costs, call statuses, profile envelopes) stay the dicts and strs the kernel wrote, so they go back into events unchanged. `step` serializes `event` with `canonicalize`, so an event holding a value JSON cannot carry fails before the kernel sees it. Leave an optional event field out; None is JSON null.

Errors:

- `WritInputError` (a `ValueError`) for input the kernel refuses, with `path` naming the parameter (`policy_text`, `state_text`, `event`, `ledger_text`, `traces_text`, `json_text`, `digest`, `time`, and `id` or `input` for `profile`) or the JSON value (`event.audit[0]`). A str holding a lone surrogate is refused here, naming its parameter, and so are inputs over `MAX_INPUT_BYTES` (8 MiB of UTF-8, summed over one call's inputs), before the kernel is called.
- `WritKernelError` (a `RuntimeError`) for a failure inside the kernel. A trap (an abort, which every C++ throw reaches, running out of memory, or a bad memory access) leaves the instance in an unknown state, so that call and every later call on the kernel raise `WritKernelError("kernel aborted; load a new kernel")`, with the wasmtime `Trap` or `ExitTrap` as `__cause__`. Load a new kernel.

## Run a gate

A gate steps one session at a time against a `Store` and commits every accepted step before it returns. `examples/gate.py` is this walk-through as a runnable program that also prints the calls and meters at the end; in `packages/writ-py`, run `uv run python examples/gate.py`.

```python
import json
import uuid

from writ import Cost, MemoryStore, call_digest, create_gate, load_kernel

policy_text = json.dumps({
    "writ": "0.1",
    "approver_roles": ["owner"],
    "meters": {"spend": {"currency": "USD", "cap": 5000, "scope": "principal", "window_ms": 86_400_000}},
    "actions": {"shop.search": {"consent": "none"}, "shop.buy": {"consent": "per_call", "meters": ["spend"]}},
})
gate = create_gate(kernel=load_kernel(), policy_text=policy_text, store=MemoryStore())
session_id = str(uuid.uuid4())

gate.start(
    session_id,
    requester="user:alice",            # the principal the session acts for
    permissions=[],
    approvers={"alice-laptop": {"principal": "user:alice", "kind": "human", "roles": ["owner"]}},
    user_initiated=True,               # also starts the first turn
)
gate.step_start(session_id)            # one per model response

# A free call: propose, dispatch, run, report.
search_digest = call_digest({"server": "shop", "tool": "shop.search", "tool_digest": "sha256:tool-v1",
                             "args": {"q": "tea"}})
p1 = gate.propose(session_id, call_id="c1", tool="shop.search", call_digest=search_digest)
if p1.kind == "allowed":
    d = gate.dispatch(session_id, call_id="c1", call_digest=search_digest)
    if d.claimed:
        # run the tool now, then report what happened
        gate.result(session_id, call_id="c1", outcome="succeeded")

# A call that needs approval and spends money.
cost: Cost = {"amount": "1999", "currency": "USD"}  # 19.99 USD
buy_digest = call_digest({"server": "shop", "tool": "shop.buy", "tool_digest": "sha256:tool-v1",
                          "args": {"sku": "tea-100", "qty": 2}, "cost": cost})
p2 = gate.propose(session_id, call_id="c2", tool="shop.buy", call_digest=buy_digest, cost=cost)
if p2.kind == "needs_approval":
    assert p2.request_id is not None   # always set for needs_approval
    # show the call to the approver in a trusted renderer, then:
    gate.approve(session_id, call_id="c2", request_id=p2.request_id, approver_id="alice-laptop",
                 reviewed_digest=buy_digest, reviewed_cost=cost)
    d = gate.dispatch(session_id, call_id="c2", call_digest=buy_digest, cost=cost)
    if d.claimed:
        # run the tool, then report what it actually charged
        gate.result(session_id, call_id="c2", outcome="succeeded", actual_cost="1999")
```

Three kinds of name appear here, and they are different things:

- **Principal** (`"user:alice"`): the human or system identity. The session's `requester` is a principal, and so is each approver's `principal`. Principal meters, the principal ledger and `kill_principal` are keyed by it. Quorum counts distinct principals.
- **Approver id** (`"alice-laptop"`): the session's name for one attested approver, the key of `approvers`. Approval methods take it as `approver_id`. Once attested, an id can never be pointed at another principal, kind or roles in the same session (rejected `approver_changed`).
- **Role** (`"owner"`): what an approver may approve. Roles come from the policy's `approver_roles`, and consent clauses name them.

Every method takes the session id first and the rest as keyword arguments. The events the gate builds keep the kernel's field names (`approver_id` becomes `approver`), and an optional argument left as None is left out of the event. Any `Mapping` (costs, guards, escalators, request ids, approvers) is copied into a dict and any sequence of strings (`permissions`, `roles`) into a list before it goes into the event; a bare str where a sequence of strings is expected raises `WritInputError` naming the argument (`permissions`, `roles`, `approvers.<id>.roles`). `call_id`s are yours to mint, unique within the session; do not reuse the model's tool-call id, which can change on retry.

`create_gate(*, kernel, policy_text, store, clock=None, ledger_scope="principal", max_state_bytes=None, retired_policy_texts=())` checks the policy and returns a `Gate`. `kernel` is any `KernelLike`, a protocol of the kernel methods the gate calls (`check`, `digest`, `initial`, `step`, `tombstone`, `inspect`), which a `Kernel` from `load_kernel()` satisfies and a wrapper around one can too. `clock` returns integer milliseconds from a trusted clock and defaults to `time.time_ns() // 1_000_000`; a float with an integral value, such as `1000.0`, counts as that int; `ledger_scope` is described under [Stores](#stores), `max_state_bytes` under [The state budget](#the-state-budget), and `retired_policy_texts` under [Policy changes](#policy-changes).

### Gate methods

| Method | Event | Use |
|---|---|---|
| `start(id, *, requester, permissions, approvers, user_initiated=None)` | `session_start` | starts a session; with `user_initiated` also its first turn, whose result it returns |
| `turn_start(id, user_initiated)`, `turn_end(id)` | `turn_start`, `turn_end` | a turn is one user message and the agent's work on it |
| `step_start(id)` | `step_start` | one per model response |
| `propose(id, *, call_id, tool, call_digest, cost=None, guards=None, escalators=None)` | `propose` | asks whether a call may run; returns `ProposeResult` |
| `approve(id, *, call_id, request_id, approver_id, reviewed_digest, reviewed_cost=None, edit=None)` | `approve` | one approver's approval; `edit` (`{"new_digest", "new_cost"?, "escalators"?}`) changes the arguments and restarts the tally |
| `reject(id, *, call_id, request_id, approver_id)` | `reject` | a veto: the call ends rejected |
| `approval_expire(id, *, call_id, request_id)` | `approval_expire` | ends a request early |
| `grant_create(id, *, grant_id, approver_id, tool, scope, max_uses, reviewed_scope_digest, call_digest=None, max_cost=None, not_before=None, expires_at=None)`, `grant_revoke(id, grant_id)` | `grant_create`, `grant_revoke` | standing grants for `grantable` actions |
| `dispatch(id, *, call_id, call_digest, attempt=None, cost=None, guards=None, idempotency_key=None)` | `dispatch` | claims the call immediately before it runs; returns `DispatchResult` |
| `result(id, *, call_id, outcome, actual_cost=None, no_effect=None, untrusted=False, trusted_decline=False)` | `result` | the outcome of a claimed call; returns `ReportResult` |
| `outcome_unknown(id, call_id)` | `outcome_unknown` | the outcome cannot be known |
| `reconcile(id, *, call_id, outcome, actual_cost=None, no_effect=None, untrusted=False, trusted_decline=False)` | `reconcile` | the outcome of an Unknown call, learned later; returns `ReportResult` |
| `cancel(id, call_id)` | `cancel` | withdraws a call that has not been dispatched |
| `escalation_ack(id, *, approver_id, escalation)` | `escalation_ack` | clears an escalation |
| `permission_add(id, *, permission, approver_id)`, `permission_revoke(id, permission)` | `permission_add`, `permission_revoke` | changes the session's permissions |
| `approver_attest(id, *, approver_id, principal, kind, roles)` | `approver_attest` | adds an approver mid-session |
| `reset(id)` | `reset` | starts a new epoch: awaiting and authorized calls are cancelled, dispatched calls become Unknown (settle them with `reconcile`), and turn and session grants die |
| `kill(id)`, `end(id)` | `kill`, `session_end` | see [Kill](#kill) |
| `kill_principal(principal)`, `clear_principal_kill(principal)` | none (ledger only) | see [Kill](#kill); return `PrincipalKillResult(ledger_version, changed)` |
| `inspect(id)` | none (read only) | see [Crash recovery](#crash-recovery-with-inspect) |

Every method that steps returns at least a `GateResult(verdict, state_version, reason)`, a frozen dataclass. `verdict` is the kernel's verdict dict; `state_version` is the version of the stored state after the call.

How it commits:

- The gate commits through a store that does compare-and-swap on the state version and on the version of the principal ledger the step read. Commit happens before effect: a method returns only after its commit, so run a tool after `dispatch` returns with `claimed` True, never before.
- Refusals are returned, not raised. A rejected verdict comes back in the result and writes nothing. A denial is an accepted step: it is committed, and the call keeps its denied status. A propose of a tool the policy does not define is denied `unknown_tool` and counts against the proposal limits, but leaves no call record.
- When two writers race on one session, one commit wins; the other reloads and steps again. After 5 conflicting commits in one call the call raises `WritConflictError`.
- A ledger conflict (another session of the same principal moved the ledger) makes the gate send a `ledger_sync` and retry. If the kernel refuses that sync with `ledger_conflict`, the gate commits a `session_end` and returns that rejected verdict: the session's state can no longer be reconciled with the ledger.
- The gate commits only an accepted step, or that forced `session_end`, even if the kernel reports `changed`.
- The gate sends `max(last_time, now)` as the event time, so a clock that goes backwards does not fail a step. The clock must return an int within plus or minus (2^53 - 1), or a float with an integral value, which is sent as that int (as `Kernel.inspect` takes its time); a fractional float such as `1.5`, a bool or anything else raises `TypeError`.
- `dispatch` sends `idempotency_key`, or else `default_idempotency_key(principal, session_id, call_id)`: `"sha256:"` plus the hex SHA-256 of `canonicalize({"principal": principal, "session": session_id, "call": call_id})`, the same key the TypeScript package derives. It is the same on every attempt of a call, so pass it to the tool as its idempotency key. An explicit key must stay the same across attempts, or the retry is rejected `idempotency_key_mismatch`.
- Store errors and kernel errors propagate unchanged and commit nothing.

### What `kind`, `reason`, `claimed` and `overrun` mean

`propose` returns a `ProposeResult`, a `GateResult` with a `kind`:

| `kind` | Verdict it covers | What the host does |
|---|---|---|
| `allowed` | decision `allowed`, `allowed_by_grant` or `authorized`; or `existing` with status `authorized` | `dispatch`, then run the tool only if the dispatch is claimed |
| `needs_approval` | decision `needs_approval`; the result carries `request_id` | show the call to an approver, then `approve` or `reject` with that `request_id` |
| `denied` | decision `denied`; `existing` with any other status, `dispatched` included; any other decision | do not run the tool. `reason` says why; `status` is the call's status when the verdict is `existing` |
| `rejected` | a rejected verdict: the kernel refused the event itself | do not run the tool; `reason` says why |

A repeated `propose` of the same call (same `call_id`, tool, digest and cost) changes nothing and reports where the call stands, so a host that lost track of a call can simply propose it again. A `dispatched` call cannot be dispatched again; it is settled with `result`, `outcome_unknown` or `reconcile`.

`reason` on any `GateResult` is the rejected verdict's reason, else a `denied` or `dispatch_denied` decision's reason, else the reason inside an `existing` status of `denied` or `denied_at_dispatch`, and None otherwise. The verdict also carries `retry`, which tells the model what to do next, and `message`, model-facing text written to stop retry loops.

`dispatch` returns a `DispatchResult` with `claimed`, which is True only for a `dispatch_claimed` decision. Run the tool when `claimed` is True, and only then. A dispatch can be rejected for a transient reason (a guard that is now false, `meter_exceeded`), in which case the call is still authorized and may be dispatched later. A dispatch rejected `killed` is final. A dispatch can also end the call with a `dispatch_denied` decision (the permission was revoked, the grant is no longer valid), in which case the call is over.

`result` and `reconcile` return a `ReportResult` with `overrun`: a tuple of the meters on which an accepted report committed more than the reservation, in the order the action lists them, else `()`.

## Turns and steps

Call `step_start` once per model response, however many tool calls that response contains. The policy's `limits.max_steps_per_turn` counts these; past it `step_start` is rejected `step_limit` (retry `next_turn`), and the host should stop calling the model for this turn. `turn_start` resets the per-turn counters. A turn started with `user_initiated=True` also clears the session's rejection memory: once a call is rejected, proposing the same tool with the same digest is denied `previously_rejected` until the user starts a turn, so the model cannot shop for a tired approver.

## Money

Amounts are integer minor units of the currency, written as decimal strs: `"1999"` is 19.99 USD, and `"500"` JPY is 500 yen. No sign, no leading zero, no fraction and no JSON number; at most 78 digits. `"6.00"` or `19.99` raises `WritInputError`. A cost is a dict `{"amount": ..., "currency": ...}` (the `Cost` TypedDict); `actual_cost` on a report is an amount alone, in the cost's currency. In the policy, a meter's `cap` and `max_per_call` are plain JSON integers in the same minor units. A `"unit": "calls"` meter counts one per dispatched call instead.

An action with a money meter must declare its cost on `propose` (else `cost_missing`), and the same cost on `dispatch`. Meters are checked at propose and reserved at dispatch, all or nothing over the action's meters, so an approved call can still be refused `meter_exceeded` at dispatch; the call then stays authorized.

## Reports

Meters are reserved at dispatch and settled by the report: `result` `succeeded` or `failed` commits `actual_cost` (else the reservation), `declined` and any report with `no_effect=True` release, `outcome_unknown` keeps the reservation, and an actual cost above the reservation is committed in full and reported in `overrun`. A `result` on an Unknown call is rejected `call_unknown`: use `reconcile`, which is accepted once per call. After `end`, `reconcile` is the only report the session accepts, and the gate resends a `result` there as `reconcile`, so either settles the call.

Releases and partial captures trust the report. When the executor is not trusted (a user's device, a browser), pass `untrusted=True` to `result` or `reconcile`: the gate drops `no_effect`, commits at least the reservation, and turns `declined` into `failed` unless `trusted_decline=True`, meaning the decline came through your trusted approval renderer. This is the TypeScript package's `clampUntrusted`, applied inside the gate.

## Retries

A call that was dispatched can be dispatched again only after `outcome_unknown`, and only if its action sets `idempotent: true`, `retry_after_unknown: true` and `max_attempts` of 2 or more. A failure is final: a `failed` result ends the call, and trying again means a new `propose` with a new `call_id`. A retry keeps the call's approval and idempotency key.

`attempt` on `dispatch` is optional. It defaults to the stored call's `attempts` plus one, read once per `dispatch` call: if the commit loses a race and the gate steps again, it keeps the attempt it first read, so it never claims a retry that another writer allowed in the meantime.

## Crash recovery with `inspect`

`inspect(session_id)` returns the stored session as the kernel sees it at the gate's clock, as a `SessionView`, or None when none is stored. It reads only, and it works under a retired policy too. After a crash, inspect each live session and settle its calls by status:

- `dispatched`: the call was claimed, so the tool may or may not have run. If the tool's own records (looked up by the idempotency key) tell you the outcome, report it with `result`; otherwise report `outcome_unknown`. Never run it a second time on a guess.
- `authorized`: approved and not dispatched; it can be dispatched now.
- `awaiting`: propose the same call again; it answers `needs_approval` with the current `request_id`, to show the approver again.
- `unknown`: `reconcile` when you learn the outcome, or dispatch a retry if the action allows one.
- Anything else has ended; there is nothing to do.

`inspect` shows a call's digest, not its arguments, so keep the canonical argument bytes (`call_preimage`) by call id in your own storage before you dispatch, and recompute the digest from them.

## Kill

- `kill(session_id)` kills the session. Awaiting and authorized calls are cancelled. Afterwards the session accepts only `propose` (answered `denied killed`), `kill`, `end`, `result`, `outcome_unknown` and `reconcile`; everything else, every `dispatch` included, is rejected `killed`. Dispatched calls still settle. With the policy's `kill_scope: "principal"`, a `kill` also sets the principal's tombstone.
- `kill_principal(principal)` sets the tombstone in the principal's stored ledger, without a session. Every live session of that principal learns of it at its next commit, through the gate's forced `ledger_sync`: its awaiting and authorized calls are cancelled and its next `dispatch` is rejected `killed`. New sessions of the principal start killed. It returns `PrincipalKillResult(ledger_version, changed)`; `changed` is False when the tombstone was already set.
- `clear_principal_kill(principal)` clears the tombstone. Live sessions that saw it set are ended at their next commit: their sync fails with `ledger_conflict`, the gate commits `session_end`, which makes their dispatched calls Unknown, and returns that rejected verdict. When that commit was a `result` or `reconcile`, the gate sends the same report once more as `reconcile` on the ended session (with the same `untrusted` clamp) and returns its verdict, so the call settles in one call. An `outcome_unknown` is not resent; settle the call later with `reconcile`.
- Both take a principal that is a non-empty str of at most 512 UTF-8 bytes with no lone surrogate (else `WritInputError` with path `principal`), need `ledger_scope="principal"` (else `WritInputError` with path `ledger_scope`), and raise `WritConflictError` after 5 conflicting ledger commits in a row.

If `kill` raises (a store error, `WritConflictError`, `WritStateFullError` and so on), call `kill_principal` with the session's principal, which writes only the ledger record and so works whatever state the session is in, then `end(session_id)`.

## The state budget

Session state grows with every call, so the gate gives each session a byte budget, `max_state_bytes`. It defaults to the store's `max_state_bytes` if it has one, else `MAX_INPUT_BYTES // 2` (4 MiB), and is never set above the store's own limit. It must be a positive int, or a float with an integral value, taken as that int; anything else, a bool included, raises `WritInputError` with path `max_state_bytes`. Growth events (`start`, `propose`, `approve`, `grant_create`, `approver_attest`, `permission_add` and `dispatch`) are refused once the stored state is above seven eighths of the budget; for `start`, the incoming principal ledger counts too. Everything else, `kill`, `end`, `result`, `outcome_unknown`, `reconcile` and `cancel` among them, keeps the remaining eighth as headroom. A step whose new state would be above the whole budget is not committed.

Both refusals raise `WritStateFullError`, which carries `session_id`, `bytes` (the size that did not fit) and `limit`. Nothing is committed. Settle the session's dispatched calls, `end` it, and start a new session with a new id; principal meters and the tombstone carry over through the ledger.

## Policy changes

A session runs under the policy it started with. `create_gate` checks `policy_text` and every entry of `retired_policy_texts` and raises `WritInputError` (path `policy_text` or `retired_policy_texts[i]`) on the first policy with an error. A gate refuses to step a stored session whose policy digest is not its own with `WritPolicyChangedError`, which carries `session_id` and the session's `policy_digest`.

To deploy a new policy, build the gate with the new `policy_text` and pass the old texts in `retired_policy_texts`. A session started under a retired policy runs under that policy, but accepts only `end`, `kill`, `result`, `outcome_unknown`, `reconcile` and `inspect`, so its dispatched calls still settle their meters; every other method raises `WritPolicyChangedError`. A session whose policy is neither current nor retired raises `WritPolicyChangedError` on every method, `inspect` included.

Policies that share a principal ledger must give each shared principal meter the same kind (money or calls), the same currency for a money meter, and the same `window_ms`, because a ledger entry holds only the meter name and an amount. `create_gate` compares every pair among `policy_text` and `retired_policy_texts`, and raises `WritInputError` (path `retired_policy_texts[j]`, the later policy of the pair, with a message naming the meter, the other policy and each property that differs) when two of them disagree. To change any of them, rename the meter.

## Stores

A `Store` (a `typing.Protocol`) has four methods, all required, and an optional `max_state_bytes` attribute:

- `load(session_id)` returns a `Stored(state, state_version, principal)`, and `load_ledger(principal)` a `LedgerRecord(text, version)`, or None.
- `commit(c)` takes a `Commit(session_id, state, state_version, expected_state_version, principal, expected_ledger_version, ledger=None)` and is one atomic compare-and-swap over the session record and the principal's ledger record: it writes only if the session's stored version equals `c.expected_state_version` and the ledger's equals `c.expected_ledger_version` (None means the record must not exist yet). It returns `"ok"`, `"state_conflict"` or `"ledger_conflict"`, and writes nothing unless it returns `"ok"`.
- `commit_ledger(c)` takes a `LedgerCommit(principal, ledger, expected_ledger_version)`: the same compare-and-swap over the ledger record alone, for `kill_principal` and `clear_principal_kill`. It must be atomic with `commit`.
- `max_state_bytes`, when present and not None, is the most UTF-8 bytes of session state the store can hold. The gate reads it with `getattr`.
- A store raises `WritStoreError` for a failure of its own: a record it cannot hold, or a stored record it cannot read. The gate never raises it and passes it on unchanged, committing nothing, as it does every store error. `MemoryStore` never raises it.

The records are frozen dataclasses. `MemoryStore` is the in-process store, for tests and single-process tools; it holds a lock, so threads may share it. For your own store, add its factory to the `make` fixture in `tests/conftest.py` of the repository: the store contract (`tests/test_store.py`) and the gate suite (`tests/test_gate.py`) then run against it.

`ledger_scope="principal"` (the default) shares one ledger between the live sessions of a principal. `ledger_scope="none"` never reads or writes principal ledgers, so principal meters and kills see one session only: run one live session per principal. If a ledger is stored for the principal anyway, a gate with `"none"` fails closed with `WritConflictError`. Any other `ledger_scope` raises `WritInputError` with path `ledger_scope` (the TypeScript gate treats any value but `"principal"` as `"none"`).

The gate is synchronous and keeps nothing between calls, so threads may share one gate and one `MemoryStore`. Concurrent steps on one session, or on one principal's ledger, race through the store's compare-and-swap exactly as two gates do, and a call that loses 5 commits in a row raises `WritConflictError`.

## Canonical JSON and digests

`canonicalize(value, root="")` is RFC 8785 canonical JSON with I-JSON checks, written in Python rather than through `json.dumps(sort_keys=True)`, whose output differs:

- Keys sort by UTF-16 code unit, so `"\U0001f600"` sorts before `"\uffff"`, and integer-like keys sort as strings (`"10"` before `"9"`).
- Numbers print as ECMAScript prints them: `1e-7`, not `1e-07`, and a float that is a whole number prints without a fraction, so `1.0` and `1` are the same value.
- `True` and `False` are `true` and `false`, never `1` and `0`.
- Refused with a path (`items[3].name`): `-0.0`, a non-finite float, an integer beyond plus or minus (2^53 - 1) whether int or float (carry it as a string), a dict key that is not a str (`json.dumps` would turn `1` into `"1"`), a str holding a surrogate code point, nesting deeper than 128 levels, and any type other than dict, list, tuple, str, int, float, bool and None.

`parse_strict(text, root="")` parses JSON text under the same rules and also refuses duplicate keys (after unescaping), trailing data and a number literal that does not round-trip through a double (`0.10000000000000001`; `4.50` and `1E2` are fine). An integer literal gives an int and any other a float.

`call_digest(call)` is `writ-call-v1`: `"sha256:"` plus the SHA-256 of `call_preimage(call)`, the canonical JSON of `{"t": "writ.call.v1", "server", "tool", "tool_digest", "args", "cost"}`. `call` is a `CallInput` dict with `server`, `tool`, `tool_digest`, and optionally `args` (missing means `{}`; `None` is JSON null) and `cost` (`{"amount", "currency"}` or `None`). Execute the preimage's arguments, not the original object.

`tool_digest(tool)` is `writ-tool-v1`, over `tool_preimage(tool)`, `{"t": "writ.tool.v1", "tool": <tool>}` with every member of the MCP tool definition. Tool definitions may hold fractions: a number with at most 15 significant digits and a magnitude of 0 or within 1e-300 to 1e300 prints as ECMAScript prints it, `-0.0` prints as `0`, and any other number is refused. An int counts by its exact value, so `10**20` is accepted and `2**60` (19 significant digits) is not. A JSON integer literal with more than 15 significant digits, read as an int, is therefore refused, as the Lean reader refuses it, where the TypeScript package sees only the rounded double.

Both digests are checked against every vector in `corpus/digests/call-v1.jsonl` and `tool-v1.jsonl`, the same vectors the Lean kernel and the TypeScript package pass.

## The MCP SEP-2848 profile

`writ.mcp_tool_approval.disposition(kernel, status)` gives the SEP-2848 disposition of a terminal call status (`approved-executed`, `denied-not-executed`, `execution-error`, `outcome-unknown`, or SEP-2663's `cancelled`), and None while the call can still move. `writ.mcp_tool_approval.envelope(kernel, verdict)` gives the SEP-2643 structured-denial envelope of a verdict, or None. Both ask the kernel through `kernel.profile("mcp-tool-approval", ...)`; the package holds no copy of the tables. `docs/formats.md` (MCP SEP-2848 profile) describes the members.

`REASONS` and `RETRY_CLASSES` list the reason codes and retry classes of `schema/reasons.json`.

## Not in this package

The TypeScript package's sealed state for client-carried sessions (`seal`, `open`), `clampUntrusted` as a public helper (the gate applies the same clamp when `result` or `reconcile` gets `untrusted=True`), the Firestore store and the Vercel AI SDK and LangGraph adapters have no Python counterpart. The API is synchronous; there is no asyncio variant.

## Tests

`scripts/py-test.sh` from the repository root refuses a missing `writ.wasm`, or one whose `writ.source` stamp does not match the current kernel sources (`scripts/wasm-source-hash.sh`), then runs `uv sync --frozen`, ruff, mypy (strict) and `pytest -q` here, with the versions pinned in `uv.lock`. The tests run every digest vector and profile vector, check that a build without `writ.wasm` fails, replay `corpus/examples` and `corpus/attacks`, and compare the kernel verdict by verdict with the native `writ oracle` (built by `lake build writ`) on the corpus streams and on 200 seeded random streams, the same streams as the TypeScript differential test. Without the native binary the differential tests are skipped, unless `WRIT_REQUIRE_NATIVE=1`. They also run the store contract, the gate suite and the minimal path, ported test for test from the TypeScript package's `store-suite.ts`, `gate-suite.ts`, `gate.test.ts` and `simple.test.ts` under the same names, and both examples, checking that the code blocks of [Quick start](#quick-start) and [Run a gate](#run-a-gate) are their text.
