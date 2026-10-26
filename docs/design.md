# Writ: design (v2)

Status: draft for review, 2026-10-16. Revised after four independent reviews (red team, Lean feasibility, adopter experience, standards fit).

## 1. What this is and why

Writ is an open-source Lean 4 library and toolchain that proves safety rules for the **policy kernel** of a tool-using AI agent: the small piece of logic that decides whether a proposed tool call may run, needs people to approve it, or is refused, and that tracks what happened afterwards. It does not verify the model, and it does not verify host application code.

Agent builders write a JSON policy. Writ checks it and runs a proven kernel over it. The kernel ships compiled to WebAssembly (and later native libraries), so hosts embed the proven decision logic rather than a reimplementation. Writ also exports a conformance corpus (event sequences with the kernel's verdict at each step), so any implementation, gateway or framework can certify its approval behavior.

Why now:
- Every major framework has its own approval mechanism (OpenAI Agents SDK, Claude Agent SDK, Vercel AI SDK, LangGraph, Google ADK, Pydantic AI, Mastra, Microsoft Agent Framework, Genkit) with differing, mostly undocumented guarantees about argument binding, replay and double execution. Recent research shows real attacks in this gap: post-approval argument substitution in Agno and LangGraph Agent Server (Loopjacking, arXiv 2609.21081), duplicated side effects that agents then report as successes (arXiv 2609.29095), misleading approval displays (arXiv 2606.02668).
- MCP is standardizing approval: SEP-2848 "Asynchronous Approval for Tool Calls" (draft, June 2026) needs a reference implementation and conformance scenarios before it can become final, and nobody has offered formal semantics. The MCP conformance repository has no tool-approval scenarios.
- The closest formal work covers parts of the problem: ASU "Approve What, Exactly?" (arXiv 2610.21063, Tamarin proofs of approval binding and single use), AWS Dogwood (temporal Cedar superset, semi-formal spec, no mechanized proofs found), Cedar (Lean-proved, stateless). No one provides proven, stateful kernel semantics plus a portable conformance corpus.

Success looks like: an agent builder can `npm install` Writ and gate tool calls in under 15 minutes without reading Lean, and any implementation of agent approvals (framework, gateway, or a hand-written gate) can certify itself against Writ's corpus.

## 2. Goals, non-goals, anti-goals

Goals:
- A small, readable, executable Lean kernel whose safety properties are proved, and whose acceptance behavior is also characterized and whose every decision is reached by a witness trace (so it cannot be "safe" by refusing everything).
- A policy format that is easy to write by hand, with optional higher-level authoring layers that compile to it.
- The proven kernel itself runnable in every major language, starting with TypeScript.
- A conformance corpus that any implementation can replay.
- Interop with MCP, A2A, AP2, OpenTelemetry, Cedar and Dogwood instead of competing with them.

Non-goals:
- Detecting prompt injection, sandboxing tool execution, model poisoning, supply chain.
- Proving anything about host code; host glue is conformance-tested, not proven.
- A general policy language competing with Cedar or Rego.
- Generating policies with an LLM.

Anti-goals (failure even if it technically works):
- Claiming "proven" for anything beyond what is proved. The README carries a per-theorem proof status table and the trust boundary (section 10) up front.
- A format so elaborate that people stop writing it by hand.
- Fixed, built-in risk tiers. Risk vocabulary belongs to users.
- App-specific concepts in the core.

## 3. Constraints

- Lean 4.35.0, pinned in `lean-toolchain`. No Mathlib.
- Kernel modules import only `Init` and `Std.Data` (verified to pull in no `Lean.*`). JSON and CLI code live outside the kernel.
- Arithmetic on `Nat`/`Int` integer minor units. No floats, no string-length semantics, no regex in the kernel. The kernel never computes hashes; it compares host-supplied digests.
- License Apache-2.0.
- User-facing copy uses no em-dashes.

## 4. Architecture

```
 presets ─┐
 extends ─┼─> labels + rules ──[writ expand]──> Policy (layer 1) ──> Kernel.step ──> verdicts
 MCP tools/list ─[writ import]─┘                     │                   │
                                                     └─[writ check]      ├─[writ traces]─> corpus
                                                                         ├─[writ oracle]─> JSONL
                                                                         └─[C → WASM/native]─> bindings
```

Lean modules:
- `Writ.Core` (data types: `Reason`, `Policy`, `Event`, `State`) and `Writ.Kernel` (logic: consent, meters, failures, grants, calls, per-event handlers in `Kernel.Step.*`, `step`, `run`): the kernel. `step : Policy → State → Event → State × Verdict`, total and deterministic. Generic over identifier types (`[DecidableEq] [Ord]`): `String` in production, small finite types for exploration and proofs by `decide`.
- `WritSpec`: traces, trace predicates and executable checkers (`Inv.check`, the fuzzer's theorem checks), `Inv`, theorem statements.
- `Writ.Proofs`: per-event characterization lemmas, invariant preservation, theorems.
- `Writ.Author`: the policy checker (`Policy.check`, `Policy.WF`), labels, rules, `extends`, presets, escalator mapping, `expand`, and their proofs.
- `Writ.Profile`: standards profiles (section 13), outside the kernel: `Writ.Api` and `WritCli` import them, `Writ.Core` and `Writ.Kernel` never do.
- `Writ.Explore`: bounded exploration with symmetry reduction; the seeded trace fuzzer (`writ-fuzz`).
- `Writ.Json` (JSON values, parser, printer, canonical form and SHA-256, written in `Init` and `Std` only so the WebAssembly build stays small) and `Writ.Codec` (policy, event, verdict, state and trace codecs); `WritCli`: the `writ` executable. No Lake dependencies.
- `bindings/ts`: the TypeScript package wrapping `writ.wasm` (digests, canonical JSON, event encoding, state persistence hooks).
- `bindings/python`: the Python package (`packages/writ-py` in the repository), the same kernel objects linked as a standalone `writ.wasm` and run in wasmtime.

## 5. Policy format

Canonical form is JSON with `$schema` and `"writ": "<version>"`. YAML is not parsed by Writ.

### Minimal policy

```json
{ "writ": "0.1", "approver_roles": ["user"], "actions": { "send_email": { "consent": "per_call" } } }
```

Everything else is optional with documented defaults. A policy with an action that needs approval must name its approver roles.

### Layer 1: resolved policy (the only thing the kernel sees)

```json
{
  "writ": "0.1",
  "mode": "enforce",
  "approver_roles": ["owner", "admin"],
  "meters": {
    "usd_day": { "currency": "USD", "cap": 500000, "scope": "principal", "window_ms": 86400000, "max_per_call": 100000 },
    "usd_month": { "currency": "USD", "cap": 5000000, "scope": "principal", "window_ms": 2592000000 },
    "tool_calls": { "unit": "calls", "cap": 600, "scope": "principal", "window_ms": 3600000 }
  },
  "limits": {
    "max_steps_per_turn": 4,
    "max_proposals_per_turn": 12,
    "max_approval_requests_per_turn": 3,
    "max_proposals_per_session": 200,
    "max_approval_requests_per_session": 30,
    "max_consecutive_failures": 3,
    "escalation_scope": "tool",
    "approval_ttl_ms": 600000,
    "authorized_ttl_ms": 300000
  },
  "escalation_roles": ["owner"],
  "actions": {
    "calendar.list": { "permission": "calendar.read", "consent": "none" },
    "calendar.create": {
      "permission": "calendar.write",
      "consent": "per_call",
      "grantable": { "scope": "session", "max_uses": 20, "max_duration_ms": 3600000 },
      "guards": ["calendar_connected"]
    },
    "shop.buy": {
      "permission": "payments",
      "consent": { "quorum": 1, "roles": ["owner", "admin"], "human_only": true, "exclude_requester": true },
      "meters": ["usd_day", "usd_month"],
      "escalate": {
        "over_limit": { "consent": { "all": [
          { "quorum": 2, "roles": ["finance"], "exclude_requester": true },
          { "quorum": 1, "roles": ["requester_manager"] } ] } }
      },
      "approval_ttl_ms": 86400000
    },
    "shell.run": {
      "consent": "none",
      "grantable": { "scope": "session", "max_uses": 50, "max_duration_ms": 3600000 },
      "escalate": {
        "not_allowlisted": { "consent": "per_call", "grantable": true },
        "dangerous": { "consent": "per_call" }
      },
      "meters": ["tool_calls"]
    },
    "http.post": { "consent": "per_call", "flags": ["sends_external"] },
    "files.delete_all": { "exposed": false }
  }
}
```

Per-action requirements:
- `permission`: opaque string or null. The host supplies the session's permission set.
- `consent`: `none` | `per_call` | a clause `{ quorum: k, roles?, human_only? (default true), exclude_requester? (default false) }` | `{ all: [clause, ...], distinct? (default false) }`. `per_call` is the clause quorum 1, any approver role, human only. Quorum is at least 1. Consent is a conjunction of groups of clauses (`none` is the empty conjunction; a single clause is a group of one): it is satisfied when every group is. A group is satisfied when every clause has k distinct eligible principals among the approvals of the current generation; one principal may count toward several clauses of a group. With `distinct: true`, the group needs an assignment of distinct principals to its clause slots (the sum of the clauses' k), each eligible for its slot, so "the requester's manager and a different finance approver" is `{ all: [{ quorum: 1, roles: ["requester_manager"] }, { quorum: 1, roles: ["finance"] }], distinct: true }`. Roles relative to the requester (manager, team lead) are attested by the host for the session, for example as a `requester_manager` role.
- `consent_if_cost_over`: an amount with a currency; a declared cost in the same currency below it needs no consent. A missing cost or a different currency never lowers consent.
- `escalate`: host-reported named booleans on `propose` mapped to stricter requirements (for example `over_limit`, computed by the host from the arguments). An escalator fires when reported true or missing. Each maps to `{ consent, grantable? (default false) }`: the fired escalators' consent is joined into the call's consent, and a grant may stand in for the call only if every fired escalator is `grantable`. So "allow this command for the session" (a grantable `not_allowlisted`) never covers a `dangerous` command. Escalators can only raise strictness. This is how "approve only if amount > 1000" style rules are expressed without the kernel reading arguments.
- `grantable`: whether a standing grant may stand in for per-call consent. Fields: `scope` (`turn` | `session`), `max_uses`, `max_duration_ms`, `any_args` (default false). `any_args: true` requires `max_uses` and `max_duration_ms` and is refused on metered actions unless `allow_any_args_metered: true`. `writ check` refuses `grantable` when the base consent or a grantable escalator's consent has a clause with quorum above 1 or a `distinct` group of more than one clause, when neither the base consent nor any escalator is grantable-relevant (base consent `none` and no grantable escalator), and refuses a grantable escalator on an action without `grantable`. The base consent may be `none`.
- `idempotent` (default false) and `retry_after_unknown` (default false, requires `idempotent`), plus `max_attempts`.
- `guards`: names of host-evaluated preconditions. The host reports their values on `propose` and `dispatch`; the kernel requires all to be true.
- `meters`: the meters the call draws on (any number; each must have room). Cost is mandatory on `propose` for actions with a money meter, and all money meters of one action must share a currency.
- `approval_ttl_ms`, `authorized_ttl_ms`: per-action overrides of the policy-level limits (a deploy approval may wait two days while an email approval expires in ten minutes).
- `exposed`: if false, the action must never be offered to the model; any proposal is denied.
- `mode`: `enforce` | `log_only`, overriding the policy-level mode; the result is the action's effective mode.
- `flags`: optional `reads_private`, `ingests_untrusted`, `sends_external` for the lethal-trifecta check.
- `review`: optional display metadata for approval UIs, never read by the kernel: a title template, field labels, and `hidden` JSON pointers (listed in the approval payload so hiding is auditable).
- `messages`: optional per-reason override of the model-facing and user-facing denial text.

Policy-level fields:
- `meters`: a money meter has a `currency` (ISO 4217, integer minor units) and counts call costs; a `"unit": "calls"` meter counts one per dispatched call (rate limits, tool-call budgets). `cap` is optional: a meter without a cap only records usage (to watch traffic before choosing a cap). `scope`: `session` (per kernel state), `principal` (across all sessions of the requesting principal, through the ledger, section 6), optionally with `window_ms` (at least 1) for rolling windows. `max_per_call` caps a single call on money meters. Reset never refunds a meter.
- `limits`: per turn and per session, including `max_failures_per_session` (at least 1) and `escalation_scope` (`session`, the default, or `tool`, see Failures and escalation in section 6). `max_steps_per_turn` counts `step_start` events (one per model response, however many tool calls it contains). Proposal limits count every `propose`, including denied ones. Approval limits count `needs_approval` dispositions of `enforce` actions (a `log_only` action's would-need-approval does not use up live budget). Session limits are reported with their own reasons (`session_proposal_limit`, `session_approval_budget`, retry class `never`), distinct from the per-turn ones (`next_turn`). TTLs are checked against event time and are half-open like grant windows: an approval requested at t with TTL d is valid while time < t + d.
- `approver_roles`: the closed set of approver roles. The reserved principal `agent` can never be an approver.
- `escalation_roles`: roles allowed to clear escalation. Defaults to all approver roles.
- `mode`: `enforce` (default) or `log_only` (shadow mode, section 6).

- `binding`: `mutable` (default) or `immutable` (approvers may not edit arguments).
- `kill_scope`: `session` (default) or `principal` (a `kill` also sets the principal tombstone).

The policy digest is `sha256:` followed by the lowercase hex SHA-256 of the policy document's canonical JSON (object keys sorted by UTF-16 code units as in RFC 8785, no insignificant whitespace). `session_start` carries it, and the kernel refuses a session whose digest differs from the policy it runs.

Unknown actions are denied. Unknown fields are an error. `writ check` also refuses `exposed: false` together with an action-level `mode: log_only` (contradictory; the kernel never shadows an unexposed or unknown action into running, even under a policy-level `log_only`), and an action that lists the same meter twice.

### Layer 2: labels, rules, extends (optional)

```json
{
  "writ": "0.1",
  "extends": ["org-baseline.json"],
  "approver_roles": ["owner"],
  "labels": { "risk": { "order": ["read", "navigate", "device", "spend", "destructive"] } },
  "rules": [
    { "when": { "risk": ">=device" }, "require": { "consent": "per_call" } },
    { "when": { "risk": ">=destructive" }, "require": { "exposed": false } }
  ],
  "actions": { "vm.restart": { "labels": { "risk": "device" }, "permission": "vm.power" } }
}
```

Rule grammar, kept small so the proofs hold:
- Label orders are total in v0.1, declared least to most risky. Partial orders are a later extension.
- Conditions are upward-closed only: `">=x"` per dimension, AND across dimensions.
- Rules set only strictness-ordered fields: `consent` (a conjunction with more groups is stricter; a group is stricter with more clauses or `distinct`; a clause is stricter with larger k, a subset of roles, or `human_only` and `exclude_requester` true), `grantable` (absent strictest, smaller limits stricter, `any_args: false` stricter), `exposed` (false stricter), `idempotent` and `retry_after_unknown` (false stricter), `guards` and `flags` (union), `mode` (enforce stricter). `permission`, `meters`, `escalate`, `review` and `messages` are per-action only.
- Rules combine by join (strictest per field). Explicit per-action requirements are joined in too, so they can only make an action stricter. Consent joins by taking the union of groups (equal groups once), so a join never makes an existing group require extra people. When the join produces a clause with quorum above 1, `grantable` becomes absent. A clause with an empty role set is a check error.
- An action missing a label on a declared dimension gets that dimension's strictest value.
- `extends` joins the parent's rules and per-action requirements, so a team policy can never weaken an organization baseline's rules and per-action requirements, and a policy that extends another cannot turn on policy-wide `log_only` (a check error). The extending policy still owns the policy-level settings (`approver_roles`, `escalation_roles`, meter definitions and caps, and limits, TTL limits included), so whoever deploys a policy must vet those and confirm that it extends the intended baseline (made precise 2026-10-23).

This example is `tests/cli/layer2/spec-example.json`, which `scripts/cli-test.sh` expands and checks. `docs/formats.md` gives the exact expansion rules, how `extends` is resolved, and the layer-2 errors.

### Presets (optional)

Shipped as layer-2 files: `generic-tiers` (read, navigate, device, spend, destructive), `mcp-annotations` (from `readOnlyHint`, `destructiveHint`, `idempotentHint`, `openWorldHint`), `mcp-risk-metadata` (SEP-2793 `riskLevel`, `blastRadius`, `reversibility`, `approvalRecommendation`; `multi` maps to quorum 2), `axes` (effect, reversibility, audience, value, data sensitivity). Presets need no new proofs. They are in `schema/presets/`, and a policy uses one by listing its relative path in `extends` (`docs/formats.md`).

### Import from MCP

`writ import mcp tools.json` emits a layer-2 draft using the `mcp-annotations` preset (and `mcp-risk-metadata` when present). Annotations are untrusted and only raise strictness; missing annotations take MCP's pessimistic defaults. Each imported action records `source.tool_digest`; `writ check --tools <tools.json>` detects changed tool definitions. At runtime, the tool digest is part of the call digest (section 6), so a swapped tool definition invalidates approvals.

### Lethal-trifecta check

`writ check` warns when one policy has a `reads_private` action, an `ingests_untrusted` action, and a `sends_external` action that needs no consent or accepts `any_args` grants. Kernel enforcement comes in v0.2 (section 8).

## 6. Kernel semantics

### Principals and the control plane

Events come from three kinds of source:
- **Agent plane**: `step_start`, `propose`. The model's proposals, relayed by the host.
- **Approval plane**: `approve`, `reject`, `grant_create`, `grant_revoke`, `escalation_ack`. Each names an attested approver.
- **Control plane**: `session_start`, `session_end`, `turn_start`, `turn_end`, `reset`, `kill`, `permission_add`, `permission_revoke`, `approver_attest`, `approval_expire`, `ledger_sync`, and execution reports (`dispatch`, `result`, `outcome_unknown`, `reconcile`, `cancel`) from the host's executor.

The trust boundary (section 10) requires that the agent can never cause approval-plane or control-plane events. `permission_add` and `escalation_ack` additionally name an attested approver; the kernel checks the approver holds a required role.

Approvers are attested with `principal` (the human or system identity), `kind` (`human` | `automated`) and roles, either at `session_start` or later through `approver_attest` (enterprise approvers often appear hours later). An approver id, once attested, can only be re-attested identically: it can never be re-pointed to another principal or change kind or roles mid-session (such an `approver_attest` is rejected `approver_changed`), so an approver who must lose authority requires ending the session. Quorum counts distinct principals, not approver ids. `human_only` consent ignores automated approvers. The session also names its `requester` principal, used by `exclude_requester`.

### Events

Every event carries `seq` (strictly increasing), `time` (non-decreasing integer milliseconds; hosts send `max(last_time, now)` from a trusted clock), `state_version` (the version of the state it applies to, for compare-and-swap, section 7), and optional opaque `origin`. Call-scoped events carry `call_id`.

| Event | Fields |
|---|---|
| `session_start` | `session_id`, `policy_digest`, `requester`, `permissions`, `approvers` (id to principal, kind, roles), `ledger` (principal ledger snapshot, see below) |
| `session_end` | |
| `turn_start`, `turn_end` | `user_initiated` (bool) on `turn_start` |
| `step_start` | |
| `propose` | `call_id`, `tool`, `call_digest`, `cost?` (amount, currency), `guards` (name to bool), `escalators` (name to bool) |
| `approve` | `call_id`, `request_id`, `approver`, `reviewed_digest`, `reviewed_cost?`, `edit?` (`new_digest`, `new_cost?`, `escalators`) |
| `reject` | `call_id`, `request_id`, `approver` |
| `approval_expire` | `call_id`, `request_id` |
| `grant_create` | `grant_id`, `approver`, `tool`, `call_digest?`, `scope`, `max_uses`, `max_cost?` (amount, currency), `not_before?`, `expires_at?`, `reviewed_scope_digest` |
| `grant_revoke` | `grant_id` |
| `approver_attest` | `approver`, `principal`, `kind`, `roles` |
| `permission_add` | `permission`, `approver` |
| `permission_revoke` | `permission` |
| `dispatch` | `call_id`, `attempt`, `call_digest`, `cost?`, `guards`, `idempotency_key` |
| `result` | `call_id`, `outcome` (`succeeded`, `failed`, `declined`), `actual_cost?`, `no_effect?` |
| `outcome_unknown` | `call_id` |
| `reconcile` | `call_id`, `outcome`, `actual_cost?`, `no_effect?` |
| `cancel` | `call_id` |
| `escalation_ack` | `approver`, `escalation` (the escalation count the approver reviewed) |
| `ledger_sync` | `ledger` (the principal ledger as currently stored) |
| `reset`, `kill` | |

Audit-only fields the kernel never reads (`display_digest` on `approve`, `by` on `grant_revoke`, authentication method, on-behalf-of for delegated approvals) travel in each event's `audit` object in the JSON trace format, so the verdict log records them without the kernel depending on them.

Field names follow ecosystem vocabulary where it exists: `tool` (MCP `name`, OTel `gen_ai.tool.name`), `call_id` (OpenAI and Gemini `call_id`, OTel `gen_ai.tool.call.id`), `step_start` (Vercel "step"; OpenAI calls this a "turn", and the spec documents the collision). The adapter mapping table for Vercel AI SDK, LangGraph, OpenAI Agents SDK, Claude Agent SDK, Google ADK and Pydantic AI is part of the spec.

### Identifiers

- `call_id` is unique per session; reuse with different content is rejected (`duplicate_call`). A `propose` repeating an existing `call_id` with the same tool and with the digest and cost either as first proposed or as current after edits returns the call's current disposition and changes nothing, so frameworks that re-run steps on resume (LangGraph, OpenAI `RunState`) are safe. The current disposition is `denied killed` (session kill or tombstone) or `denied escalated` (session or this tool blocked) when those now apply, and `denied permission_missing` for an awaiting or authorized call whose permission is no longer held; otherwise `needs_approval` with the current `request_id` while awaiting; while authorized, the denial that dispatch re-evaluation would now give without guards (`authorization_expired`, `permission_missing`, `previously_rejected`, `grant_invalid`), else the original `allowed` or `allowed_by_grant` (or `authorized` once approved); the denial for a denied call, and `existing(status)` once the call has been dispatched or has ended otherwise. A proposal for a tool the policy does not define leaves no record (Propose, below), so its repeat is evaluated afresh. Guards and escalators on a repeat are not compared: guards are re-checked at dispatch, and escalators cannot change a call after propose.
- On `needs_approval` the kernel mints `request_id = (session_id, call_id, generation)`. `approve` and `approval_expire` must echo the current `request_id`; `reject` may echo the current or an earlier generation (see Quorum). Stale dialogs and approvals replayed into another session or generation are rejected (`stale_request`).
- `idempotency_key` on `dispatch` is computed by the binding as `H(principal, session_id, call_id)`; the kernel checks that it stays constant across attempts. It is passed through to tools and payment APIs (x402 `payment-identifier`, ACP idempotency keys), and the principal is part of it so that two principals whose session and call ids coincide never share a key there.
- `session_id` must be unique per principal and, wherever sessions of different principals share a store, unique in that store; bindings generate a random UUID. The kernel refuses a `session_start` whose id already has entries in the ledger (`already_started`, Ledger below), but cannot see concurrent starts, so uniqueness is a binding obligation (and a hypothesis of theorem 9).
- `call_id` is minted by the binding (unique per session), not taken from the model: provider tool-call ids are minted per response and can change on retry. The provider's id travels in the event's `audit` object.
- `seq` is allocated by the binding, which renumbers a retried event after a `ledger_sync` and dedupes redelivered events by their content and its own event id.
- Size: the JSON event codec refuses any string in an event (identifiers, digests, map keys, roles, permissions) longer than 512 UTF-8 bytes, so a host cannot grow the state through one oversize value. Amounts keep their 78-digit limit. `origin`, `audit` and the `ledger` object (carried by `session_start` and `ledger_sync`) are not limited, because the ledger is produced by the kernel and the binding, not by the host's event stream. The kernel itself never measures strings (section 3).

### Call digests

The kernel compares digests for equality only. The spec defines how hosts compute them, labeled `writ-call-v1/RFC8785-JCS+SHA-256`:
- Preimage: canonical JSON of `{"t": "writ.call.v1", "server": <server or tool-provider identity>, "tool": <name>, "tool_digest": <digest of the tool definition>, "args": <args>, "cost": <amount and currency or null>}`, where `tool_digest` is the `writ-tool-v1` digest of the tool definition (`docs/formats.md`, Tool digests) (made precise 2026-10-23).
- Arguments must be I-JSON: duplicate keys rejected, non-finite numbers rejected, integers outside plus or minus 2^53 rejected (carry them as strings), number literals whose decimal value differs from that of their shortest round-trip form rejected too (carry them as strings), missing arguments normalized to `{}`.
- **Execute the bytes you hashed**: the tool receives the canonical serialization that was digested, not the original.
- External digests are allowed with a label (for example AP2 `checkout_hash` as `external:ap2-checkout`) when a payment protocol already binds signed bytes.
- Digest vectors in the corpus cover every pitfall (large integers, duplicate keys, Unicode escapes, key order, missing arguments).

### Per-call lifecycle

```
Proposed ─┬─> Denied*                          (default deny, permission, guard, exposed, limits,
          │                                     escalated, killed, previously_rejected, meter)
          ├─> Authorized(d)                    (consent none, or a valid grant reserved for this call)
          └─> AwaitingApproval(g) ─┬─> AwaitingApproval(g+1)   (an approver edits: new digest, tally restarts)
                                   ├─> Authorized(d)           (quorum reached on generation g)
                                   ├─> Rejected*               (any eligible approver rejects)
                                   ├─> Expired*                (approval_ttl, or approval_expire)
                                   └─> Cancelled*
Authorized(d) ─┬─> Dispatched(d, n) ─┬─> Succeeded* | Failed* | Declined*
               │                     └─> Unknown* ──> Dispatched(d, n+1)  (only retry_after_unknown, n < max_attempts)
               ├─> DeniedAtDispatch*   (re-evaluation fails terminally: permission revoked, grant invalid, previously rejected)
               ├─> Rejected*            (a late veto before dispatch)
               ├─> Expired*            (authorized_ttl)
               └─> Cancelled*          (also on session `kill` or a tombstone through `ledger_sync`)
```

A session `kill`, and a principal tombstone arriving through `ledger_sync`, both cancel every awaiting and authorized call. Dispatched and Unknown calls are not cancelled: their outcomes still settle through `result`, `outcome_unknown` and `reconcile`, but no `dispatch` of any call, a retry included, is accepted afterwards (it is rejected `killed`, and an Unknown call stays Unknown). So a kill never ends a call `DeniedAtDispatch`.

`*` is terminal; terminal states are absorbing except the explicit `Unknown` retry edge. `reconcile` on an Unknown call records evidence and adjusts the meter (below) but does not change the disposition, matching SEP-2848's rule that `outcome-unknown` is final. `cancel` after dispatch is rejected as a no-op (`call_dispatched`, or the stage reason of whatever status the call has reached): the outcome stays pending, because a call that may have run must never be reported as cancelled.

`reconcile` records the reported outcome on the Unknown call as evidence, once: a second `reconcile` is rejected `already_reconciled`. A `result` arriving after `reset` or `session_end` turned the call Unknown is reported as `reconcile` (a `result` on an Unknown call is rejected `call_unknown`).

Terminal dispositions project to SEP-2848 strings: Succeeded `approved-executed`, Denied/Rejected/Expired/DeniedAtDispatch/Declined `denied-not-executed`, Failed `execution-error`, Unknown `outcome-unknown`, Cancelled `cancelled`. Declined means a person stopped or declined the call after dispatch and before it took effect (the user pressed Stop and the host aborted the tool, or the user declined on the device); a host reports it only when the tool had no effect, and otherwise reports the outcome it observed.

### Rules (informal; the Lean is normative)

- **Every dispatch needs a prior accepted propose** for the same `call_id`.
- **Propose** of a `call_id` already recorded follows the repeat rule (Identifiers) and none of the numbered checks. A `propose` of a new `call_id` runs these checks in this order, and the first that fails gives the denial reason:
  1. `killed`: the session is killed or the principal tombstone is set;
  2. `unknown_tool`: the policy does not define the tool;
  3. `not_exposed`: the tool is not exposed;
  4. `escalated`: the session is escalated, or the tool is blocked under tool-scoped escalation;
  5. `session_proposal_limit`, then `proposal_limit`: the session's or the turn's proposal limit is reached;
  6. `permission_missing`: the action's permission is not held;
  7. `guard_false`: a declared guard is false or missing;
  8. cost shape, money meter by money meter in the order of the action's `meters` (calls meters have no shape check): `cost_missing` (no cost), `currency_mismatch` (a cost in another currency than the money meter's), `cost_above_per_call` (a cost above the meter's `max_per_call`); only when every money meter's shape is fine, room: `meter_exceeded` if the call's draw (its cost on a money meter, 1 on a calls meter) leaves any meter no room;
  9. `previously_rejected`: the same `(tool, call_digest)` was rejected earlier in the session and no `user_initiated` turn has started since (this stops the model shopping for a tired approver);
  10. consent (after `consent_if_cost_over` and escalators): `none` gives `allowed`; else a covering grant gives `allowed_by_grant` (the grant use is reserved for this call and does not count against approval budgets); else `session_approval_budget`, then `approval_budget`: the session's or the turn's approval-request budget is spent; else `needs_approval` with a fresh `request_id`.

  A `propose` for a tool the policy does not define is accepted (with `denied killed` when step 1 fails, else `denied unknown_tool`), counts toward the proposal limits, and leaves no call record, so its `call_id` stays unused (a repeat is evaluated afresh). The repeat check runs first: a `propose` of an unknown tool whose `call_id` already belongs to a recorded call is rejected `duplicate_call`. The call record keeps the proposed guard and escalator values only for the names the action declares.
- **Approve** must echo the current `request_id`, come from an approver eligible for at least one clause of the call's consent, where eligible for a clause means attested, holding an approver role and one of the clause's roles, human if the clause is `human_only`, and not the requester if it is `exclude_requester`; and have `reviewed_digest` (and `reviewed_cost`) equal to the current generation's digest and cost. A consent with no clauses (`none`) leaves nothing to be eligible for, so eligibility for it falls back to a single clause that admits any attested approver holding an approver role whose principal is not `agent`: `permission_add`, which checks eligibility against `none`, a `grant_create` whose consents have no clauses, and a `reject` of a call that needed no consent still need such an approver. An approver who edits (whether or not already in the tally) supplies `edit.new_digest` (and `new_cost`, plus host-recomputed `escalators` for the edited arguments, where a missing escalator counts as true): the call's consent becomes its current consent joined with the edited arguments' effective consent, so an edit can raise but never lower the required quorum; the editor must be eligible for at least one clause of the raised consent; this creates generation g+1 and returns `authorized` when the editor's approval alone meets the raised consent, else `pending`, so the next request id is `{ session, call, generation: g + 1 }` (bindings derive it), counts as that approver's approval of the new generation only, voids all earlier tallies, and restarts the approval TTL at the edit. An edit without `new_cost` keeps the current cost; on an action with a money meter `new_cost` is required (`cost_missing`). Every counted approval therefore reviewed exactly the digest and cost that will be dispatched (for an approver's edit, the digest and cost it set). Each principal approves a generation at most once. Profile `binding: immutable` (used by the SEP-2848 profile) refuses edits. An approval is also refused (`previously_rejected`) if the call's digest, or an edit's new digest, was rejected earlier in the session.
- **Quorum** is reached when, for every clause, k distinct principals eligible for that clause approved the current generation. Any single `reject` from an eligible approver ends the call (veto) and records `(tool, digest)` for `previously_rejected`. A reject echoing the current or an earlier generation of the call in the current session and epoch vetoes an Awaiting or an Authorized, not yet dispatched, call: a veto only narrows what can happen, so a slow approver's "no" is never lost to an edit or to a quorum reached a moment earlier. Eligibility is checked against the call's current consent (a join only adds clauses). The kernel keeps the digest of every generation, and a reject records the digest of the generation it echoes as well as the proposed and current ones.
- **Grants** are created only by an approver eligible for every clause of the action's base consent and of every grantable escalator's consent, only for `grantable` actions, within the action's `max_uses` and scope and, when the action sets `max_duration_ms`, with an `expires_at` at most the creation time plus `max_duration_ms`, without a digest only if `any_args`. A grant covers a call if every clause of the call's consent has quorum at most 1, every fired escalator is `grantable`, the grant's creator is eligible for every clause, tool and digest match (when the grant has one), the call's declared cost fits the grant's remaining `max_cost` (when it has one: a cost is present, in the same currency, and reserved plus consumed cost plus this cost is at most `max_cost`), time is within `[not_before, expires_at)`, uses consumed plus reserved is below `max_uses`, it is not revoked, and its scope is current (`turn` grants die at `turn_end`, `session` grants at `reset` or `session_end`). A use (and the call's cost, for a grant with `max_cost`) is reserved at `propose`, consumed at the first claimed `dispatch`, and returned if the call ends without dispatching. Retries of an Unknown call do not consume further uses.
- **Dispatch** re-evaluates, then claims. Accepted only if the call is Authorized for that digest and cost (or Unknown, for a permitted retry), within the action's `authorized_ttl` (retries included), its `(tool, digest)` was not rejected in the session (first attempts only; a retry of an Unknown call is not blocked), any grant it relies on is still valid, the permission is still held, guards are still true, not escalated, and every meter of the action can reserve. If re-evaluation fails because of revocation, the call ends `DeniedAtDispatch`; if it fails for a transient reason (guard false) the dispatch is rejected and the call stays Authorized. Any `dispatch` after a kill or while the tombstone is set is rejected `killed` before re-evaluation (Kill, below). A retry `dispatch` of an Unknown call whose action lacks `retry_after_unknown` is rejected `retry_not_allowed`, and one of an already reconciled call `already_reconciled`. The call's status is checked before the attempt number, so a `dispatch` of a Dispatched call is rejected `call_dispatched`, not `attempt_order`.
- **Meters**: a first-attempt dispatch reserves on every meter of the action, all or nothing: the call's cost on money meters, 1 on calls meters. On `result` or `reconcile` with `no_effect: true` or with outcome `declined`, release every meter of the call. Otherwise commit, whether the call succeeded or failed: `actual_cost` when reported (else the reservation) on money meters, 1 on calls meters. The committed amount up to the reservation keeps the reservation's time; the excess of an overrun is dated at the reporting event, so a late overrun counts in the window it was reported in and a commit never moves already-checked spend into a window that did not check it. An entry counts in a windowed meter's usage at an event while the event time is below the entry's time plus `window_ms` (for the excess, `excess_at` plus `window_ms`), with no lower bound: an entry dated after this session's last event (written meanwhile by another session of the principal) still counts, and is inside its window. A commit below the reservation is a partial capture and frees the difference. Releases and partial captures trust the executor's report (section 10); a binding relaying reports from an untrusted executor (a user's device or a browser) clamps them to commit at least the reservation and never release: it drops `no_effect`, and reports a device's `declined` as `failed` unless the decline came through the trusted approval renderer (otherwise a device could dodge escalation, and release its spend, by labelling its failures declined). With several meters, each meter is re-timed and re-checked on its own. A reconciled call is never retried (`already_reconciled`). An overrun arises only when a report commits: a `result` or `reconcile` that commits an actual cost above the reservation on some money meter is accepted with decision `overrun` carrying `meters`, the overrun meters in the order the action lists them: `{"verdict":"accepted","state_version":n,"decision":"overrun","meters":["usd_day"]}`. Otherwise `result` and `reconcile` decide nothing. A release (`no_effect: true`, or outcome `declined`) reports no overrun, so it adds no overrun failure, whatever `actual_cost` it carries; the outcome's own counting is unchanged (a `failed` outcome still counts as a failure, see Failures and escalation). An overrun counts as a failure for escalation. On Unknown keep the reservation. A retry reuses its reservation while that entry is inside the meter's window; if the entry has left the window, the retry must fit the cap again (otherwise it is rejected `meter_exceeded`, transient) and the entry is re-timed to the retry. No reservation is accepted that would bring usage above the cap; usage can exceed the cap only through a reported overrun, a reservation by a `log_only` action, or a `ledger_sync` or `session_start` that brings in a principal ledger whose usage is above the cap. A meter without a cap never denies for usage.
- **Ledger pruning**: whenever a step changes the entry list of a meter scope (the session's entries or the principal ledger's entries), it also drops from that same list every committed entry whose meter has a `window_ms` and which lies outside the window at the event time, both its reserved part (`time`) and its excess part (`excess` 0, or `excess_at` outside the window). The session's list is pruned only by the session policy's session-scope meters, and the principal ledger's list only by the session policy's principal-scope meters: an entry whose meter the policy defines only in the other scope, or not at all, is never dropped, so a session meter never prunes the principal ledger, whatever its name. Entries of meters without a window and uncommitted entries are never dropped either. Only a list the step already changes is pruned, so pruning never changes a ledger without incrementing its version. `ledger_sync` never prunes: it takes the stored ledger as is. Policies that share a principal ledger (a policy change, retired policies whose sessions still settle, or two gates during a rolling deploy) must give each shared principal meter the same identity: the same kind (money or calls), the same currency for a money meter, and the same `window_ms`. A ledger entry carries only the meter name and an amount, so a meter that changes kind or currency would sum unlike amounts, and a session prunes by the windows of its own policy, so a meter that changes its window would let one policy drop entries the other still counts. To change any of them, rename the meter (or, for a window, drain the old sessions first). A binding can check this only for the policies it knows; two gates on different policies during a rolling deploy rely on the documented rule.
- **Ended sessions**: after `session_end` only `reconcile` and `ledger_sync` are accepted, so late outcomes still settle principal reservations (a sync may then clear the tombstone, Ledger below).
- **Ledger** (principal-scoped meters and kill): `session_start` carries the principal ledger snapshot (window balances, kill tombstone, ledger version). A `session_start` whose `session_id` already owns entries in the ledger it brings is rejected `already_started`: the id was used by an earlier session of this principal, and accepting it would make that session's entries look like this one's. A `session_start`'s own rules run after the envelope checks and the kill check (Protocol errors): first `policy_digest_mismatch` (the `policy_digest` it carries is not the digest of the policy the session runs under), then this reused-id rule. The kernel's state carries the ledger forward and every verdict exposes it, so the host writes it back with compare-and-swap on the ledger version (section 7). Every claimed dispatch, every principal meter change and every tombstone change increments the ledger version, so two live sessions of one principal can never both commit a step that read the same ledger version. `ledger_sync` brings a session up to date with the stored ledger: it is accepted only if the stored version is not older, the stored entries of this session are among the state's own entries, none of them more often than the state holds it, every own entry missing from the stored ledger is committed (so another session pruned it), and, for a live session, the sync does not clear a set tombstone (`ledger_conflict` otherwise, retry class `never`: the binding ends the session, because its stored state can no longer be reconciled with the ledger). An ended session accepts a sync that clears the tombstone: it accepts only `reconcile` and `ledger_sync` (Ended sessions), so nothing reopens, and its late `reconcile` can still settle. A tombstone arriving through `ledger_sync` voids pending approvals as `kill` does. A principal `kill` tombstone persists across sessions until the binding clears it in the stored ledger (section 7). Starting a new session therefore never resets principal meters or a principal kill.
- **Reset** increments the epoch. Every non-terminal call ends (Cancelled if never dispatched, Unknown if dispatched); turn and session grants die; meters, rejection memory and escalation carry over.
- **Kill** applies to the session (`kill`) and, when the policy says so, sets the principal tombstone. Pending approvals are void. While the session is killed or the principal tombstone is set, the only events accepted are `propose` (accepted, disposition `denied killed`), `kill`, `session_end`, `result`, `outcome_unknown`, `reconcile` and `ledger_sync`, so in-flight calls still settle and the session can still end. Every other event, `dispatch` included, is rejected `killed`, after the envelope checks (Protocol errors, below). A `session_start` whose ledger snapshot already has the tombstone set is accepted, and every later event then follows this rule (its proposals are denied `killed`). Hosts process kill out of band with priority and propagate abort to in-flight tools.
- **Failures and escalation**: the kernel counts consecutive failures per tool and total failures per session. Failed results, accepted `outcome_unknown` events and meter overruns (from results or reconcile that commit) count. A report that is both a failure and an overrun counts once. A declined result does not count and does not reset a counter; a call that `reset` or `session_end` turns Unknown does not count (that is not an outcome report); a dispatch attempt beyond `max_attempts` is simply rejected. A success only resets that tool's counter; `reconcile` touches counters only on an overrun. When the session total reaches `max_failures_per_session`, or a tool's counter reaches `max_consecutive_failures` under `escalation_scope: session`, the session is escalated: new proposals and all dispatches are denied with `escalated`. Under `escalation_scope: tool`, a tool reaching `max_consecutive_failures` blocks only that tool's proposals and dispatches. The escalation count rises by one for each counted failure that leaves the session escalated or a tool blocked. Blocks last until `escalation_ack` from an approver holding an escalation role whose `escalation` echoes the current count (a stale acknowledgment is rejected `stale_request`, so it cannot clear failures nobody reviewed; an acknowledgment while nothing is blocked is rejected `not_escalated`); it clears every block and resets the counters. Policies that must keep the requester from clearing their own escalation set `escalation_roles` accordingly.
- **Shadow mode**: for actions in `log_only` mode (never an unknown or unexposed action, and never a kill), every decision that would deny is recorded in the verdict (`would_deny: reason`) and the call proceeds as if allowed. `would_deny` is the first failing Propose check from step 4 on, the approval budget checks of step 10 included (steps 1 to 3, `killed`, `unknown_tool` and `not_exposed`, are never shadowed), and a would-be `needs_approval` is recorded as `would_need_approval`. This lets teams roll out policies on live traffic without the kernel's state diverging from reality. Theorems in section 8 hold for `enforce` actions; `log_only` actions are explicitly excluded.
- **Policy change**: the kernel holds one policy per session. A changed policy ends the session (fail closed, matching AgentCore's behavior); principal meters and tombstones carry over through the ledger, and every principal meter the old and new policies share must keep its kind, currency and `window_ms` (Ledger pruning). This is the only meter rule across policies, because each list is pruned only by the meters of its own scope and session meters share no ledger. Rejection memory, escalation and grants are per session: starting a new session is a control-plane decision of the host. `writ diff` (section 11) shows the effect of a change before rollout.
- **Protocol errors**: events that make no sense in the current state are rejected with a reason code and do not change state. Every event first passes the envelope checks, in this order: `not_started` (no `session_start` yet), `session_ended` (for every event but `reconcile` and `ledger_sync`, see Ended sessions), `already_started` (so `session_start` on an ended session is `session_ended`), `stale_seq`, `time_decreasing`, `state_version_mismatch`; then the kill check (Kill, above), which a first `session_start` passes even when its ledger snapshot carries a set tombstone; then the event's own rules (for a `session_start`, `policy_digest_mismatch` and then the reused-id rule, which also gives `already_started`, Ledger). A call-scoped event (`approve`, `reject`, `approval_expire`, `dispatch`, `result`, `outcome_unknown`, `reconcile`, `cancel`) whose `call_id` has no record is rejected `unknown_call` before any rule of its own (request ids, digests, stage reasons, attempt numbers). A call-scoped event that does not fit the call's current status is rejected with the reason that names that status: `call_awaiting` (awaiting approval), `call_authorized` (authorized, not dispatched), `call_dispatched` (dispatched, no outcome), `call_unknown` (outcome unknown), `call_ended` (any other terminal status). Four cases have reasons of their own, described above: `retry_not_allowed` and `already_reconciled` (Dispatch and Meters, taking precedence over `call_unknown`), `not_escalated` (Failures and escalation) and `approver_changed` (Principals and the control plane). `call_awaiting`, `call_authorized`, `call_dispatched`, `call_unknown` and `not_escalated` have retry class `fix_request`; `call_ended`, `retry_not_allowed`, `already_reconciled` and `approver_changed` have `never`.

### Verdicts and reason codes

Each event yields `accepted` or `rejected(reason)`, plus the new `state_version`. An accepted `propose` also yields a disposition: `allowed`, `allowed_by_grant`, `needs_approval(request_id)`, or `denied(reason)`, and for a repeated propose also `authorized` or `existing(status)`. An accepted `result` or `reconcile` that overruns yields `overrun(meters)` (Meters, above). In shadow mode, verdicts carry `would_deny`.

In JSON a verdict is `{ "verdict": "accepted", "state_version": n, "decision": d, ... }` or `{ "verdict": "rejected", "state_version": n, "reason": r }`, where `d` is one of `pending`, `authorized`, `allowed`, `allowed_by_grant` (with `grant`), `needs_approval` (with `request_id`), `denied` (with `reason`), `dispatch_claimed`, `dispatch_denied` (with `reason`), `existing` (with `status`), `overrun` (with `meters`), and is omitted when the event decides nothing; shadow mode adds `would_deny` (a reason) or `would_need_approval: true`. Reason codes, statuses and decisions are written in snake_case.

Reason codes are a closed, versioned enumeration. Each has a `retry` class (`fix_request`, `never`, `after_user_action`, `next_turn`, `after_escalation`), a default model-facing message written to stop retry loops, and a default user-facing message. Policies may override messages per action. Renaming or removing a reason code is a breaking schema change.

## 7. State contract and deployment patterns

- **State format** `writ.state/1`: canonical JSON with `kernel_version`, `policy_digest`, `session_id`, `state_version`, `last_seq`, `last_time`, epoch, calls, grants, meters, counters and ledger. Serializable and deterministic.
- **Single writer per session**: every event names the `state_version` it applies to; the binding stores the result with compare-and-swap on that version. Two processes sharing a session can never both accept a dispatch. Recommended stores: the host's database with a version column, Redis with `WATCH`/Lua, Durable Objects.
- **Several live sessions per principal**: every store is one atomic compare-and-swap on both the state version and the ledger version the step read (for `ledger_sync`, the version it brought in); the ledger is written only if the step changed its version beyond that. On a ledger conflict the binding discards the step, sends `ledger_sync` with the stored ledger, and retries the event. A binding without atomic two-key writes runs one live session per principal. To kill a principal without a session, or to clear its tombstone, the binding sets or clears the tombstone directly in the stored ledger with compare-and-swap, incrementing its version; live sessions learn of it at their next commit through `ledger_sync` (a set tombstone cancels their pending calls; a cleared one fails their sync, and the binding ends them). The dispatched and Unknown calls of a session ended this way can still be settled with `reconcile`, because an ended session's sync may clear the tombstone (section 6, Ledger). When a binding ends a session because its `ledger_sync` was rejected `ledger_conflict` while handling a `result` or `reconcile`, it sends that report once more, as `reconcile` with the same fields, on the now-ended session, and returns that verdict. Likewise, once a session is ended, by the binding or by the host's `session_end`, the binding reports a `result` rejected `session_ended` once more as `reconcile` with the same fields and returns that verdict, so the host keeps calling `result` for the session's other dispatched calls (or calls `reconcile` directly) and they settle. The resent `reconcile` goes through the usual ledger-conflict handling (sync and retry) like any event; "once" means the binding never resends a report a second time. Both apply the rule that a result arriving after `session_end` is reported as `reconcile` (section 6, Per-call lifecycle). An `outcome_unknown` is not resent: the end already made the call Unknown. Because every claim increments the ledger version, the committed steps of all sessions of one principal form a single sequence in which each step saw the ledger as last committed.
- **Commit before effect**: the post-dispatch state is durably stored before the tool runs. A crash between store and execution yields an Authorized-then-Dispatched call that becomes Unknown on recovery, never a second dispatch.
- **Redelivery**: events with `seq` at or below `last_seq` are rejected without change; the binding keeps the verdict log (which is also the audit log) and returns the original verdict for an identical redelivered event. Identical repeated `propose` is idempotent in the kernel itself.
- **State lives on the server.** Client-carried state (Vercel message history, OpenAI `RunState` strings) must be sealed with a MAC by the binding (`seal`/`open` helpers) or kept server side. Sealing gives integrity, not freshness: a client can replay an older sealed state. A host that carries state on the client must keep the latest `state_version` of each session on the server, compare-and-swap it on every step, and refuse a sealed state whose version differs; the principal ledger is never taken from client-carried state.
- **Versioning**: a session stays on the kernel version it started with. A later kernel may resume an older state only through a migration function proved to preserve the invariant; until one exists, old sessions finish on the old kernel (the binding can load several WASM versions).
- **Bounded state**: the binding gives each session a byte budget for its stored state and refuses growth events (`session_start`, `propose`, `approve`, `grant_create`, `approver_attest`, `permission_add`, `dispatch`) once the stored state is above seven eighths of it, so `kill`, `session_end`, `result`, `outcome_unknown`, `reconcile`, `cancel` and `ledger_sync` have headroom for the session's own control events; the host then ends the session and starts a new one. The headroom does not cover the principal ledger: a forced `ledger_sync` brings in the stored ledger, so a principal ledger that grew by more than the remaining headroom since the session last synced can still push the state over the budget. The session then cannot step and nothing commits, and the tombstone in the stored ledger still stops dispatch. With pruning (section 6), the ledger holds one window of traffic per windowed meter. Compaction of terminal calls and aggregation of windowless ledger entries are deferred (section 16).
- **Split client/server** (desktop, browser): the kernel runs on the server. For a device-local tool, the server issues an authorization ticket (call_id, digest, epoch, expiry, signature) after a claimed `dispatch`; the device presents it to execute and reports `result` when it reconnects (a decline on the device is `declined` only when it came through the trusted approval renderer, otherwise `failed`; the server applies the untrusted-executor clamp of section 6). A device that never reports is timed out by the server with `outcome_unknown`. Approvals that must wait days need a session that lives that long.
- **Gateway profile** (MCP gateways, which see only `tools/call` since MCP removed sessions): the gateway creates sessions and derives their keys from authenticated identity only (a client-supplied header may only select among sessions the gateway created, so the agent can never mint a fresh session to shed escalation or rejection memory), with several live sessions per principal handled as above; turn and step limits are disabled and session-scoped limits become windowed principal meters (calls meters for rate limits). Approvals collected in-band (MCP elicitation `accept`) are client assertions; policies can require `out_of_band` approval (a console or chat approval authenticated by the gateway's identity provider) for consequential actions.

## 8. Theorems

Assumptions: the policy satisfies `Policy.WF` (a Lean predicate; `writ check p = ok` implies `WF p`), the trace is any finite event sequence from the initial state, and the action is in `enforce` mode (for unknown tools, the policy-level mode is `enforce`). "Claimed dispatch" means a dispatch whose verdict is `ok dispatch_claimed`; a dispatch that ends the call (`dispatch_denied`) is not a claim. The host executes a tool only on a claim.

v0.1:
1. **Consent.** If a dispatch is claimed for a call whose recorded consent (the effective consent at propose, joined with the effective consent of every approver edit) is not `none`, then either (a) every group of that consent is satisfied by the approvals of the call's final generation (for every clause, at least k distinct principals eligible for the clause, and for a `distinct` group an assignment of distinct principals to all clause slots (approver role and a clause role, human if `human_only`, not the requester if `exclude_requester`, never `agent`)), each approval with reviewed digest and cost equal to the dispatched ones (for an approver's edit, the digest and cost it set), with matching `request_id`, within the action's `approval_ttl`, and no eligible approver rejected any generation of it; or (b) every clause has k at most 1 and no `distinct` group has more than one clause, every escalator that fired at propose is grantable, a grant created by an approver eligible for every clause covered the call at propose (including its `max_cost`) and is valid at dispatch (not revoked, same epoch, inside its time window and turn), and its use was reserved for this call.
2. **Grant accounting.** At all times a grant's consumed plus reserved uses are at most `max_uses`, and its consumed plus reserved cost is at most `max_cost`; at most `max_uses` claimed first attempts use the grant, and their costs sum to at most `max_cost`; a use returned by a call that ended without dispatch can be reused; retries of an Unknown call consume no extra use.
3. **Permission.** A proposal with a non-denied disposition (new or repeated; `existing` reports a call's past and is not a disposition here), and a claimed dispatch, only occur while the action's permission is held; every held permission was attested at `session_start` or added by an attested approver holding an approver role whose principal is not `agent`.
4. **At most once.** For actions without `retry_after_unknown`, at most one claimed dispatch per call, ever. For actions with it, claimed dispatches are at most 1 plus the number of accepted `outcome_unknown` events for that call, never more than `max_attempts`, with strictly increasing attempt numbers, each retry preceded by an Unknown.
5. **Terminal absorption.** Once a call reaches a terminal disposition, no event changes it, except the Unknown retry edge.
6. **Epoch and freshness.** No claimed dispatch uses a call from an earlier epoch; no approval is accepted with a stale `request_id` or outside the action's `approval_ttl`; no dispatch (first attempt or retry) is claimed outside the action's `authorized_ttl`.
7. **Kill.** No claimed dispatch after an accepted `kill`, or while the principal tombstone is set.
8. **Bounds.** Under a policy-level `enforce` mode, per turn and per session, non-denied new proposals (a repeated proposal changes nothing and is not counted), `step_start` events and new `needs_approval` dispositions stay within their limits. For each meter with a cap, no reservation is accepted that would bring usage (within the window) above the cap, and no single call reserves more than `max_per_call`. Usage can exceed the cap only through an overrun (a result or reconcile reporting an actual cost above the reservation, which is committed in full because the money is already spent, and counted from the time it was reported), a reservation by a `log_only` action, or a `ledger_sync` or `session_start` that brings in a principal ledger whose usage is above the cap; every overrun counts as a failure for escalation, and while usage is above the cap no further first-attempt dispatch on that meter is claimed, nor a retry whose reservation has left the window (a retry inside the window reuses its existing reservation). Accounting invariant: every entry belongs to exactly one dispatched call of an action that uses that meter; every dispatched call, and every Unknown call not yet reconciled, has one uncommitted entry on each of its action's meters; a reconciled call that was not released keeps a committed entry, and a committed entry stays until pruning drops it outside its meter's window.
9. **Ledger.** Consider any interleaving of steps from several sessions of one principal, with distinct session ids, in which each committed step that changed the stored ledger (a `ledger_sync` never does; it only brings the state up to it) was taken on a state whose ledger equals the last committed ledger (what `session_start`, `ledger_sync` and the two-version compare-and-swap of section 7 provide; every claim changes the ledger). Principal meter caps and the principal kill hold across the whole interleaving, as they do for one session. Sequential chains of sessions are the special case of one live session at a time. The sessions may run different policies (a live policy and retired ones, or the policies of two gates during a rolling deploy) when every principal meter they share has the same kind, currency and window: each claim stays within its own policy's cap, and no session prunes an entry another still counts at the time of the pruning step or later. These cross-session claims assume the sessions share the trusted monotone clock of section 10 and the binding stamps each commit attempt, compare-and-swap retries included, from it, so commits are ordered by time. The host may also set or clear the tombstone out of band: no session claims on a stored ledger that carries it, and a session that has seen it never claims again, even after it is cleared.
10. **Default deny.** Unknown and unexposed actions are never authorized and never claimed, whatever the policy-level or action-level mode.
11. **Escalation.** Once the session failure total reaches its limit, or a tool's consecutive-failure counter reaches its limit under session scope, no proposal (new or repeated) has a non-denied disposition and no dispatch is claimed until an accepted `escalation_ack` from an eligible approver that echoes the escalation count current at the acknowledgment. Under tool scope, the same holds for that tool's proposals and dispatches.
12. **Rejection memory.** Once a `(tool, digest)` is rejected in a session (the digest as proposed, as current, or of the generation the reject echoed), until a `user_initiated` turn starts no call with that pair is newly authorized (by propose, approval or edit) and no first-attempt dispatch with that pair is claimed, whether the call was proposed before or after the rejection.
13. **Expansion soundness.** If `writ check` accepts a layer-2 policy, then `check (expand p)` succeeds; `expand` is total; it is monotone (comparing resolved labels, missing labels as top, and explicit requirements excluding `permission` and `meter`); it is never weaker than any matching rule, explicit requirement, or `extends` parent. Lattice laws for each field's join are proved as lemmas.

Supporting results, also v0.1:
- **Characterization lemmas**: for every event kind, `accepted ↔` an explicit condition. Together with the witness traces, these rule out a kernel that is safe by refusing everything.
- **Witness traces**: for each disposition and reason code, a concrete trace reaching it under a witness policy, proved by `decide +kernel`.
- **Frame lemma**: a rejected event leaves the state unchanged.
- **Policy check soundness for degenerate limits**: `writ check` refuses zero windows, zero failure limits, unexposed actions whose own mode is `log_only` and mixed-currency money meters; the aim is that no theorem is vacuous or false for a checked policy.
- **Origin independence**: for each step, the verdict and state do not depend on `origin`.
- **Monotone time and seq** are enforced by the kernel.
- The well-formedness invariant `Inv` (call status consistent with records, reservations match calls, tallies duplicate-free, epochs bounded, no calls before `session_start`) holds on every reachable state.

Later:
- v0.2: closed UI catalog (`Writ.Catalog`); lethal-trifecta enforcement (a session that has ingested untrusted output and holds a `reads_private` grant or result requires per-call consent on `sends_external` actions); SEP-2848's seven conformance statements as named theorems; state migration preservation.
- v0.3: information flow (untrusted-origin data in side-effect arguments must be marked as displayed on the approval); A2A delegation (an approval bound to agent A is useless to agent B; intermediaries cannot widen consent).

### Proof architecture

- `run : Policy → List Event → State × List Verdict`; theorem 4 is stated over traces and theorem 9 over interleavings of several sessions' steps; theorems 5 and 10 over reachable states or for one step from any state; the others combine results over traces with results over reachable states or for one step from any state.
- Proof method: a history-linked invariant `Inv p s tr` proved by snoc induction over the trace, with per-event characterization lemmas between `step` and the theorems, so refactoring `step` breaks only those lemmas. `Inv` is split into per-concern structures.
- Maps use `Std.ExtTreeMap` (canonical representation, extensional equality, large lemma library with `grind` support).
- Tactics: `grind` (since Lean 4.22, extended since), `simp` for unfolding (state updaters tagged), `omega` for counters, `decide +kernel`/`rfl` for witnesses. No `native_decide` in proofs.
- Before proving, `Inv.check` runs on every state the explorer reaches, so a wrongly stated invariant fails in seconds. A spike on 2026-10-16 proved a consent invariant for a six-event mini kernel in about ten lines of tactic script, checking in 0.7 seconds; the real work is invariant strengthening.
- No second relational spec in v0.1. Veil is not used (it pins Lean 4.32 and pulls in SMT and other dependencies that conflict with the small kernel); an independent Veil model may come later as a cross-check.
- Proof status per theorem is published in the README and checked by CI (no `sorry` in released theorems).

## 9. Conformance traces, corpus and audit

Schema `writ.trace/1`, one JSON object per trace, shipped as JSONL in a versioned tarball per release (`writ-corpus-<version>.tar.gz`, built by `scripts/corpus.sh --tar`):

```json
{
  "schema": "writ.trace/1",
  "id": "consent/edit-restarts-tally/0007",
  "policy": { "...resolved layer-1 policy..." },
  "events": [
    { "event": { "type": "session_start", "seq": 1, "time": 0, "state_version": 0, "session_id": "s1",
                 "requester": "u1", "permissions": ["payments"], "approvers": {}, "ledger": {} },
      "expect": { "verdict": "accepted" } },
    { "event": { "type": "propose", "seq": 2, "time": 1, "state_version": 1, "call_id": "c1", "tool": "shop.buy",
                 "call_digest": "d1", "cost": { "amount": "1200", "currency": "USD" }, "guards": {}, "escalators": {} },
      "expect": { "verdict": "accepted", "decision": "needs_approval" } }
  ]
}
```

Plain JSON values; amounts as decimal strings; times and counts as JSON integers within plus or minus 2^53. `expect` lists only the verdict fields a trace pins (any subset of the verdict JSON, section 6). A trace may carry `policy_digest`; otherwise it is computed from `policy` as below.

Generation:
- `writ traces <policy> --depth N` explores the state space breadth-first over an abstract alphabet: one representative action per distinct requirement tuple, two call ids, two digests, four approver principals (the requester, a human, an automated approver and the reserved principal `agent`), a small time domain that crosses each TTL. States are deduplicated after symmetry reduction (canonical renaming of calls, approvers and digests; grant ids are kept, because the kernel picks grants in id order), with `state_version` and `last_seq` removed from the key (revised 2026-10-24; `docs/formats.md` gives the alphabet).
- Emitted: every accepted transition between abstract states, as the shortest trace reaching it, plus rejected transitions sampled per `(event kind, reason code)`. This keeps the corpus in the thousands to tens of thousands of traces instead of gigabytes.
- The **standard corpus** is generated from fixture policies (`corpus/standard/fixtures`) that together use every requirement feature the kernel reads except `max_failures_per_session` (a hand-written trace uses it) and, with the hand-written traces, reach every reason code, plus hand-written attack traces (`corpus/attacks`): the ASU attack catalogue (each attack whose kernel-level part Writ can express), Loopjacking substitution, the red-team scenarios (cross-session escape, rollback, quorum edit laundering, stale dialog, rejection shopping), and digest vectors. The generated traces are not committed: `corpus/standard/manifest.json` pins them in the repository by each fixture's depth, trace and state counts and the SHA-256 of its output, and the release tarball carries them (revised 2026-10-24).
- `writ oracle` reads events as JSONL on stdin and writes verdicts on stdout for random differential testing of long traces.
- `writ replay` checks stored expectations; CI runs it on the shipped corpus so the corpus cannot drift from the kernel. `scripts/corpus.sh` regenerates the standard corpus, compares it with the manifest, replays it with the hand-written traces and judges every trace with the spec-side checkers (`writ-fuzz --judge`), which restate the spec without reading the kernel.

Audit: `writ.audit/1` is a trace (events, verdicts, `policy_digest`) with host-computed hash chaining and approver identity and authentication method. An audit log is therefore a replayable conformance trace: `writ replay` shows after the fact that the host followed the kernel.

Converters (v0.2): ITF (`#meta.format: "writ/1"`) for Quint and Apalache, Dogwood `trace.log` plus `expected.out` for the subset Dogwood can express, Cedar integration-test JSON for the stateless per-call slice.

Versioning: any change to event fields, reason codes or verdict semantics bumps the schema version and gets a CHANGELOG entry. Additive optional fields bump the minor version.

## 10. Trust boundary (top of the README)

Writ's guarantees hold only if:
- every side effect goes through the kernel (complete mediation), and the mapping from a raw tool call to a Writ `tool` name is part of the host's trusted code;
- the agent cannot cause approval-plane or control-plane events, and cannot write the policy (the policy comes from outside the agent's reach, for example a pinned file or a config service; loosening it should itself require approval);
- the host computes digests per the spec and executes the exact bytes it digested; on an approver edit, the host recomputes `new_digest` from the edited arguments and `new_cost`, and a host that relays an end user's edit must not let that user lower the declared cost of their own call without the policy's consent;
- a trusted renderer, not the agent, builds the approval display from the canonical arguments, without truncation, flagging confusable and invisible characters;
- approver identities, kinds and roles are authenticated by the host, and so is the freshness of the messages that carry an approver's decision: `approve` and `reject` echo a request id, but `grant_create`, `permission_add` and `escalation_ack` name no request (`escalation_ack` carries only the escalation count it reviewed), so the kernel takes a replayed one for a fresh one, and the host must refuse one replayed from another session or from an earlier decision (for example by binding a grant's `reviewed_scope_digest` to the session id) (made precise 2026-10-24);
- event times come from a trusted, monotone server clock;
- every store is a compare-and-swap on the session state version and on the version of the principal ledger the step read (atomic over both when several sessions of a principal are live), and post-dispatch state is stored before execution;
- state carried on the client is sealed and also checked for freshness: the host keeps each session's latest `state_version` on the server, compare-and-swaps it on every step, and refuses a sealed state whose version differs (sealing gives integrity, not freshness), and never takes the principal ledger from client-carried state;
- `dispatch` immediately precedes execution, and kill is delivered with priority and aborts in-flight tools where possible;
- guard values, escalator values (on `propose` and on approver edits; they decide whether a session grant may stand in for a call), declared and actual costs, and outcomes (`declined`, `no_effect`) are reported by trusted code, or clamped by the binding as section 6 describes (from an untrusted executor, a release becomes a commit of at least the reservation, and a `declined` becomes `failed` unless the decline came through the trusted approval renderer).

Writ proves the kernel and the policy compiler. With the WASM or native build, the decision logic in the host is the proven code; only the glue (digests, event encoding, persistence) is tested, against the corpus and the oracle.

## 11. CLI

- `writ check <policy> [--tools tools.json [--server s]] [--profile id]`: validate layer 1 or 2, check the lethal trifecta, detect changed tool definitions, report the settings a standards profile of section 13 forbids.
- `writ digest <policy>`: the policy digest every `session_start` carries.
- `writ expand <policy>`: layer 2 to layer 1.
- `writ import mcp <tools.json>`: a pessimistic layer-2 draft from an MCP tool list.
- `writ traces <policy> [--depth N] [--max-states M] [--out dir]`: the explorer of section 9.
- `writ replay <traces> [--coverage]`, `writ oracle <policy>`.
- `writ diff <old> <new> <events.jsonl> [--json]`: replay recorded traffic under both policies and list changed verdicts.
- `writ explain <traces> [--id id] [--profile id]`: a readable walk-through with each verdict and reason, and a standards profile's view of each step.

v0.1-preview has `check` (layer 1 and the lethal trifecta, without `--tools`), `digest`, `replay`, `oracle` and `explain`. Delivered on main after v0.1-preview, unreleased: layer 2, so `check` validates layer 1 or 2 and `expand` prints the layer-1 policy a layer-2 policy expands to, both resolving `extends`, with the four presets as layer-2 files in `schema/presets/`; and four commands, `import mcp`, which drafts a layer-2 policy from an MCP tool list, `check --tools`, which detects changed tool definitions, `diff`, which lists the verdicts a policy change alters in recorded traffic, and `traces`, which generates the corpus of section 9, with `replay --coverage` listing the reasons and decisions a replay reached (revised 2026-10-24). Every command of this section now exists. Also delivered on main after v0.1-preview, unreleased: `check --profile mcp-tool-approval`, which reports the settings SEP-2848 forbids, and `explain --profile mcp-tool-approval`, which prints each step's SEP dispositions and SEP-2643 envelopes (section 13; revised 2026-10-25). There are no release binaries and no Reservoir listing yet: the release workflow below exists and has been rehearsed locally with `scripts/release-dryrun.sh` (every asset on macOS; build, tests and corpus in a linux/arm64 container), never run on GitHub, and both wait for the first tagged release (revised 2026-10-25).

Release binaries for linux x64 and arm64 and macOS arm64 via GitHub Actions (made precise 2026-10-25: built with `lake build writ` after the elan installer pinned as in CI, not with `leanprover/lean-action`, whose v1.6.2 installs elan from an unpinned script): `.github/workflows/release.yml` packs each as `writ-<version>-<target>.tar.gz`, holding the binary, `LICENSE` and `README.md` (its tar stream is the same on any machine for the same files, and its compressed bytes the same for a given Python and zlib), and section 12 says how a release is made. Windows on request. Listed on Lean Reservoir.

## 12. Distribution

- CI compiles the kernel to C with the pinned toolchain, vendors a GMP-free subset of the Lean runtime (Apache-2.0), and builds `writ.wasm` (single-threaded, no pthreads). Measured on 2026-10-16: a toy kernel was 200 KB (66 KB gzipped); size with the real kernel plus `Init` and `Std.Data` must be measured in the first week, with a budget of 3 MB.
- **TypeScript** (`npm`, browser and Node): the first binding. It wraps the WASM kernel, computes digests, canonicalizes arguments, manages state versions, and offers a ten-line API: `gate.propose(toolCall)` returns allowed, needs approval or denied.
- **Python** (wasmtime): second binding. Delivered on main after v0.1-preview, unreleased (revised 2026-10-25): `writ-kernel`, import package `writ` (`packages/writ-py`), runs a second, standalone link of the same kernel objects (`build/wasm/README.md`) in wasmtime and mirrors the TypeScript package synchronously in snake_case: the kernel wrapper, RFC 8785 canonical JSON written in Python, the call and tool digests, the gate with its store protocol and `MemoryStore`, the minimal path and the SEP-2848 profile, with a differential test against `writ oracle`. It has no sealed state, no public untrusted-report helper (the gate applies the clamp), no Firestore store and no framework adapters, and it is not on PyPI until the first tagged release.
- **Native bindings** (a C ABI for other languages), Go (wazero) and JVM follow, after checking WASM exception-handling support in those runtimes.
- Every binding replays the standard corpus and runs differential tests against `writ oracle`.
- **Releases** (revised 2026-10-25): one version, which `scripts/check-version.sh` checks is the same in `lakefile.toml`, `cliVersion`, `packages/writ/package.json` and its lockfile, and `packages/writ-py/pyproject.toml` and `uv.lock` (in PEP 440 form, `X.Y.Z-preview.N` written `X.Y.ZaN`), with a `## <version>` heading in `CHANGELOG.md`. A pushed tag `v<version>` runs `.github/workflows/release.yml`. It checks the version and runs the green set; builds the WebAssembly kernel with emsdk 6.0.12 and runs the npm and Python suites on it; builds the three binary tarballs, the npm tarball, the Python wheel and sdist, and the corpus tarball through `scripts/release-build.sh`; and only once a reviewer approves the `release` environment creates a draft GitHub release with every asset and `SHA256SUMS`, publishes `@anijani/writ` to npm with provenance (a preview under the `preview` dist-tag) and `writ-kernel` to PyPI by trusted publishing, then publishes the draft. Each publish step skips what is already there, so a failed publish can be re-run. Run by hand, the workflow builds and checks the same assets and publishes nothing. `scripts/release-dryrun.sh` rehearses a release locally through the same script, and `--linux` adds the build, the tests and the corpus check in a linux/arm64 container. The workflow has been rehearsed locally with `scripts/release-dryrun.sh` (every asset on macOS; build, tests and corpus in a linux/arm64 container) and has never run on GitHub.
- **Fallback**: if WASM proves impractical for a runtime, a small hand-written port certified against the same corpus and oracle (Cedar's model), clearly labeled as tested rather than proven.

## 13. Integrations and standards profiles

- **MCP SEP-2848 profile** (`writ/mcp-tool-approval`): immutable binding, `outcome-unknown` final with no re-invocation, cancel after claim is a no-op, an execution error keeps meter reservations unless `no_effect`, SEP disposition strings, SEP-2643 structured-denial envelopes (`remediation: available` for needs-approval, `unavailable` for denials; a per-reason disclosure posture). The profile keeps SEP terms out of the core so the draft can change. Delivered on main after v0.1-preview, unreleased (revised 2026-10-25): the profile id is `mcp-tool-approval`, in `Writ/Profile/McpToolApproval.lean`. It maps each terminal call status to its SEP disposition (a cancelled call to SEP-2663's `cancelled`) and each needs-approval, denial or rejection to its SEP-2643 envelope, following the draft pinned in `corpus/sep-2848.json`; every reason discloses its code, its retry class and its reviewed model message, and nothing else. `writ check --profile` makes `retry_after_unknown` an error and `max_attempts` above 1 without it a warning; `writ explain --profile`, WebAssembly function 10 and both bindings expose the tables, and `profile_unknown_final` proves that no dispatch of an Unknown call is accepted under a policy without profile errors. Immutable binding is SEP-2848's binding of an approval to the call digest, which the kernel enforces whatever the policy's `binding` field says, and cancel after claim and reservations on execution error are kernel rules (section 6), so the profile checks none of them (`docs/formats.md` maps each to its rule; made precise 2026-10-25).
- **MCP gateway gate** (v0.2): a standalone MCP proxy, an agentgateway `ExtMcp` guardrail service (fail closed), a Docker MCP Gateway `exec` interceptor; MRTR `requestState` minted with principal, call digest, epoch, nonce and TTL, single use enforced server side. Writ runs beside Cedar-based gateways such as ToolHive, not in place of them.
- **Framework adapters**: Vercel AI SDK `toolApproval` first (v0.1-preview), then LangGraph and OpenAI Agents SDK, then Claude Agent SDK. Adapters refuse framework features that would weaken guarantees unless the policy allows them (for example OpenAI `alwaysApprove` maps to a session grant and needs `any_args`).
- **A2A** (v0.3): `AUTH_REQUIRED` maps to `needs_approval`; Writ defines the A2A extension that the spec now says must define authorization scope; outcome-unknown is carried in metadata because A2A has no such state.
- **AP2 / ACP / x402**: amounts in minor units with ISO 4217 (AP2 `payment.budget.max` is in major units and is normalized on import); open-mandate constraints map to meters (`budget`), grant `max_uses` (`agent_recurrence`), grant `not_before`/`expires_at` (`execution_date`) and `max_per_call` (`amount_range`); the call digest may be an external `checkout_hash`; idempotency keys pass through.
- **OpenTelemetry**: emit the proposed `gen_ai.tool.call.decision` event (OTel PR #535) plus `writ.*` attributes for lifecycle, epoch, reason and state version. The offline checker maps GenAI spans to events and treats gaps as `unknown`.
- **Cedar export** of the stateless slice, with a proof against cedar-spec's Lean semantics as a stretch goal.
- **AADP** (IETF draft-saha-aadp-03): publish a mapping; its decide/report, reservations and single-use approvals correspond to Writ's events.

## 14. Prior art and positioning

- ASU "Approve What, Exactly?" (arXiv 2610.21063, Oct 2026): Tamarin proofs of approval binding, single use, grant scope and max uses, plus an attack catalogue. Writ cites it, imports its attacks as fixtures, and differs by proving stateful kernel semantics (quorum, meters, epochs, escalation, outcome-unknown) and shipping the proven kernel as a library with a corpus.
- AWS Dogwood and AgentCore Policy: temporal Cedar superset, LOG_ONLY and ENFORCE modes, semi-formal spec, no mechanized proofs found. Writ is complementary: proven semantics and a corpus Dogwood behavior can be compared against.
- Cedar and cedar-spec: the method Writ copies (Lean model, differential testing, exported corpus), for stateless authorization.
- MCP SEP-2848 and SEP-2643: draft approval standards that Writ's MCP profile follows.
- AADP: a near-duplicate event model without formal semantics or vectors.
- LLMbda calculus (Lean, information flow, no public code), Lean4Agent (Lean workflow contracts), Progent (per-tool policies, unproven), Loopjacking and arXiv 2609.29095 (attack and duplicate-execution evidence used as fixtures).

## 15. Milestones (revised 2026-10-25)

- **v0.1-preview**: executable kernel (all v0.1 rules), `writ check/digest/replay/oracle/explain`, the hand-written corpus (six adopter trace files plus the SEP-2848 traces), `writ.wasm`, the TypeScript package `@anijani/writ` with the gate and the minimal path, the Vercel AI SDK adapter, the LangGraph example, a local browser playground on the same WASM (write a policy, click through events, see verdicts, step through the corpus traces), docs with trust boundary and proof status table. Theorems 1 to 12 and the supporting results are proved, and the README says exactly which.
- **Delivered on main after v0.1-preview, unreleased**: layer 2 (labels, rules, `extends`, `writ expand` and layer-2 `writ check`) with theorem 13 proved (`docs/theorems.md`), so every v0.1 theorem and supporting result is now proved; the four presets (`schema/presets/`); the `writ-tool-v1` tool digest and the per-action `source` field; `writ import mcp` and `writ check --tools`; `writ diff`; the trace generator `writ traces` (with `writ replay --coverage`) and the standard corpus it generates from the fixture policies in `corpus/standard`, pinned by its manifest and packed into the release tarball by `scripts/corpus.sh --tar`; the hand-written attack traces in `corpus/attacks`; and the spec-side judge `writ-fuzz --judge`, which checks every corpus trace against `WritSpec`. Then (revised 2026-10-25) the Python binding `writ-kernel` with the gate, the store protocol and the minimal path (section 12), on a standalone link of `writ.wasm`; the MCP SEP-2848 profile `mcp-tool-approval` with `writ check --profile`, `writ explain --profile`, WebAssembly function 10, both bindings and `profile_unknown_final` (section 13); and the release workflow with `scripts/check-version.sh` and the local rehearsal `scripts/release-dryrun.sh` (section 12). The workflow has been rehearsed locally with `scripts/release-dryrun.sh` (every asset on macOS; build, tests and corpus in a linux/arm64 container) and has never run on GitHub. The next release carries them.
- **v0.1**: the first tagged release through that workflow, which publishes the release binaries, `@anijani/writ` on npm, `writ-kernel` on PyPI and the corpus tarball; all of these wait for it. The Reservoir listing follows once the repository and the tag are public. The release version follows section 9's rule: the additive fields since the preview make it a minor bump, `0.2.0-preview.1` unless the owner decides otherwise. Milestone names are not release versions.
- **v0.2**: MCP gateway gate, LangGraph and OpenAI adapters, Python framework adapters, catalog and lethal-trifecta theorems, converters, OTel event, state migration.
- **v0.3**: native bindings, Go and JVM, information flow, A2A extension, Cedar export proof.

Estimated effort for v0.1 by an experienced Lean developer: kernel and trace spec 2 to 3 weeks, theorems 1 to 12 four to six weeks, theorem 13 two weeks, explorer and corpus 2 weeks, CLI, JSON, WASM build and TypeScript binding 3 to 4 weeks.

## 16. Decisions made by the designer (for review)

- Kernel knows requirements only; risk vocabulary is user-defined labels plus shipped presets.
- License Apache-2.0; Lean 4.35.0; no Mathlib; kernel uses `Init` and `Std.Data` only.
- Quorum counts distinct principals; any eligible reject is a veto; an edit starts a new generation that every counted approver must review; `human_only` defaults to true.
- Grants need an approver holding the action's role, never stand in for quorum above 1, and need use and time limits when unrestricted.
- Calls survive `turn_end`; only reset, kill and session end close them.
- Meters support money and call counting, session and principal scope, windows and optional caps; an action may draw on several meters; reset never refunds; outcomes commit the reported actual cost (partial captures included) at the time of the report; `declined` and `no_effect` release.
- `outcome-unknown` is final unless the action opts into retries; cancel after dispatch is a no-op (SEP-2848 alignment).
- Rejected `(tool, digest)` pairs are blocked until a user-initiated turn.
- Escalation counts per-tool consecutive failures and a session total, blocks proposals and dispatches (per session, or per tool with `escalation_scope: tool`), and clears only through an `escalation_ack` that echoes the current escalation count.
- A policy change ends the session; the ledger carries principal state over.
- Examination revisions (2026-10-17, revised after a builder review the same day), after adopter studies (web chat SDK, coding agent, LangGraph, MCP gateway, enterprise payments, device split), two red teams and a trace fuzzer: consent as a conjunction of clause groups with optional `distinct`; grantable escalators; several meters per action, calls meters, optional caps, actual-cost commits at report time and retry re-reservation outside the window; a `declined` outcome that is not a failure and outcomes recorded by `reconcile`; repeated proposals report the current disposition; stale-generation vetoes count; per-action TTLs; tool-scoped escalation and acknowledgments bound to an escalation count; grant `max_cost`; `ledger_sync` and a ledger version bump on every claim for several live sessions per principal; audit-only fields moved to the trace format. Deferred to later plans: per-action message overrides are validated but not applied (the binding applies them), returning `needs_approval` with the new `request_id` after an approver edit that does not authorize the call, live policy updates and a default for unknown tools, principal-scoped and pattern grants ("always allow in this repo"), plan consent objects, agent identity on proposals, permission wildcards, several ledgers per session (tenant scope), refunds, compaction of terminal calls, aggregation of windowless ledger entries, a `writ check` warning for a grant `max_cost` whose currency differs from the action's money meter, a per-meter overrun tolerance, principal-scoped escalation and rejection memory.
- Hardening revisions (2026-10-18), after a red team and a trial integration of the preview: a killed session accepts only the events that settle or end it; a call-scoped event that does not fit the call's status is rejected with a reason naming that status; `declined` releases like `no_effect`; overruns are reported in the verdict; committed entries outside their window are pruned, and `ledger_sync` accepts a ledger another session pruned and, on an ended session, one whose tombstone was cleared; unknown-tool proposals leave no record; event strings are limited to 512 bytes; the idempotency key includes the principal; bindings bound each session's stored state and check the freshness of client-carried state. Cleanup revisions (2026-10-19), before the proofs: each entry list is pruned only by the policy's meters of its own scope, so a session meter never prunes the principal ledger; a `session_start` whose session id already owns ledger entries is rejected `already_started`.
- v0.1-preview ships the WASM kernel and TypeScript package before all proofs are done, with an exact proof status table.
- Implementation simplifications (2026-10-17): identifiers are `String` rather than a generic type (exploration uses short canonical strings); escalators map only to stricter `consent` in v0.1; dispatch attempts beyond `max_attempts` are rejected rather than counted as failures; a `kill` is never shadowed by `log_only`; grants are valid while `not_before <= time < expires_at`.

## 17. Decided by the project owner

- No upstream contribution work (MCP SEPs, OpenTelemetry proposals, outreach). Writ stands on its own; standards appear only as compatibility profiles inside Writ.
- Writ is a personal project of the owner. Repository `github.com/aniJani/writ` (free as of 2026-10-16); Lean package `Writ` on Reservoir from that repo; commits use the owner's personal git identity. The npm scope `@writ` is already taken, so the npm package is `@anijani/writ` if the owner's npm username matches, otherwise the unscoped `writ-kernel` (free on npm and PyPI). PyPI package `writ-kernel`. A transfer to a neutral organization later keeps GitHub redirects.

## 18. Left to the builder

- Exact Lean data structures within the constraints above.
- The fixture policy set, as long as it covers every requirement combination and reason code.
- CLI output formatting and message wording (default reason messages are reviewed before v0.1).
- Repository layout and CI details.
