# Writ JSON formats and CLI reference

This page describes every JSON document Writ reads or writes: policies, events, verdicts, state and conformance traces, plus the `writ` command. It is written for people who build agents, hosts and bindings in any language. The Lean code in `Writ/Codec/` and `Writ/Json/` is the source of truth; the examples below are real files, replayed by `scripts/cli-test.sh` (they live in `tests/cli/`).

## Rules for all formats

- Documents are UTF-8 JSON. A byte order mark at the start is rejected (`byte order mark at start of input is not allowed`), because the digest is of the document as written. Field names are snake_case, and so are the values of every enumeration (reasons, decisions, statuses, outcomes, modes, scopes, flags, kinds).
- Numbers are JSON integers within plus or minus (2^53 - 1). A fraction, an exponent or a larger integer is a parse error. Times are integer milliseconds. Counts, versions, generations and sequence numbers are non-negative integers.
- Amounts are decimal strings of at most 78 digits (longer is an error such as `cost.amount: amount has more than 78 digits`): `"0"`, `"1200"`. No sign, no leading zero, no spaces, no fraction, and no JSON number. Cost `amount`, `actual_cost`, ledger amounts and the grant cost counters in state are amounts. The exception is a meter's `cap` and `max_per_call` in a policy, which are plain JSON integers.
- In an event, every string (identifiers, digests, map keys, roles, permissions) is at most 512 UTF-8 bytes; a longer one is a decode error that names its path. Amounts keep their 78-digit limit. `origin`, `audit` and the `ledger` object of `session_start` and `ledger_sync` are not limited, because the ledger is produced by the kernel and the binding, not by the host's event stream.
- A field name the decoder does not know is an error that names the JSON path, for example `actions.buy.consnet: unknown field`. A misspelled optional field is never silently ignored.
- A duplicate key in one object is a parse error. Nesting deeper than 128 levels is a parse error. Empty input and trailing data after a value are errors.
- A string may contain any Unicode character. Escapes follow JSON; a lone surrogate (`"\ud800"`) and an unescaped control character are errors.
- Name maps (guards, escalators, approvers, meters, actions, grants, calls) are JSON objects with unique keys. Decoding a document and encoding it again gives the same value for everything reachable from JSON input, but for a policy not the same document: `$schema`, `review`, `messages`, `source`, explicitly written defaults and `permission: null` are dropped. The policy digest is therefore always of the document as written, never of a re-encoding. A Lean caller that builds a list with a repeated name gets the first entry, which is also the entry the kernel reads.
- Optional fields with a default are left out when written if they hold the default (policies, events, ledgers). State writes every top-level field, but the nested `ledger` and the entries of `session_meters` omit their defaults as in events (`"ledger":{}`, and no `excess` or `excess_at` on an entry that has none). Readers must accept both forms.

### Canonical JSON and the policy digest

Canonical JSON is the compact form with object keys sorted by UTF-16 code units (so `"\ud83d\ude00"` sorts before `"\uffff"` and `"\u00e9"` after `"z"`), no whitespace, and minimal escapes: `"` and `\` are escaped; U+0008, U+000C, U+000A, U+000D and U+0009 are written `\b`, `\f`, `\n`, `\r` and `\t`; every other character from U+0000 to U+001F is written `\u00xx` with lowercase hex; everything else, U+007F included, is raw UTF-8.

The policy digest is `"sha256:"` followed by the lowercase hex SHA-256 of the canonical JSON of the policy document as written. Reformatting the file (indentation, key order) does not change the digest; changing a value, adding a field or adding `"$schema"` does. The digest is computed over the document, not over the decoded policy, so a field with its default value written out gives a different digest from the same field left out.

```sh
$ writ digest tests/cli/policies/formats-shop.json
sha256:866cd32f034a15421198ab518d1e23a34f4acfb4ba2fb20884f9af5fca97a6dd
```

### Call digests

A tool call's digest is `"sha256:"` plus the lowercase hex SHA-256 of its canonical `writ.call.v1` preimage, defined in section 6 of `docs/design.md`. Arguments are canonicalized with RFC 8785 and a stricter number rule. `corpus/digests/call-v1.jsonl` holds the test vectors, and `corpus/digests/README.md` lists the rules they pin. The TypeScript package computes it with `callDigest`, the Python package with `call_digest`.

### Tool digests

A tool definition's digest, `writ-tool-v1`, is `"sha256:"` plus the lowercase hex SHA-256 of the RFC 8785 canonical JSON of `{"t": "writ.tool.v1", "tool": <tool>}`, where `<tool>` is the tool object exactly as the server lists it, every member included (`name`, `title`, `description`, `inputSchema`, `outputSchema`, `annotations`, `_meta` and any other). Key order and whitespace never change the digest; any change of content (a description, a schema, an annotation) does. It is the `tool_digest` an action records in `source` (see Policy) and the `tool_digest` a host puts in each call digest's preimage, so a changed tool definition invalidates the approvals given for the old one.

Tool definitions are written by MCP servers, not by Writ, so their numbers are not limited to integers. A number literal is accepted when it has at most 15 significant digits (the digits from its first to its last nonzero digit, so `100`, `2.0` and `1.000` count one) and its magnitude is 0 or within 1e-300 to 1e300. It is printed as ECMAScript prints the nearest double, which for such a literal is its own digits, normalized: `0.5`, `1.5e3` gives `1500`, `-0` gives `0`, `1E-7` gives `1e-7`, `2.0` gives `2`, `1e21` gives `1e+21`. Any other number is refused, with an error that names its JSON path and position, such as `[0].inputSchema.maximum: number has more than 15 significant digits at line 1, column 39`. Duplicate keys, a lone surrogate, a byte order mark and nesting deeper than 128 levels are refused as in every Writ document. The `writ` command counts those 128 levels from the tools.json document, so a tool inside a bare array has one level fewer and a tool inside a `tools/list` result two fewer, while `toolDigest` in `@anijani/writ` counts them from the tool.

A tools.json document is either an MCP `tools/list` result, `{"tools": [...], "nextCursor"?: string | null, ...}`, or a bare array of tool objects. The result's other members, `_meta` included, are ignored whatever their type, though the whole document must still parse under the rules above; `nextCursor`, when present, must be a string or null, and null counts as absent. Each tool must be an object with a string `name`, and a name listed twice is an error (`tools[1].name: duplicate tool name "t"`). Writ reads annotations from `tool.annotations`: MCP's `readOnlyHint`, `destructiveHint`, `idempotentHint` and `openWorldHint`, and also the SEP-2793 risk metadata (`riskLevel`, `blastRadius`, `reversibility`, `approvalRecommendation`). SEP-2793 is a proposal, so where it puts those fields is an assumption that may change with it.

`corpus/digests/tool-v1.jsonl` holds the test vectors, and `corpus/digests/README.md` describes them. The TypeScript package computes the digest with `toolDigest`, the Python package with `tool_digest`.

### Versions and frozen formats

Writ has two versions. The release version (`0.1.0-preview.1`) is that of the Lean package, the `writ` command, `@anijani/writ` and the Python package `writ-kernel`, which writes it in PEP 440 form (`0.1.0a1`). The kernel version (`0.1.0`) names the kernel's semantics and is recorded in every state as `kernel_version`; a kernel refuses a state of another kernel version (see State), so the kernel version changes only when the semantics do, and while it stays 0.1.0 a state moves between 0.1.0-preview.1 and 0.1.0 unchanged. `writ --version` prints both, with the trace and state schemas:

```sh
$ writ --version
writ 0.1.0-preview.1 (kernel 0.1.0, trace writ.trace/1, state writ.state/1)
```

From 0.1.0-preview.1 these formats are frozen: `writ.trace/1`, `writ.state/1`, the policy format `"writ": "0.1"` (`schema/writ.policy-0.1.schema.json`), the reason codes and retry classes in `schema/reasons.json`, and the `writ-call-v1` call digest. The `writ-tool-v1` tool digest is frozen from the release that introduces it (the next release); a change to it would be `writ-tool-v2`. A change to event fields, reason codes or verdict semantics bumps the version of every format it touches (`writ.trace/2`, `writ.state/2`, `"writ": "0.2"`, `writ-call-v2`) and is listed in `CHANGELOG.md`; an additive optional field bumps the release's minor version and is listed there too. Reason codes appear in three formats: in trace verdicts, in state as the reasons of `denied` and `denied_at_dispatch` calls, and as the keys of a policy's `messages`. So any change to the reason codes (a new, renamed or removed code) or to the retry classes bumps `writ.trace`, `writ.state` and the policy format together. The model and user message texts, the WebAssembly ABI, the `@anijani/writ` and `writ-kernel` APIs and the MCP SEP-2848 profile's strings and envelopes are outside this rule; their changes are listed in `CHANGELOG.md` as well.

## Policy

A policy is one JSON object. Only `"writ": "0.1"` is required. A tool that is not listed in `actions` is denied (`unknown_tool`); the proposal counts toward the proposal limits but leaves no call record, so its `call_id` stays unused. The editor-facing JSON Schema is `schema/writ.policy-0.1.schema.json`; set `"$schema": "../writ.policy-0.1.schema.json"` (that relative path works from `schema/examples/`; any string is accepted) to get validation and completion. `schema/examples/assistant.json` is a larger sample, for a general-purpose assistant. The schema checks shape only; `writ check` adds the cross-field rules below.

```json
{
  "writ": "0.1",
  "approver_roles": ["owner"],
  "meters": {
    "spend": { "currency": "USD", "cap": 5000, "scope": "principal", "window_ms": 86400000 }
  },
  "limits": { "approval_ttl_ms": 600000, "max_consecutive_failures": 3 },
  "actions": {
    "search": { "permission": "shop.read" },
    "buy": {
      "permission": "shop.buy",
      "consent": "per_call",
      "guards": ["card_on_file"],
      "meters": ["spend"],
      "idempotent": true
    }
  }
}
```

Top-level fields: `writ` (required, `"0.1"`), `$schema`, `mode` (`enforce` or `log_only`), `approver_roles`, `escalation_roles`, `meters` (name to meter), `limits`, `actions` (name to requirements), `binding` (`mutable` or `immutable`, default `mutable`; with `immutable`, approvers may not edit a call's arguments and an `approve` with `edit` gets `edit_not_allowed`), `kill_scope` (`session` or `principal`, default `session`; with `principal`, a `kill` also sets the principal tombstone in the ledger).

Action fields (all optional): `permission` (string or null), `consent`, `consent_if_cost_over` (`{ amount, currency }`; the action's own consent is waived when the call's cost is strictly below this amount in the same currency, and applies otherwise; escalator consent still joins, and it has no effect when `consent` is `none`), `escalate` (name to `{ consent, grantable }`; `consent` is required), `grantable` (`{ scope, max_uses, max_duration_ms, any_args, allow_any_args_metered }`; `scope` is `turn` or `session`, and `scope` and `max_uses` are required), `idempotent`, `retry_after_unknown`, `max_attempts` (default 1), `guards` (names), `meters` (names), `approval_ttl_ms`, `authorized_ttl_ms`, `exposed` (default true), `mode`, `flags` (`reads_private`, `ingests_untrusted`, `sends_external`), `review` (an object the kernel accepts and ignores), `messages` and `source`. `messages` maps reason codes to `{ model?, user? }` strings; an unknown code or field is an error such as `actions.a.messages.guard_flase: unknown reason code`. Messages are validated but not stored or applied in 0.1, and `writ check` warns with `messages_not_applied`.

`source` records the MCP tool an action was written for: `{ "tool_digest": "sha256:<64 lowercase hex digits>", "server"?: string, "tool"?: string, "annotations"?: object }`. `tool_digest` is required and is the tool's `writ-tool-v1` digest (see Tool digests). `tool` is the tool's name on the server and defaults to the action name. `server` names the server that lists it. `annotations` holds the server's annotations as it wrote them, for the author to read (`writ import mcp` writes each number in its canonical form, so `1.0` becomes `1`, `1e2` becomes `100` and `-0` becomes `0`): they are the server's untrusted claims, and nothing applies them. Being part of the policy, `annotations` follows the policy's number rule: integers within plus or minus (2^53 - 1) only. `server` and `tool` are at most 512 UTF-8 bytes, and any other key is an error such as `actions.web.fetch.source.digest: unknown field`. The kernel accepts `source` and ignores it, as it does `review`; it is for comparing a policy with a server's current tool list. The field is additive and optional, so the format version stays `"writ": "0.1"`.

`consent` takes one of these forms:

| Form | Meaning |
|---|---|
| `"none"` | no approval needed (the default) |
| `"per_call"` | one human approver, any approver role |
| `{ "quorum": 2, "roles": ["finance"], "human_only": true, "exclude_requester": true }` | one clause; only `quorum` is required |
| `{ "all": [clause, ...], "distinct": false }` | every clause must be met; `distinct` stops one person filling two clauses |
| `{ "groups": [group, ...] }` | several groups, all of which must be met |

A meter is either money (`"currency": "USD"`) or a call counter (`"unit": "calls"`), never both. Its `cap`, `window_ms` and `max_per_call` are integers, `scope` is `session` or `principal`.

### What `writ check` reports

`writ check` exits 0 when there are no errors, 1 when there are, and prints warnings either way. With `--tools`, it also reports changed tool definitions (see Changed tool definitions), and with `--profile mcp-tool-approval` the settings SEP-2848 forbids (MCP SEP-2848 profile). Errors: a meter or role that is not defined, a zero quorum, empty roles, a consent that needs approval with no `approver_roles`, a grantable whose consent needs more than one approval or whose action needs no consent, `max_uses` 0, `any_args` without `max_duration_ms` or on a metered action without `allow_any_args_metered`, `retry_after_unknown` without `idempotent`, `max_attempts` 0, zero failure limits, a zero window, mixed currencies in one action, `max_per_call` on a calls meter, `exposed: false` with `mode: log_only`, a meter or escalator listed twice, and a consent group with no clauses (`empty_consent_group`, which would allow everything). The list includes `grantable_escalator_without_grantable` and `unknown_escalation_role`. Warnings: `lethal_trifecta`, `no_approval_ttl`, `zero_ttl`, `cost_threshold_unmetered`, `retries_exceed_failure_limit`, `cost_threshold_without_consent`, `messages_not_applied`, `meter_without_cap`, `principal_meter_without_window`, `per_call_above_cap`, `retry_without_attempts`. The last four flag meters and retries that do less than they seem to:

| Code | Message |
|---|---|
| `meter_without_cap` | meter "{m}" has no cap, so it records usage but never denies a call |
| `principal_meter_without_window` | principal meter "{m}" has no window_ms, so its cap is a lifetime limit for each principal |
| `per_call_above_cap` | meter "{m}" has max_per_call above its cap, so the cap denies calls the per-call limit allows |
| `retry_without_attempts` | retry_after_unknown is set but max_attempts is 1, so an unknown call can never be retried |

A meter without a cap stays valid, because recording usage before choosing a cap is a supported use; it is only a warning.

```sh
$ writ check tests/cli/policies/formats-err-meter.json
error: a: it uses meter "nope", which is not defined
error: a: it needs approval but the policy has no approver roles
warning: some actions can need approval but no approval_ttl_ms is set, so requests never expire
2 errors, 1 warning
$ echo $?
1
```

`--json` prints one object with `ok`, `errors`, `warnings` (each `{ code, action?, message }`) and `policy_digest`:

```sh
$ writ check tests/cli/policies/formats-err-warn.json --json
{"ok":true,"errors":[],"warnings":[{"code":"no_approval_ttl","message":"some actions can need approval but no approval_ttl_ms is set, so requests never expire"}],"policy_digest":"sha256:025cb1c0c17c80fe793ca5ca9816ede2eaa8de5740082d37c017e535b92679f4"}
```

### Policy errors

A policy that cannot be parsed or decoded is exit 2, with one line on stderr naming the file and the path:

| Input | Error |
|---|---|
| `{"writ":"0.1","actions":{"buy":{"consnet":"per_call"}}}` | `actions.buy.consnet: unknown field` |
| `{"writ":"0.2"}` | `writ: unsupported version "0.2", expected "0.1"` |
| `{"writ":"0.1","meters":{"m":{"unit":"calls","cap":1.5}}}` | `only integers are allowed at line 1, column 52` |
| `{"writ":"0.1","actions":{"a":{},"a":{}}}` | `duplicate key "a" at line 1, column 33` |
| `{"writ":"0.1","actions":{"a":{"consent_if_cost_over":{"amount":"01","currency":"USD"}}}}` | `actions.a.consent_if_cost_over.amount: expected no leading zero` |
| `{"writ":"0.1","actions":{"a":{"consent":"always"}}}` | `actions.a.consent: unknown value, expected "none", "per_call" or an object` |

Each stderr line starts with `error: <file>: `. These inputs are in `tests/cli/policies/formats-err-*.json`.

## Layer 2: labels, rules and extends

A layer-2 policy labels its actions, derives their requirements from rules, and can extend other policy files. `writ expand` turns it into the layer-1 policy the kernel runs, and `writ check` checks it. The layer-2 fields are additive optional fields of the `"writ": "0.1"` format, so the format version does not change. The kernel, `Writ.Api`, the WebAssembly build and `@anijani/writ` accept only layer 1: a layer-2 document passed to them still fails on its unknown fields, and so do `writ digest` and `writ oracle`, which point at `writ expand` instead. A document is layer 2 when it has a top-level `extends`, `labels` or `rules`, or an action with `labels`. Any other document is a layer-1 policy and goes through the layer-1 decoder unchanged, so a misspelled key (`"label"` on an action) is still an `unknown field` error.

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

This is `tests/cli/layer2/spec-example.json`, the example in section 5 of `docs/design.md`. It extends `tests/cli/layer2/org-baseline.json`, which declares the same `risk` dimension and lists `vm.status` labeled `read` and `vm.terminate` with no label, so `vm.terminate` takes the strictest value, `destructive`, and both rules apply to it:

```sh
$ writ expand tests/cli/layer2/spec-example.json
{"actions":{"vm.restart":{"consent":"per_call","permission":"vm.power"},"vm.status":{"permission":"vm.read"},"vm.terminate":{"consent":"per_call","exposed":false,"permission":"vm.admin"}},"approver_roles":["owner"],"writ":"0.1"}
```

### Fields

- `writ` is required, as in every policy.
- `labels` maps a dimension name to `{ "order": [values] }`, least to most risky, with at least one value and no value twice.
- An action's `labels` maps dimensions to values. An action that does not label a declared dimension takes that dimension's strictest (last) value.
- `rules` is a list of `{ "when": {...}, "require": {...} }`, and both fields are required. `when` maps dimensions to `">=value"`; a rule matches an action when every dimension it lists resolves to that value or above. `"when": {}` matches every action.
- `require` sets only strictness-ordered fields: `consent`, `grantable`, `exposed`, `idempotent`, `retry_after_unknown`, `guards`, `flags` and `mode`. Any other action field there is a decode error such as `rules[0].require.permission: not a strictness-ordered field`.
- `grantable` in a rule is a limit, not a grant. Absent, it constrains nothing; `null` forbids it; an object `{ scope?, max_uses?, max_duration_ms?, any_args? }` caps the action's own `grantable` (`turn` is stricter than `session`, smaller numbers and `any_args: false` are stricter). Rules never make an action grantable.
- `extends` is a list of paths of other policy files, each relative to the directory of the file that lists it. An empty path is a decode error (`extends[0]: expected a non-empty path`).

### Extends

`writ check` and `writ expand` read the extended files depth-first in `extends` order: a file, then the files it extends, then the next file in the list. Files are identified by their real path, so a file reached twice, by any spelling or through a symbolic link, is read once: a diamond (two parents that extend one grandparent) works and the grandparent's problems are reported once. A chain may pass through at most 8 files below the policy named on the command line, and all the chains together may reach at most 256 distinct files. An `extends` cycle, a file that cannot be read, a deeper chain and a 257th file are errors that name the chain where they occur, with exit 1:

```sh
$ writ check tests/cli/layer2/cycle-a.json
error: extends forms a cycle: tests/cli/layer2/cycle-a.json -> tests/cli/layer2/cycle-b.json -> tests/cli/layer2/cycle-a.json
1 error, 0 warnings
```

An extended file that is not UTF-8, does not parse or does not decode is exit 2, as for the file named on the command line. Paths in messages are as the command line and the `extends` lists spell them, joined and with `.` and `..` folded, never the real paths, so messages do not depend on the machine. When folding would name a different file, as a `..` after a symbolic link can, the path is shown joined but not folded. Each file read through `extends` goes through the same parser limits as any policy.

An extended policy may contain only `writ`, `$schema`, `extends`, `labels`, `rules` and `actions`. Policy-level fields (`approver_roles`, `escalation_roles`, `meters`, `limits`, `mode`, `binding`, `kill_scope`) come from the policy named on the command line; an extended policy that writes one, even at its default, is a `parent_policy_field` error. Label dimensions merge across the files, and a dimension declared with two different orders is a `conflicting_dimension` error.

An extended policy's labels and rules may use only the dimensions that it declares or that the files it extends, directly or not, declare. A label or `when` on any other dimension is an `unknown_label_dimension` or `unknown_rule_dimension` error in that file, even when the policy named on the command line declares the dimension, and a value is checked against the order that file sees. So an extending policy cannot give a parent's labels an order of its own that turns the parent's rules off. The policy named on the command line may use the dimensions of every file.

A policy that extends at least one file may not set the policy-level `mode` to `log_only`, which would only log every action the files it extends require: that is an `extends_log_only` error. It may write `"mode": "log_only"` on its own actions. On an action that a file it extends also names, `log_only` takes effect only when every file naming the action says so; otherwise the action takes the policy-level mode (`tests/cli/layer2/team-action-log-only.json`).

Extending never weakens the rules and per-action requirements of the files a policy extends, but the extending policy owns the policy-level settings: `approver_roles` and `escalation_roles` (who may approve), meter definitions and caps, and `limits`, TTL limits included. A team policy can widen `approver_roles`, add an uncapped meter or raise `approval_ttl_ms` over an organization baseline and still pass `writ check` (`tests/cli/layer2/team-log-only.json` does all three, and fails only on its `mode`). Whoever deploys a policy must vet those settings and confirm that it extends the intended baseline.

### How an action expands

The expanded policy has the policy-level fields of the policy named on the command line and one action for each name that any of the files lists under `actions`. Each action is built in four steps.

1. **Every file that names the action speaks for its whole strictness.** Its requirements, defaults included, are joined field by field, the strictest value winning:
   - `consent`: the union of the groups, equal groups kept once, so every file's groups must all be met.
   - `grantable`: present only if every naming file writes one, with the smaller limits.
   - `exposed`, `idempotent` and `retry_after_unknown`: true only if every naming file has true (an unwritten `exposed` is true, an unwritten `idempotent` or `retry_after_unknown` false).
   - `guards` and `flags`: the union.
   - `mode`: `enforce` if any naming file says so; `log_only` only if every naming file says so; otherwise unset, so the action takes the policy-level mode.
   - `consent_if_cost_over`: the smallest amount when every naming file writes one in the same currency, absent otherwise. Different currencies are also a `conflicting_currency` error.
   - `escalate`: the union by reason; a reason written in several files gets every file's consent and is grantable only if all of them say so.
   - `max_attempts`: the smallest, an unwritten one counting as 1.
   - `approval_ttl_ms` and `authorized_ttl_ms`: the smallest over the files that write one; when none does, the action defers to the policy-level limit.

   So a team policy that names an organization's action only to add a guard must repeat its labels, `grantable`, `idempotent`, `retry_after_unknown`, `consent_if_cost_over` and `max_attempts`, or it gets the strictest values.

   A rule that sets `idempotent: false` on an action that writes `retry_after_unknown: true` leaves the expanded action with `retry_after_unknown` but not `idempotent`, which the layer-1 check refuses at that action (`retry_needs_idempotent`), so the policy fails closed. The fix is not to write `retry_after_unknown` on that action.
2. **Labels.** Per declared dimension, the action gets the strictest value over every file that names it, where a file that does not label the dimension counts as its strictest value.
3. **Rules.** Every rule of every file whose `when` holds for those labels is joined in, a field the rule does not set staying as it is.
4. **Grants.** When the consent then has a clause with a quorum above 1, or a `distinct` group of more than one clause, `grantable` is dropped (a grant stands in for one approval). An action without `grantable` keeps no grantable escalators: they become non-grantable, and a grantable escalator with no consent groups is dropped.

`permission`, `meters`, `review`, `messages` and `source` are per action only: no rule and no join sets them, and every file that writes one for an action must write the same value, or it is a `conflicting_field` error. `guards` and `flags` come out sorted and deduplicated when a join touched the action (a second file names it, or a rule matches it); otherwise they are as written.

Section 8's theorem 13 is proved for this expansion (`docs/theorems.md`): the expanded action is never weaker than any file's entry for it, any rule that matches it, or the expansion of any policy it extends, and a policy that `writ check` accepts expands to one that passes the layer-1 check. A team policy that extends an organization baseline and tries to lower a quorum, expose a hidden action or allow more grant uses (`tests/cli/layer2/team.json` over `org.json`) expands to the baseline's strictness or more. That covers the baseline's rules and per-action requirements; the policy-level settings are the team's (see Extends).

Known limit: expansion and the layer-2 check take time quadratic in the number of actions, as the layer-1 check already does.

### `writ expand` and `writ check`

`writ expand <policy.json> [--out <file>]` prints the expanded policy as canonical JSON on one line, so its digest is stable: `writ digest` of the output is the digest that `session_start` carries. The layer-1 policy does not store `review`, `messages` and `source`, so `writ expand` copies each action's `review`, `messages` and `source` into the output from the files that write them. `$schema` and fields written at their default are left out, and a layer-1 policy that passes `writ check` expands to its own canonical form. Because `$schema` and default-valued fields are dropped, the digest of the output can differ from `writ digest` of a source policy, even a layer-1 one: a host must load the expanded file for its `session_start` digests to match. `--out` writes the line to a file instead of stdout. `writ expand` runs the same check as `writ check`: when it reports errors (`extends` problems, layer-2 problems, or errors of the expanded policy), `writ expand` prints them instead of the policy, writes nothing to `--out` and exits 1. Warnings do not stop it. So every policy `writ expand` prints passes `writ check`.

`writ check` on a layer-2 document reports the `extends` and layer-2 problems, then the errors and warnings of the expanded policy, with the usual exit codes. With `--json`, `policy_digest` is the digest of the `writ expand` output, and it is absent when the policy has `extends` or layer-2 problems.

### Layer-2 errors

When the policy extends others, a problem in a rule or action of a file adds `(in <file>)`. As in layer 1, a problem with an action starts with the action's name.

| Code | Message |
|---|---|
| `extends_cycle` | extends forms a cycle: {a} -> {b} -> {a} |
| `extends_unreadable` | cannot read extended policy "{file}" (extends chain: {a} -> {file}) |
| `extends_too_deep` | extends is nested more than 8 files deep (extends chain: ...) |
| `extends_too_many` | extends reaches more than 256 files (extends chain: ...) |
| `parent_policy_field` | an extended policy (in {file}) sets policy-level field "{k}"; only the extending policy may |
| `conflicting_dimension` | label dimension "{d}" is declared with two different orders |
| `duplicate_label_value` | label dimension "{d}" lists value "{v}" twice in its order |
| `unknown_label_dimension` | it is labeled on dimension "{d}", which is not declared |
| `unknown_label_value` | its "{d}" label "{v}" is not in that dimension's order |
| `unknown_rule_dimension` | rules[{i}]: when names dimension "{d}", which is not declared |
| `unknown_rule_value` | rules[{i}]: "{v}" is not in the order of dimension "{d}" |
| `rule_empty_roles` | rules[{i}]: a consent clause has an empty role list, so nobody can approve |
| `rule_zero_quorum` | rules[{i}]: a consent clause has a quorum of 0 |
| `rule_unknown_role` | rules[{i}]: a consent clause names role "{r}", which is not an approver role |
| `conflicting_field` | the policy and the policies it extends set "{k}" to different values |
| `conflicting_currency` | consent_if_cost_over uses different currencies ({currency} in {file}, ...), so it never lowers consent |
| `grantable_escalator_without_grantable` | escalator "{e}" is grantable but the action has no grantable |
| `extends_log_only` | the policy extends other policies and sets "mode": "log_only", so every action they require would only be logged; set "mode": "log_only" on this policy's own actions instead |

The JSON decoder already refuses a label order that lists a value twice, so `duplicate_label_value` is reported only for a policy built in Lean.

```sh
$ writ check tests/cli/layer2/problems.json
error: files.delete: its "risk" label "severe" is not in that dimension's order
error: rules[0]: when names dimension "reach", which is not declared
error: rules[1]: a consent clause names role "finance", which is not an approver role
error: files.delete: a consent clause names role "finance", which is not an approver role
error: files.list: it uses meter "nope", which is not defined
warning: some actions can need approval but no approval_ttl_ms is set, so requests never expire
5 errors, 1 warning
```

A role in a rule's consent that is not an approver role is reported twice: once as `rule_unknown_role` for the rule, then as the expanded policy's layer-1 `unknown_role` error for each action the rule matches, as for `files.delete` above.

### Presets

Four presets ship in `schema/presets/`, each an extended policy with only `writ`, `$schema`, `labels` and `rules`: `generic-tiers` (one `risk` dimension, `read` to `destructive`), `mcp-annotations` (the MCP tool annotations), `mcp-risk-metadata` (the risk metadata of the MCP draft SEP-2793) and `axes` (effect, reversibility, audience, value, data). `schema/presets/README.md` lists each one's dimensions and rules. There is no built-in name lookup: a policy uses a preset by listing its path in `extends`, relative to the policy's directory like any other extended file, and sets every policy-level field itself, `approver_roles` included, since the presets' consent rules name no roles. Label values are strings (`"read_only": "true"`), and a dimension an action does not label takes its strictest value, so an action with no labels gets every rule of the preset. `mcp-risk-metadata` and `axes` both declare `reversibility`, with the same order and the same rule, so a policy can extend both; the other dimension names differ. Only `mcp-risk-metadata` produces a quorum of 2 (`approval_recommendation: multi`), which needs two different human approvers at runtime, one of whom may be the requester, and drops `grantable`. The presets are not in `@anijani/writ`, which accepts only layer 1.

```sh
$ writ expand tests/cli/presets/generic-tiers.json
{"actions":{"shop.buy":{"consent":"per_call","grantable":{"max_uses":3,"scope":"turn"}},"vm.console":{},"vm.restart":{"consent":"per_call","grantable":{"max_uses":5,"scope":"session"}},"vm.status":{},"vm.terminate":{"consent":{"groups":[{"all":[{"quorum":1}]},{"all":[{"exclude_requester":true,"quorum":1}]}]}}},"approver_roles":["owner"],"limits":{"approval_ttl_ms":600000},"writ":"0.1"}
```

`tests/cli/presets/` holds a small policy extending each preset, and one extending both `axes` and `mcp-risk-metadata`. In the one above, `vm.restart` (`device`) needs consent and keeps its grant, and `vm.terminate`, which has no label and so is `destructive`, needs an approver other than the requester and loses its `grantable`.

### Import from MCP

`writ import mcp <tools.json> [--server <name>] [--preset-dir <dir>] [--out <file>]` drafts a layer-2 policy from an MCP server's tool list (see Tool digests for the tools.json format), with one action per tool, in listing order, named after the tool. This is the start of `tests/cli/import/claims-draft.json`, the draft of `tests/cli/import/claims.json`, cut after its first action:

```json
{
  "writ": "0.1",
  "extends": [
    "../../../schema/presets/mcp-annotations.json"
  ],
  "approver_roles": [
    "owner"
  ],
  "actions": {
    "web.fetch": {
      "labels": {
        "read_only": "false",
        "destructive": "true",
        "idempotent": "false",
        "open_world": "true"
      },
      "source": {
        "tool_digest": "sha256:21c3fdd0a03683d2d85f985cb8da0ec3e4c9821a72531bfbb61e909eab2b0268",
        "annotations": {
          "title": "Fetch a page",
          "readOnlyHint": true,
          "openWorldHint": true
        }
      }
    }
  }
}
```

Annotations are claims the server makes about its own tools, and Writ does not trust them. Every MCP default is the pessimistic value, so a hint can only ever claim less strictness than the default, and import never applies one: it labels every action explicitly at each dimension's strictest value (`read_only` `"false"`, `destructive` `"true"`, `idempotent` `"false"`, `open_world` `"true"`), whatever the server says. When some tool's annotations carry a SEP-2793 field, the draft also extends `mcp-risk-metadata.json` and labels every action `risk_level` `"critical"`, `blast_radius` `"public"`, `reversibility` `"irreversible"` and `approval_recommendation` `"multi"`. These are the last values of each order in `schema/presets/`, and a test in `WritTests/Import.lean` keeps them equal. So `writ expand` of a draft requires consent for every tool and allows no grant (the `mcp-risk-metadata` labels add a quorum of 2). There is no flag to trust annotations.

The server's annotations are copied into `source.annotations` as it wrote them, for the author to read, except that each number is written in its canonical form (`1.0` becomes `1`, `1e2` becomes `100`, `-0` becomes `0`), with the tool's `writ-tool-v1` digest in `source.tool_digest` and `--server` in `source.server`. Import prints one line on stderr for each claim it did not apply, that is each annotation above whose value is not the strictest one, echoing at most 200 characters of the value (then `...`). Control characters in tool names and annotation keys are escaped, so each line stays one line:

```sh
$ writ import mcp tests/cli/import/claims.json --preset-dir ../../../schema/presets --out tests/cli/import/claims-draft.json
web.fetch: the server says readOnlyHint true; read_only left "false" (lower it after review)
notes.put: the server says destructiveHint false; destructive left "true" (lower it after review)
notes.put: the server says idempotentHint true; idempotent left "false" (lower it after review)
notes.put: the server says openWorldHint false; open_world left "true" (lower it after review)
```

The author lowers a label by editing the draft after reviewing the tool. That is a trusted act, made by whoever owns the policy; the server's claim is not. Edit `approver_roles` too: `["owner"]` is a placeholder that lets the draft pass `writ check`. The draft sets no `limits`, so `writ check` warns that approvals never expire until you add `approval_ttl_ms`.

`source.annotations` is part of the policy, so it follows the policy's number rule. An annotation member holding a number a policy cannot hold (a fraction, or an integer beyond plus or minus (2^53 - 1)), anywhere inside it, is left out, not turned into a string, and stderr names the tool, the member and the number (`météo.prévoir: source.annotations leaves out cost: cost is 0.25, which a policy cannot hold ...`); a member nested more than 123 levels, which would push the draft past the 128-level limit, is left out the same way. `source.tool_digest` still covers the whole tool, those members included. An `annotations` that is not an object is left out with a line on stderr. So the draft always parses.

The `extends` entries are `<dir>/mcp-annotations.json` and `<dir>/mcp-risk-metadata.json`, where `<dir>` is `--preset-dir` (default `presets`): copy `schema/presets/` next to the draft, or pass the path from where the draft will live to `schema/presets/`. The draft is pretty-printed with a two-space indent, keys in the order above, and written to stdout or to `--out`. Exit 0 when it is written, and 2 for a usage or input error: a file that cannot be read or is not UTF-8, a document that does not parse or is not a tool list, a number the tool digest refuses (named by its JSON path), no tools, or a duplicate tool name (`tools[2].name: duplicate tool name "a"`).

### Changed tool definitions

`writ check <policy.json> --tools <tools.json> [--server <name>]` also compares the policy with a server's current tool list (a tools.json document, read and refused exactly as `writ import mcp` reads it, see Tool digests). For each action with a `source`, it finds the tool named `source.tool`, or the action name when `source.tool` is absent, and compares the tool's `writ-tool-v1` digest with `source.tool_digest`. With `--server`, only the actions whose `source.server` is that name are compared; `--server` without `--tools` is a usage error, and a `--server` longer than 512 UTF-8 bytes is one too, as for `writ import mcp`. A layer-2 policy is compared after expansion, so a `source` written in a file it extends counts; when an `extends` problem stops the expansion, nothing is compared. The digest is canonical, so key order, whitespace and number spelling (`0.5` or `5e-1`) never count as a change, and any change of content (a description, a schema, an annotation) does.

| Code | Kind | Message |
|---|---|---|
| `tool_changed` | error | `{action}: tool "{t}" changed: source.tool_digest is {old}, the tool list has {new}` |
| `tool_missing` | warning | `{action}: tool "{t}" is not in the tool list` |
| `tool_unpinned` | warning | `{action}: it allows tool "{t}" but records no source.tool_digest, so writ cannot detect changes to the tool` (with `--server`, for an action whose `source` is for another server: `but its source is not for server "{s}", so this check cannot detect changes to the tool`; for an action named `{t}` whose `source.tool` names another tool: `but its source pins tool "{other}"`) |
| `tool_unlisted` | warning | `tool "{t}" is in the tool list but no action names it (by name or source.tool), so default deny refuses it` |

A changed tool is an error because its description, schema or annotations are no longer the ones the policy was reviewed against: a description rewritten to instruct the model (tool poisoning) keeps the tool's name, so only the digest shows it. A listed tool that no compared `source` pins gets one of two warnings. When some action still allows it (an action of that name, or one whose `source.tool` names it) but records no `source`, or under `--server` records one for another server, the tool is callable and a later change to it goes undetected: `tool_unpinned`, one per such action. The kernel matches a call's tool with the action names and ignores `source`, so an action named `read_file` whose `source.tool` is `write_file` allows `read_file` with a digest pinned for another tool; it gets `tool_unpinned` too (`read_file: it allows tool "read_file" but its source pins tool "write_file"`). So a policy with no `source` at all, checked with `--tools`, reports each of its actions that a listed tool shares a name with. When no action names the tool, default deny already refuses it (`unknown_tool`): `tool_unlisted`. The findings follow the policy's own, errors after its errors and warnings after its warnings, in text and in `--json`, with the usual exit codes:

```sh
$ writ check tests/cli/tools/policy.json --tools tests/cli/tools/web-poisoned.json --server web
error: web.fetch: tool "web.fetch" changed: source.tool_digest is sha256:2090263f72e715d1bcdc3e8c2dbba75a65f0567b365ee68a8f371b5a9a6b1cab, the tool list has sha256:17964b625595c02034011bd7f85b9bff78931e8109e2ba8971e2ab4f7d794e26
1 error, 0 warnings
$ echo $?
1
```

## Event

An event is one JSON object. Every event has `type`, `seq` (strictly increasing), `time` (milliseconds, non-decreasing), `state_version` (the version of the state it applies to) and optionally `origin` (an opaque string) and `audit` (an object the kernel ignores). The remaining fields depend on the type; all listed fields are required unless marked with `?`.

| `type` | Fields |
|---|---|
| `session_start` | `session_id`, `policy_digest`, `requester`, `permissions`, `approvers` (name to `{ principal, kind, roles }`; `kind` is `human` or `automated`), `ledger` |
| `session_end`, `turn_end`, `step_start`, `reset`, `kill` | none |
| `turn_start` | `user_initiated` |
| `propose` | `call_id`, `tool`, `call_digest`, `cost?` (`{ amount, currency }`), `guards` (name to bool), `escalators` (name to bool) |
| `approve` | `call_id`, `request_id` (`{ session, call, generation }`), `approver`, `reviewed_digest`, `reviewed_cost?`, `edit?` (`{ new_digest, new_cost?, escalators }`) |
| `reject` | `call_id`, `request_id`, `approver` |
| `approval_expire` | `call_id`, `request_id` |
| `grant_create` | `grant_id`, `approver`, `tool`, `call_digest?`, `scope`, `max_uses`, `max_cost?`, `not_before?`, `expires_at?`, `reviewed_scope_digest` |
| `grant_revoke` | `grant_id` |
| `approver_attest` | `approver`, `principal`, `kind`, `roles` |
| `permission_add` | `permission`, `approver` |
| `permission_revoke` | `permission` |
| `dispatch` | `call_id`, `attempt`, `call_digest`, `cost?`, `guards`, `idempotency_key` |
| `result`, `reconcile` | `call_id`, `outcome` (`succeeded`, `failed`, `declined`), `actual_cost?` (an amount string), `no_effect?` (default false) |
| `outcome_unknown`, `cancel` | `call_id` |
| `escalation_ack` | `approver`, `escalation` |
| `ledger_sync` | `ledger` |

A ledger is `{ version?, entries?, tombstone? }` (`{}` for an empty one). An entry is `{ meter, session, call, time, amount, committed, excess?, excess_at? }`.

`session_start.policy_digest` is required and must equal the digest of the policy the kernel runs, or the session is refused (`policy_digest_mismatch`). The one exception is inside a trace, where a missing `policy_digest` is filled with the trace's digest.

Two behaviors worth knowing when you write a host: an approver edit (`approve` with `edit`) creates generation g + 1 and returns `authorized` if the editor alone meets the raised consent, `pending` otherwise, and the next request id is `{ session, call, generation: g + 1 }`; and `kill`, or a principal tombstone arriving through `ledger_sync`, cancels awaiting and authorized calls, after which the only events accepted are `propose` (denied `killed`), `kill`, `session_end`, `result`, `outcome_unknown`, `reconcile` and `ledger_sync`; every other event, any `dispatch` included, is rejected `killed`.

A session as JSON lines (`tests/cli/formats-events-a.jsonl`; the digest is the one printed above):

```json
{"type":"session_start","seq":1,"time":0,"state_version":0,"session_id":"s1","policy_digest":"sha256:866cd32f034a15421198ab518d1e23a34f4acfb4ba2fb20884f9af5fca97a6dd","requester":"u1","permissions":["shop.read","shop.buy"],"approvers":{"laptop":{"principal":"u1","kind":"human","roles":["owner"]}},"ledger":{}}
{"type":"turn_start","seq":2,"time":1000,"state_version":1,"user_initiated":true}
{"type":"step_start","seq":3,"time":1000,"state_version":2}
{"type":"propose","seq":4,"time":1100,"state_version":3,"call_id":"c1","tool":"buy","call_digest":"d-buy-lamp","cost":{"amount":"1200","currency":"USD"},"guards":{"card_on_file":true},"escalators":{}}
```

## Verdict

`writ oracle` and the kernel answer each event with one verdict object. Keys, in this order:

1. `verdict`: `accepted` or `rejected`.
2. `state_version`: the state's version after the step. This is what the next event must name in its own `state_version`. A rejected event leaves the state as it was, so the version does not move.
3. For an accepted verdict, `decision` (left out when the event decides nothing) with its payload: `grant` for `allowed_by_grant`, `request_id` for `needs_approval`, `reason` for `denied` and `dispatch_denied`, `status` for `existing`, `meters` for `overrun`. For a rejected verdict, `reason`.
4. `would_deny` (a reason) or `would_need_approval: true`, in `log_only` mode.
5. `retry` and `message`, only when there is a reason to explain: a decision's reason or a rejected verdict's reason. They are never written for `would_deny` alone.

Decisions: `pending`, `authorized`, `allowed`, `allowed_by_grant`, `needs_approval`, `denied`, `dispatch_claimed`, `dispatch_denied`, `existing`, `overrun`. A `result` or `reconcile` that commits an actual cost above the reservation on some money meter is accepted with `overrun`, whose `meters` lists the overrun meters in the order the action lists them: `{"verdict":"accepted","state_version":7,"decision":"overrun","meters":["usd_day"]}`. Otherwise those events decide nothing. A release (`no_effect: true`, or outcome `declined`) commits nothing, so it reports no overrun and adds no overrun failure, whatever `actual_cost` it carries; a `failed` outcome still counts as a failure. A call status (in `existing` and in state) is `denied`, `awaiting`, `authorized`, `dispatched`, `succeeded`, `failed`, `declined`, `unknown`, `rejected`, `expired`, `denied_at_dispatch` or `cancelled`; `denied` and `denied_at_dispatch` are written as `{ "status": ..., "reason": ... }`, and `existing` with one of those two statuses also carries `retry` and `message`.

`retry` tells the model what to do next: `fix_request`, `never`, `after_user_action`, `next_turn` or `after_escalation`. `message` is the model-facing text. Reason codes by retry class:

- `fix_request`: `not_started`, `already_started`, `session_ended`, `stale_seq`, `time_decreasing`, `state_version_mismatch`, `policy_digest_mismatch`, `duplicate_call`, `unknown_call`, `call_awaiting`, `call_authorized`, `call_dispatched`, `call_unknown`, `not_escalated`, `stale_request`, `unknown_approver`, `approver_not_eligible`, `already_approved`, `digest_mismatch`, `cost_mismatch`, `edit_not_allowed`, `duplicate_grant`, `unknown_grant`, `grant_not_allowed`, `attempt_order`, `idempotency_key_mismatch`, `attempt_limit`, `turn_state`, `cost_missing`, `currency_mismatch`
- `never`: `killed`, `unknown_tool`, `not_exposed`, `cost_above_per_call`, `ledger_conflict`, `session_proposal_limit`, `session_approval_budget`, `call_ended`, `retry_not_allowed`, `already_reconciled`, `approver_changed`
- `after_user_action`: `permission_missing`, `guard_false`, `meter_exceeded`, `previously_rejected`, `approval_expired`, `authorization_expired`, `grant_invalid`
- `next_turn`: `proposal_limit`, `step_limit`, `approval_budget`
- `after_escalation`: `escalated`

Twelve reasons are host-protocol errors: `not_started`, `already_started`, `stale_seq`, `time_decreasing`, `state_version_mismatch`, `policy_digest_mismatch`, `duplicate_call`, `unknown_approver`, `approver_changed`, `attempt_order`, `idempotency_key_mismatch` and `turn_state`. Their cause is always in the host's or the binding's code, never in the model's request, so their model message says only that the system running tool calls hit an internal error and that the model must not change or repeat its request; for those in `fix_request`, that retry class means the host must fix its event, not the model its request. A binding should treat them as its own bug (log them, alert on them) and need not forward them to the model.

`schema/reasons.json` lists every reason code with its retry class, in a fixed order. It is the list that bindings in other languages generate from; the Lean tests and the TypeScript package are both checked against it.

The verdicts for the session above, from `writ oracle tests/cli/policies/formats-shop.json < tests/cli/formats-events-a.jsonl`:

```json
{"verdict":"accepted","state_version":1}
{"verdict":"accepted","state_version":2}
{"verdict":"accepted","state_version":3}
{"verdict":"accepted","state_version":4,"decision":"needs_approval","request_id":{"session":"s1","call":"c1","generation":0}}
```

## State

State is the kernel's whole memory of one session. `writ oracle --state-out` writes it as canonical JSON (one line, keys sorted); a host stores it with compare-and-swap on `state_version`. `state.ledger` is what the host writes back with compare-and-swap on the ledger version (spec section 7), so several live sessions of one principal share one stored ledger. Schema `writ.state/1`. Unlike the other formats, state writes every top-level field, defaults included, and decoding requires every top-level field (nested ledger and meter entries may omit their defaults), checks `schema` and `kernel_version` (`kernel_version: state was written by kernel 0.0.9, this is 0.1.0`) and rejects unknown ones. A state with a different `kernel_version` is refused, so stored sessions finish on the kernel version they started with. A state also records the digest of its policy (`policy_digest`); the oracle refuses a `--state` whose digest differs from the policy's.

The state after the four events above (`tests/cli/states/formats-state.json`; the awaiting call `c1` is in `calls`):

```json
{"approvals_this_session":1,"approvals_this_turn":1,"approvers":{"laptop":{"kind":"human","principal":"u1","roles":["owner"]}},"blocked_tools":[],"calls":{"c1":{"attempts":0,"authorized_at":null,"consent":"per_call","cost":{"amount":"1200","currency":"USD"},"decision":{"decision":"needs_approval","request_id":{"call":"c1","generation":0,"session":"s1"}},"digest":"d-buy-lamp","epoch":0,"generation":0,"generations":[{"cost":{"amount":"1200","currency":"USD"},"digest":"d-buy-lamp"}],"grant":null,"idempotency_key":null,"proposed_cost":{"amount":"1200","currency":"USD"},"proposed_digest":"d-buy-lamp","proposed_escalators":{},"proposed_guards":{"card_on_file":true},"reconciled":null,"requested_at":1100,"shadow":null,"status":"awaiting","tally":[],"tool":"buy"}},"ended":false,"epoch":0,"escalated":false,"escalations":0,"failures":{},"failures_this_session":0,"grants":{},"kernel_version":"0.1.0","killed":false,"last_seq":4,"last_time":1100,"ledger":{},"permissions":["shop.read","shop.buy"],"policy_digest":"sha256:866cd32f034a15421198ab518d1e23a34f4acfb4ba2fb20884f9af5fca97a6dd","proposals_this_session":1,"proposals_this_turn":1,"rejected_memory":[],"requester":"u1","schema":"writ.state/1","session_id":"s1","session_meters":[],"started":true,"state_version":4,"steps_this_turn":1,"turn_active":true,"turn_index":1}
```

Continuing from it with the next events (`tests/cli/formats-events-b.jsonl`) gives the same verdicts as running all of them in one go. The five events approve and dispatch the purchase, report its result (the actual cost `"1150"` lands in the ledger), propose a tool the policy does not know, and send an event that names a stale `state_version`:

```json
{"type":"approve","seq":5,"time":9000,"state_version":4,"call_id":"c1","request_id":{"session":"s1","call":"c1","generation":0},"approver":"laptop","reviewed_digest":"d-buy-lamp","reviewed_cost":{"amount":"1200","currency":"USD"}}
{"type":"dispatch","seq":6,"time":9100,"state_version":5,"call_id":"c1","attempt":1,"call_digest":"d-buy-lamp","cost":{"amount":"1200","currency":"USD"},"guards":{"card_on_file":true},"idempotency_key":"k-s1-c1"}
{"type":"result","seq":7,"time":9500,"state_version":6,"call_id":"c1","outcome":"succeeded","actual_cost":"1150"}
{"type":"propose","seq":8,"time":9600,"state_version":7,"call_id":"c2","tool":"wire_money","call_digest":"d-wire","guards":{},"escalators":{}}
{"type":"propose","seq":9,"time":9700,"state_version":6,"call_id":"c3","tool":"search","call_digest":"d-q","guards":{},"escalators":{}}
```

```sh
$ writ oracle tests/cli/policies/formats-shop.json --state tests/cli/states/formats-state.json < tests/cli/formats-events-b.jsonl
{"verdict":"accepted","state_version":5,"decision":"authorized"}
{"verdict":"accepted","state_version":6,"decision":"dispatch_claimed"}
{"verdict":"accepted","state_version":7}
{"verdict":"accepted","state_version":8,"decision":"denied","reason":"unknown_tool","retry":"never","message":"This tool is not part of the policy. Do not call it again; use only the tools you have been given."}
{"verdict":"rejected","state_version":8,"reason":"state_version_mismatch","retry":"fix_request","message":"The system that runs tool calls hit an internal error (it acted on an out-of-date copy of the session). Your request was not the cause; do not change or repeat it on your own, and tell the user if this keeps happening."}
```

## Trace

A trace (`writ.trace/1`) is a policy plus events, with optional expected verdict fields per event. A file holds one trace per line (JSONL; blank lines are skipped). Fields: `schema`, `id`, `description?`, `policy` (a full policy document), `policy_digest?`, `events`. Each element of `events` is `{ event, expect? }`. `expect` is any subset of a verdict's keys; `writ replay` compares those keys only, so a trace pins what it cares about. Request ids and other objects compare as JSON values, key order ignored. The digest used for the run is `policy_digest` if the trace has one, otherwise the digest of the `policy` document as written, and `session_start` events inside a trace may leave `policy_digest` out.

```json
{"schema":"writ.trace/1","id":"shop/approve-and-dispatch","description":"A purchase waits for the owner's approval, then dispatches.","policy":{"writ":"0.1","approver_roles":["owner"],"meters":{"spend":{"currency":"USD","cap":5000,"scope":"principal","window_ms":86400000}},"limits":{"approval_ttl_ms":600000,"max_consecutive_failures":3},"actions":{"search":{"permission":"shop.read"},"buy":{"permission":"shop.buy","consent":"per_call","guards":["card_on_file"],"meters":["spend"],"idempotent":true}}},"events":[{"event":{"type":"session_start","seq":1,"time":0,"state_version":0,"session_id":"s1","requester":"u1","permissions":["shop.read","shop.buy"],"approvers":{"laptop":{"principal":"u1","kind":"human","roles":["owner"]}},"ledger":{}},"expect":{"verdict":"accepted"}},{"event":{"type":"turn_start","seq":2,"time":1000,"state_version":1,"user_initiated":true},"expect":{"verdict":"accepted"}},{"event":{"type":"step_start","seq":3,"time":1000,"state_version":2},"expect":{"verdict":"accepted"}},{"event":{"type":"propose","seq":4,"time":1100,"state_version":3,"call_id":"c1","tool":"buy","call_digest":"d-buy-lamp","cost":{"amount":"1200","currency":"USD"},"guards":{"card_on_file":true},"escalators":{}},"expect":{"verdict":"accepted","decision":"needs_approval","request_id":{"session":"s1","call":"c1","generation":0}}},{"event":{"type":"approve","seq":5,"time":9000,"state_version":4,"call_id":"c1","request_id":{"session":"s1","call":"c1","generation":0},"approver":"laptop","reviewed_digest":"d-buy-lamp","reviewed_cost":{"amount":"1200","currency":"USD"}},"expect":{"verdict":"accepted","decision":"authorized"}},{"event":{"type":"dispatch","seq":6,"time":9100,"state_version":5,"call_id":"c1","attempt":1,"call_digest":"d-buy-lamp","cost":{"amount":"1200","currency":"USD"},"guards":{"card_on_file":true},"idempotency_key":"k-s1-c1"},"expect":{"verdict":"accepted","decision":"dispatch_claimed"}}]}
```

```sh
$ writ replay tests/cli/traces/formats-shop.jsonl
ok shop/approve-and-dispatch
1 trace, 0 failed
```

A mismatch prints one line per failing step, for example `FAIL web-chat/parallel-calls step 1: expected verdict rejected, got accepted`, and the exit code is 1. With `--coverage`, replay adds one last line, `{"reasons":[...],"decisions":[...]}`, listing every reason code and every decision in the verdicts the replay gave (not in the traces' `expect`), each once and sorted. The reasons are those of rejected events, of `denied` and `dispatch_denied` decisions, of `existing` statuses that carry one, and of `would_deny`; the exit code is unchanged:

```sh
$ writ replay tests/cli/traces/would-deny.jsonl --coverage
ok shadow/guard-false-would-deny
1 trace, 0 failed
{"reasons":["guard_false"],"decisions":["allowed"]}
```

`writ explain` walks through each step, one line each (a trace carries its own policy, so there is no policy argument):

```sh
$ writ explain tests/cli/traces/formats-shop.jsonl
trace shop/approve-and-dispatch: A purchase waits for the owner's approval, then dispatches.
  0 session_start -> accepted none
  1 turn_start -> accepted none
  2 step_start -> accepted none
  3 propose call_id=c1 tool=buy -> accepted needs_approval
  4 approve call_id=c1 approver=laptop -> accepted authorized
  5 dispatch call_id=c1 -> accepted dispatch_claimed
```

Parse errors in a trace file name the line, then the path inside the trace: `line 1: events[0].expect.decison: unknown field`.

## Trace generator

`writ traces <policy.json> [--depth N] [--max-states M] [--out <dir>]` generates traces from a policy. It explores the kernel's states breadth-first from the initial state over a small alphabet of events and prints one `writ.trace/1` trace per line, or with `--out` writes them to `<dir>/<name>.jsonl`, creating the directory, where `<name>` is the policy file name without `.json`. The policy may be layer 1 or 2, expanded as `writ expand` expands it; a policy that `writ check` reports errors for is refused (exit 2, the errors on stderr). Each trace's `policy` is the layer-1 policy, the file as written or for layer 2 exactly what `writ expand` prints, and each `session_start` names its digest, so the traces carry no `policy_digest`. Every event carries an `expect` holding the whole verdict the kernel gave, `state_version`, `retry` and `message` included, so `writ replay` checks all of it. stderr gets `states S, traces T (accepted A, rejected R), depth N`, followed by `, truncated` when `--max-states` stopped the search. Before it, stderr gets one line for each action the alphabet leaves out because an event could not name it (Alphabet, below): `skipped action <name>: its name, a guard name or an escalator name is longer than 512 UTF-8 bytes, which an event cannot hold`, the name escaped onto one line. Exit 0, or 2 for a usage, IO or policy error. The same input gives the same bytes.

```sh
$ writ traces tests/cli/traces/tiny.json --depth 0 | head -1 | cut -c1-120
{"schema":"writ.trace/1","id":"tiny/a/00000","policy":{"writ":"0.1","approver_roles":["owner"],"actions":{"ping":{"conse
states 3, traces 28 (accepted 2, rejected 26), depth 0
```

### Alphabet

The identifiers are session `s1`, requester `u1`, calls `c1` and `c2`, digests `d1` and `d2`, grants `g1` and `g2`, and four approvers: `u1` (the requester, human, every approver role), `a2` (human, the first approver role), `a3` (automated, every approver role) and `a4` (human, every approver role, with the reserved principal `agent`, which no rule admits). The explorer uses one representative action per distinct set of requirements, in policy order: an action whose requirements equal an earlier one's is skipped. An action whose name, guard names or escalator names are longer than 512 UTF-8 bytes is left out, because the event codec refuses such strings.

From each state it tries the events below, event type by event type in the order of the table. A new call takes the first unused call id and a new grant the first unused grant id; a digest is one already in the state or the first unused one. Up to renaming (Search, below), any other unused call id or digest would reach the same states (grant ids are not renamed).

| Event | What the explorer sends |
|---|---|
| `session_start` | At time 1, requester `u1`, every permission the policy names, approvers `u1` and `a2` (`a3` joins only through `approver_attest`), and an empty ledger; the same with a ledger whose tombstone is set, at version 1 (a store bumps the ledger version on every write, so it never holds a non-empty ledger at version 0). |
| `session_end`, `turn_end`, `step_start`, `reset`, `kill` | One each. |
| `turn_start` | `user_initiated` true and false. |
| `propose` | A new call for each representative action, with each digest, each cost choice (below), all guards true or all false, and all escalators reported false or none reported (an unreported escalator counts as fired); one new call of a tool the policy does not define. Each recorded call proposed again with its first digest and cost and, after an edit, its current ones. In a killed session, where every new proposal is denied `killed`, only the first new proposal. |
| `approve` | For each awaiting call, its current request id, digest and cost, by each approver, without an edit and with an edit to the other digest that keeps the cost (escalators all false, and also none reported when the action has escalators). |
| `reject` | For each awaiting call, and each authorized call not yet dispatched, by each approver at the current generation, and by `u1` at generation 0 after an edit. |
| `approval_expire` | For each awaiting call, its current request id. |
| `grant_create` | For each grantable representative action: by each approver, for each digest (and with no digest when it is `any_args`), at the action's scope and `max_uses`, with no `max_cost` and, for an action with a money meter or a `consent_if_cost_over`, the first cost; `expires_at` is the time plus `max_duration_ms` when the action sets one; `reviewed_scope_digest` is `rsd`. Also one grant by `u1` for the first digest with `not_before` one past the time, valid only from the next millisecond. |
| `grant_revoke` | Each grant. |
| `approver_attest` | `u1`, `a2`, `a3` and `a4`, each as above. |
| `permission_add` | Each permission the policy names and the state does not hold, by `u1`; once `a4` is attested, the first permission (`p` when the policy names none) by `a4`, which the `agent` rule refuses. |
| `permission_revoke` | Each permission the state holds (`p` when the policy names none). |
| `dispatch` | For each authorized or unknown call, the next attempt, its digest and cost, idempotency key `k-` followed by the call id, and guards all true or all false. |
| `result`, `reconcile` | For each dispatched call (for `reconcile`, each unknown call not yet reconciled): `succeeded`, `failed` and `declined`; on an action with a money meter also `succeeded` with an `actual_cost` one above the call's cost (an overrun) and `failed` with `no_effect`. |
| `outcome_unknown` | Each dispatched call. |
| `cancel` | Each awaiting or authorized call. |
| `escalation_ack` | When the session is escalated or a tool blocked, by each approver, echoing the current escalation count. |
| `ledger_sync` | The state's ledger; the same with its tombstone flipped and its version one higher; without this session's committed entries (as if another session pruned them), version one higher, when it has some; with an entry of another session (`s0`) filling the first principal meter, version one higher, when the policy has one. |

Costs: none, plus, for each money currency (of a money meter or a `consent_if_cost_over`), the amounts 1, each cap, each `consent_if_cost_over` amount plus 1 and each `max_per_call`, the first four of these. Only an action with a money meter or a `consent_if_cost_over` proposes with a cost.

Times: an event normally carries the last time `t`; `session_start` carries time 1, so a later event can carry a decreasing time. An event also goes at `t + d` where a time-dependent check can turn: an `approve` at `t` plus the action's approval TTL; a `dispatch` at `t` plus its authorized TTL, the window of each of its meters that holds entries and, for a call that uses a grant, `max_duration_ms` (and `t + 1` when the grant has a `not_before`); a `propose` of a new call at `t` plus the window of each of its meters that holds entries and, when a grant for the tool exists, `max_duration_ms`, and at `t + 1` when such a grant has a `not_before`; a repeated `propose` of an authorized call at `t` plus its authorized TTL; `result` and `reconcile` at `t` plus the window of each of the call's meters that holds entries. The later times use only the first guard and escalator choice, and only `u1` approves at them. A time above 2^53 - 1, the largest integer the JSON parser reads, is never sent, and neither is an event whose `expires_at`, `not_before` or `max_uses` would pass it or whose amount would pass 78 digits (a large TTL, window, `max_duration_ms`, `max_uses` or cost threshold), so every trace replays.

Rejection samples: besides the events above, the explorer sends events meant to be rejected. Every event type gets three with a wrong envelope (`seq` equal to the last one, the time minus 1, `state_version` plus 1), two from the initial state, where time cannot decrease. `session_start` gets a wrong `policy_digest` and a ledger at version 1 with an entry of session `s1`. Each call-scoped type gets one on every call whose status it does not fit (`call_awaiting`, `call_authorized`, `call_dispatched`, `call_unknown`, `call_ended`, `already_reconciled`) and one on an unused call id. `propose` repeats a recorded call id with another tool; `approve` sends generation plus 1, the other digest, another cost and, on a money meter, an edit without a cost; `reject` and `approval_expire` send generation plus 1; `grant_create` sends `max_uses` plus 1, an existing grant id, a tool that is not grantable and one the policy does not define; `grant_revoke` an unused id; `approver_attest` re-attests `a2` as automated; `permission_add` names `a3` while it is not attested; `dispatch` skips an attempt number, sends the other digest, another cost and, on a retry, another idempotency key; `escalation_ack` echoes the count plus 1, or the current count when nothing is blocked; `ledger_sync` sends the ledger one version back (the empty ledger at version 0 when the state's is at version 1). A sample is skipped once its event type has been sampled with the reason it is meant to reach.

### Search

The search is breadth-first from the initial state. A state is identified by a key: its canonical JSON without `state_version` and `last_seq`, with call ids, digests and approver principals other than the requester and `agent` renamed by first occurrence in that JSON (an idempotency key `k-<call>` follows its call). Two states with one key are equal up to such a renaming. Grant ids are kept: the kernel picks the first valid grant in id order, so two states that differ by a renaming of grants can behave differently, and merging them would hide transitions. Renaming by first occurrence can miss a symmetry, so two states that are renamings of each other may still get two keys; that costs only duplicate traces. The explorer steps from the first concrete state it found for each key, so every trace is a real run.

`--depth N` (default 4) counts the events after `session_start`: the explorer steps from every state at most N events after it, so a trace has at most N + 1 events. `--max-states M` (default 20000) bounds the number of keys: when a new key would be the M + 1st, the search stops where it is and the output is marked truncated.

### Emission and ids

- Every accepted transition whose (pre key, post key) pair is new, self-loops included, as the shortest path to the pre state followed by the event. Its id is `<name>/a/<k>`, `k` its index in the order found, zero-padded to 5 digits from `00000`.
- For each (event type, reason) pair, the first rejected transition found, with id `<name>/r/<event type>/<reason>`.

The accepted traces come first, then the rejected ones, each in the order found. The order of the search is fixed (the event types in the table's order, and within a type the order above), so the output never depends on hash order.

### Budgets

The state space grows about fivefold with each level of depth. `tests/cli/traces/tiny.json`, one action that needs approval, gives:

| `--depth` | states | traces | time |
|---|---|---|---|
| 2 | 80 | 261 | 0.01 s |
| 3 | 434 | 867 | 0.06 s |
| 4 | 2355 | 4300 | 0.4 s |
| 5 | 12149 | 23045 | 2.5 s |

A policy with more representative actions, costs or meters grows faster, so pick the depth for the policy and let `--max-states` bound a run whose size is unknown. Some reasons need depth 4: a retry (`retry_not_allowed`, `attempt_limit`, `idempotency_key_mismatch`) needs a proposal, a dispatch and an unknown outcome before it.

## Standard corpus

The standard corpus is generated, never committed: `scripts/corpus.sh` runs `writ traces` on each fixture policy in `corpus/standard/fixtures/` and writes `build/corpus/standard/<name>.jsonl`. Each fixture has at most 4 actions and passes `writ check` without errors; together they use every requirement feature the kernel reads except `max_failures_per_session`, which `corpus/examples/payments.jsonl` uses, and their traces, with the hand-written ones, reach every reason code. `corpus/standard/README.md` says what each fixture is for.

`corpus/standard/manifest.json` pins the output, one fixture object per line:

```json
{
  "generator": 1,
  "fixtures": [
    { "policy": "fixtures/basic.json", "depth": 2, "max_states": 10000, "traces": 408, "states": 181, "truncated": false, "sha256": "d5e79..." }
  ]
}
```

`policy` is relative to `corpus/standard/`; `depth` and `max_states` are the `writ traces` options, chosen per fixture; `traces`, `states` and `truncated` are what `writ traces` reported; `sha256` is the lowercase hex SHA-256 of the generated file. `generator` is the manifest's format version. Since `writ traces` gives the same bytes for the same input, a changed `sha256` means the fixture, the explorer or the kernel changed.

`corpus/standard/uncovered.json` lists the reason codes that no replayed verdict of the generated or the hand-written corpora reaches, each as `{ "code": ..., "reason": ... }` with a one-line reason holding no double quote or backslash, one entry per line (`scripts/corpus.sh` refuses any other layout, here and in `schema/reasons.json`). It is empty (`[]`) today.

`scripts/corpus.sh` with no arguments:

1. regenerates every fixture into `build/corpus/standard/`, with the depth and `max_states` its manifest entry gives;
2. compares `traces`, `states`, `truncated` and `sha256` with the manifest and fails, naming each difference, with `the generated corpus changed; review the difference, then run scripts/corpus.sh --update` (a fixture without a manifest entry, or an entry without a fixture, counts as a difference);
3. replays the generated corpus with `corpus/examples/*.jsonl` (and `corpus/attacks/*.jsonl` when that directory exists) in one `writ replay --coverage`, and fails if a trace fails;
4. judges the same traces with `writ-fuzz --judge` (below), and fails on any violation;
5. fails if a code in `schema/reasons.json` is neither in the coverage nor in `uncovered.json`, or if an `uncovered.json` code is covered after all or is not a reason code.

`corpus/sep-2848.json` maps SEP-2848's statements to traces in `corpus/examples`, so it adds nothing to replay. `--update` rewrites the manifest from the run (a new fixture gets depth 3 and `max_states` 20000 until its entry is edited) and then runs steps 3 to 5. `--tar` also writes `build/writ-corpus-<version>.tar.gz`, `<version>` being the CLI version, holding `standard/` (the generated `traces/`, the fixtures, the manifest, `uncovered.json` and the README), `examples/`, `digests/`, `profiles/` (the MCP SEP-2848 profile vectors), `sep-2848.json` and, when present, `attacks/`. The script needs only the `writ` and `writ-fuzz` binaries, which it builds, and POSIX tools, and for `--tar` also `python3`, which runs `scripts/tarball.py` to make the tarball reproducible; CI runs it.

`lake exe writ-fuzz --judge <traces.jsonl>...` is the spec-side judge. `writ replay` checks a trace against its own `expect`, which the kernel produced. The judge instead runs the trace's events through the kernel and checks every verdict and state against the checkers in `WritSpec`, which restate the design spec without reading the kernel. Each trace is one session from a fresh state, and the stored ledger before it is the ledger of its first accepted `session_start`. The judge prints one line per violation, `<trace id> step <n> <checker>: <message>` (the step is the 0-based event index; each checker reports its first violation per trace), then `judged T traces, V violations`. Exit 0 with no violations, 1 with any, 2 when a file cannot be read or decoded, in which case nothing is judged. A violation means either a kernel bug or a gap in a checker. Its own self-test runs when `writ-fuzz` is built: three hand-made traces, replayed under small inline mutants (one allows a proposal after a kill, one ignores principal spend that another session's entries brought in through `ledger_sync`, one drops the entries an accepted `session_start` brings after a rejected one), must be flagged, and under the real kernel must judge clean. CI builds and runs `writ-fuzz`, so this self-test runs there and not under a plain `lake build`.

## MCP SEP-2848 profile

The profile `mcp-tool-approval` (`writ/mcp-tool-approval` in section 13 of `docs/design.md`) maps call statuses and verdicts to the terms of two MCP drafts, and flags the policy settings one of them forbids. It follows two texts, both pinned in `corpus/sep-2848.json`: SEP-2848, "Asynchronous Approval for Tool Calls" (`spec_url`), and SEP-2643, "Structured Authorization Denials" (`sep2643_url`: `seps/2643-structured-authorization-denials.md` at commit `c74b0c9321e89a904780d1024d895232fbb03820` of `monmohan/modelcontextprotocol`, the head of the open pull request modelcontextprotocol/modelcontextprotocol#2643, status Draft). The code is `Writ/Profile/McpToolApproval.lean`, which only `Writ.Api` and the `writ` command import: the kernel, its formats and its reason codes do not change, so the drafts can change without touching them. Its strings and envelope members follow those drafts and are outside the frozen formats.

### Dispositions

A SEP-2848 server writes the outcome of a completed approval task as `io.modelcontextprotocol/tool-approval-disposition`. The profile gives it for every terminal status (section 6 of `docs/design.md`) and nothing while the call can still move:

| Call status | Disposition |
|---|---|
| `succeeded` | `approved-executed` |
| `denied`, `rejected`, `expired`, `denied_at_dispatch`, `declined` | `denied-not-executed` |
| `failed` | `execution-error` |
| `unknown` | `outcome-unknown` |
| `cancelled` | `cancelled` |
| `awaiting`, `authorized`, `dispatched` | none |

`cancelled` is not a SEP-2848 disposition: SEP-2848 reports a cancelled task with the SEP-2663 task status `cancelled` and no disposition, so a server writes it as the task status. A host reports `declined` only when the tool had no effect (section 6), which is why it maps to `denied-not-executed`.

### Envelopes

A SEP-2643 server puts a denial envelope under `io.modelcontextprotocol/authorization` in the `_meta` of the result that expresses the denial. The profile gives one for a `needs_approval` decision, with the request id:

```json
{"reason":"insufficient_authorization","remediation":"available","remediationHints":[{"type":"task"}],"requestId":{"session":"s1","call":"c1","generation":0}}
```

and one for a `denied` or `dispatch_denied` decision or a rejected verdict, holding the reason code, its retry class and its model message:

```json
{"reason":"insufficient_authorization","remediation":"unavailable","code":"killed","retry":"never","message":"The session has been stopped. Do not retry this or any other call."}
```

Any other verdict (`allowed`, `allowed_by_grant`, `authorized`, `pending`, `dispatch_claimed`, `existing`, `overrun`, an accepted event that decides nothing, and a `would_deny` in `log_only` mode, whose decision is `allowed`) has none.

- `reason`, `remediation` and `remediationHints` are SEP-2643's members. `reason` is `insufficient_authorization`, the one value the draft defines. A pending approval is SEP-2643's case 2, remediation in the background through a task, so it gets `remediation: "available"` with one hint of type `task`. A denial is its case 4, a final denial with no hints.
- SEP-2643 is silent on the reason code, the retry class, the message and the request id, so these members take Writ's terms, as section 13 of `docs/design.md` says for anything the draft leaves open. `code`, `retry` and `message` are the code, retry class and model message of the verdict (`reason` is taken by SEP-2643), and `requestId` is the verdict's `request_id`, named in the envelope's own camelCase.
- The disclosure posture (section 13) is the same for every reason: an envelope discloses the code, the retry class and the reviewed model message of `Writ/Core/Messages.lean`, which v0.1-preview reviewed for model safety, and nothing else: no digest, cost, approver, grant, meter or policy text. A denial envelope is the same for every verdict with that reason.
- `remediation: "unavailable"` tells the client not to retry the request unchanged and not to start a reauthorization flow. The retry class says what can change that: `after_user_action`, `next_turn` and `after_escalation` reasons can succeed later, after the user, the next turn or a reviewer acts.
- SEP-2643's optional `authorizationContextId` is a correlation handle the server issues, so the profile does not set it; a server may add it.
- A rejected verdict of any event gets an envelope, a host-protocol error included (Verdict, above). The server decides which reach the client: a denial of a `tools/call` comes from a `propose` or a `dispatch`.
- SEP-2643 says "A server MUST NOT attach the envelope to a result in which the operation partially executed." So a server never forwards the envelope of an event reported after a claim: a rejected `result`, `outcome_unknown` or `reconcile` concerns a call that may have run, and its outcome is reported through the disposition instead.
- The `needs_approval` envelope assumes the client declared the tasks extension, so the server can return a task (SEP-2643 case 2). When the denied request declared neither `elicitation.url` nor `io.modelcontextprotocol/tasks`, SEP-2643 has the server answer with a `CallToolResult` whose envelope has `remediation: "undisclosed"` and no hints; the server writes that envelope itself, since the kernel does not see the client's capabilities.

### `writ check --profile` and `writ explain --profile`

`writ check <policy.json> --profile mcp-tool-approval` adds two findings to the usual ones, for the policy the kernel runs (for layer 2, the `writ expand` output):

| Code | Kind | Message |
|---|---|---|
| `profile_retry_after_unknown` | error | retry_after_unknown is true, but under SEP-2848 outcome-unknown is final: a call whose outcome is unknown must never run again |
| `profile_max_attempts` | warning | max_attempts is above 1 without retry_after_unknown, so it has no effect: under SEP-2848 a call runs at most once |

```sh
$ writ check tests/cli/policies/profile-retry.json --profile mcp-tool-approval
error: payments.refund: retry_after_unknown is true, but under SEP-2848 outcome-unknown is final: a call whose outcome is unknown must never run again
warning: docs.read: max_attempts is above 1 without retry_after_unknown, so it has no effect: under SEP-2848 a call runs at most once
1 error, 1 warning
```

The exit codes are the usual ones; another profile id is a usage error, exit 2. The profile adds no other rule, because the kernel already decides the rest of section 13's list:

| SEP-2848 rule | Kernel rule |
|---|---|
| `outcome-unknown` is final, no re-invocation | `profile_retry_after_unknown` above: without `retry_after_unknown`, a `dispatch` of an Unknown call is rejected (`retry_not_allowed`, or `already_reconciled`), which `profile_unknown_final` proves (`docs/theorems.md`, Supporting results) |
| immutable call binding (R23, R24, statement 4 in `docs/sep-2848.md`) | the `call_digest` covers the tool, the arguments and the subject, and every approval binds the digest it reviewed: a dispatch with another digest is rejected `digest_mismatch` and a re-proposal of the call with another tool or digest `duplicate_call`. This holds under either `binding` setting. The policy field `binding` says only whether approvers may edit: an approver's edit sets a new digest and restarts the tally, a changed envelope that requires new approval, as statement 4 asks (`mcp-approval/s4-changed-arguments`) |
| cancel after claim is a no-op | `cancel` is accepted only for an awaiting or authorized call; after a claim it is rejected `call_dispatched` (or the stage reason of the call's status) and the outcome stays pending |
| an execution error keeps meter reservations | a `failed` result commits the reservation (or `actual_cost`) unless it carries `no_effect: true` (section 6, Meters) |

`writ explain <traces.jsonl> --profile mcp-tool-approval` prints, under each step, the disposition of every call whose status became terminal in that step (a call that `kill`, `reset` or `session_end` ended included), and the envelope of the verdict when it has one:

```sh
$ writ explain corpus/examples/coding-agent.jsonl --profile mcp-tool-approval --id coding-agent/kill-stops-everything | sed -n 8,14p
  6 propose call_id=c3 tool=shell.run -> accepted needs_approval
      envelope {"reason":"insufficient_authorization","remediation":"available","remediationHints":[{"type":"task"}],"requestId":{"session":"s1","call":"c3","generation":0}}
  7 kill -> accepted none
      disposition call_id=c2 cancelled
      disposition call_id=c3 cancelled
  8 result call_id=c1 outcome=declined -> accepted none
      disposition call_id=c1 denied-not-executed
```

The kill cancels the authorized `c2` and the awaiting `c3`; the dispatched `c1` settles at step 8, declined. A step that leaves a call's status as it was, such as a rejected dispatch of an ended call, prints no disposition for it.

### In WebAssembly and the bindings

WebAssembly function 10, `profile`, takes `{"profile": "mcp-tool-approval", "verdict": v}` or `{"profile": "mcp-tool-approval", "status": s}`, with a verdict or a call status written as above, and returns `{"envelope": ...}` or `{"disposition": ...}`, or `{}` when the profile gives none (`build/wasm/README.md`). `@anijani/writ` exposes it as `kernel.profile(id, { verdict })` or `kernel.profile(id, { status })`, and as `mcpToolApproval.envelope(kernel, verdict)` and `mcpToolApproval.disposition(kernel, status)`. The Python package `writ-kernel` mirrors them as `kernel.profile(id, {"verdict": v})` or `kernel.profile(id, {"status": s})`, and as `writ.mcp_tool_approval.envelope(kernel, verdict)` and `writ.mcp_tool_approval.disposition(kernel, status)`. No binding re-implements the tables.

`corpus/profiles/mcp-tool-approval-v1.jsonl` holds one test vector per line, `{"id", "input", "output"}`, where `input` is the function's input and `output` its result: every call status (`denied` and `denied_at_dispatch` with each reason), a rejected verdict for each of the 52 reason codes, and one verdict of every other shape. The file is what `Writ.Api.profile` gives for the inputs listed in `WritTests/ProfileVectors.lean`, and `lake build` fails when they differ. After a change to the profile, rewrite it with:

```sh
printf 'import WritTests.ProfileVectors\ndef main : IO Unit := IO.print WritTests.ProfileVectors.text\n' > /tmp/profile-vectors.lean
lake build WritTests.ProfileVectors && lake env lean --run /tmp/profile-vectors.lean > corpus/profiles/mcp-tool-approval-v1.jsonl
```

## The `writ` command

Build it from source with `lake build writ`; the binary is `.lake/build/bin/writ`.

| Command | What it does |
|---|---|
| `writ check <policy.json> [--json] [--tools f [--server s]] [--profile id]` | decode the policy, report errors and warnings, compare it with a tool list, and apply a standards profile |
| `writ expand <policy.json> [--out f]` | print the layer-1 policy a layer-2 policy expands to |
| `writ digest <policy.json>` | print the policy digest |
| `writ import mcp <tools.json> [--server s] [--preset-dir d] [--out f]` | draft a layer-2 policy from an MCP tool list |
| `writ replay <traces.jsonl>... [--coverage]` | replay traces and compare with `expect`, and list the reasons and decisions reached |
| `writ oracle <policy.json> [--state f] [--state-out f] [--digest d]` | read events on stdin, write verdicts on stdout |
| `writ explain <traces.jsonl> [--id <id>] [--profile id]` | describe each step of each trace, or of one, with a standards profile's view |
| `writ diff <old.json> <new.json> <events.jsonl> [--json]` | replay recorded events under two policies and list the changed verdicts |
| `writ traces <policy.json> [--depth N] [--max-states M] [--out dir]` | generate the shortest trace for every abstract transition of a policy (Trace generator, above) |

Exit codes for every command: 0 success, 1 findings (check errors, replay failures), 2 usage, IO, parse or decode errors. Results and findings go to stdout; errors go to stderr as `error: ...`.

`writ oracle` is the differential-testing hook for bindings. It refuses a policy that fails `writ check` (exit 2, the errors on stderr), and requires `session_start.policy_digest` (`policy_digest: missing field` otherwise). It writes exactly one JSON line per input line. A line that is not valid UTF-8, does not parse or does not decode produces `{"error": "..."}` and leaves the state unchanged; it keeps going, and the exit code is still 0. An empty line is such a line. `--digest` sets the digest expected in `session_start` instead of the policy file's. `--state` starts from a saved state and must match that digest.

```sh
$ printf '{"type":"cancel"}\nnot json\n\n' | writ oracle tests/cli/policies/formats-shop.json
{"error":"seq: missing field"}
{"error":"invalid literal at line 1, column 1"}
{"error":"unexpected end of input at line 1, column 1"}
```

### `writ diff`

`writ diff <old.json> <new.json> <events.jsonl> [--json]` replays recorded traffic under two policies and lists the events whose verdict changed, so you can see what a policy change does before you deploy it. Each policy may be layer 1 or layer 2; a layer-2 policy is expanded as `writ expand` expands it, `extends` included. A policy that `writ check` reports errors for is refused (exit 2, the errors on stderr, each naming the file).

The events file holds one event per line, as `writ oracle` reads them, except that a `session_start` may omit `policy_digest`, as inside a trace; diff supplies each run's. Every line must parse and decode before anything runs: an empty line or one that does not parse or decode is exit 2, with its line number (`error: events.jsonl: line 3: seq: missing field`). A file holding nothing but line breaks has no events (`0 of 0 events changed`, exit 0).

The file holds one session: its first event is a `session_start` and no later event is one. Events carry no session id, so diff cannot split interleaved sessions, and a second session's events would run in the first session's state under both policies (its `session_start` rejected `already_started` by both) and compare equal without having been replayed. So a first event of another type, or a second `session_start`, is exit 2 naming its line (`error: events.jsonl: line 12: a second session_start; diff replays one session per events file`); split such traffic into one file per session. Each policy runs from a fresh state under its own digest (for layer 2, the digest of the `writ expand` output). Before each event, diff sets the event's `state_version` to that run's current version and a `session_start`'s `policy_digest` to that run's digest. So traffic recorded under the old policy still starts a session under the new one, and once the runs diverge (an event one policy accepts and the other rejects leaves their versions apart), later events are still compared on their merits instead of all failing with `state_version_mismatch`. The recorded `state_version` and `policy_digest` are therefore never checked. Everything else in an event is replayed as recorded, including payloads that carry recorded state, such as the `ledger` of a `ledger_sync` and the `request_id` generation of an `approve` or `reject`; after a divergence those can differ for real under one policy (a `ledger_conflict` or a `stale_request`), and diff lists that as a change.

Verdicts are compared as JSON with `state_version` left out; every other key counts (`decision`, `reason`, `request_id`, `grant`, `meters`, `would_deny`, and so on). The text output has one line per changed event, `line <n> seq <s> <type>[ <call_id>]: <old verdict> -> <new verdict>`, the first suffixed ` (first divergence)`, then `<k> of <m> events changed`, followed by `, <j> rejected under both policies` when both policies rejected j > 0 of the events. Such an event is not listed when the two rejections are the same, yet neither policy accepted it, so traffic that fits neither policy (a stale `seq`, a call never proposed) shows in the count instead of passing as unchanged. Each verdict is printed as compact JSON without `state_version`, `retry` and `message` (both follow from the reason). With `--json`, diff prints one object per changed event, `{"line", "seq", "type", "call_id"?, "old", "new"}`, where `old` and `new` are the whole verdicts without `state_version`, and no count. Exit 0 when no verdict changed, 1 when one did, 2 for a usage, IO or policy error.

The events in `tests/cli/diff/old-events.jsonl` were recorded under a policy where `buy` is free; `tests/cli/diff/tight.json` makes it need approval:

```sh
$ writ diff tests/cli/diff/old.json tests/cli/diff/tight.json tests/cli/diff/old-events.jsonl
line 4 seq 4 propose c1: {"verdict":"accepted","decision":"allowed"} -> {"verdict":"accepted","decision":"needs_approval","request_id":{"session":"s1","call":"c1","generation":0}} (first divergence)
line 5 seq 5 dispatch c1: {"verdict":"accepted","decision":"dispatch_claimed"} -> {"verdict":"rejected","reason":"call_awaiting"}
line 6 seq 6 result c1: {"verdict":"accepted"} -> {"verdict":"rejected","reason":"call_awaiting"}
3 of 11 events changed
$ writ diff tests/cli/diff/old.json tests/cli/diff/tight.json tests/cli/diff/old-events.jsonl --json | head -1
{"line":4,"seq":4,"type":"propose","call_id":"c1","old":{"verdict":"accepted","decision":"allowed"},"new":{"verdict":"accepted","decision":"needs_approval","request_id":{"session":"s1","call":"c1","generation":0}}}
```

The dispatch and result of `c1` are rejected under the new policy, which leaves its state two versions behind the old one; the next call, `c2`, is still accepted under both and is not listed. Two identical policies list nothing and print `0 of 11 events changed`, exit 0.
