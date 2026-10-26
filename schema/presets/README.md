# Writ presets

A preset is a layer-2 policy file with only `writ`, `$schema`, `labels` and `rules`: a risk vocabulary and the requirements it implies. Your policy extends it, labels its actions on the preset's dimensions, and sets the policy-level fields (`approver_roles`, `limits` and the rest) itself. `writ expand` turns the result into the layer-1 policy the kernel runs.

There is no built-in name lookup: `extends` takes a path relative to the directory of the file that lists it. Copy a preset next to your policy or point at it where it lives. Each preset's `$schema` is relative to `schema/presets/`, so a copy moved elsewhere loses editor validation until you fix that path; `writ` ignores `$schema`.

```json
{
  "writ": "0.1",
  "extends": ["presets/generic-tiers.json"],
  "approver_roles": ["owner"],
  "limits": { "approval_ttl_ms": 600000 },
  "actions": {
    "vm.status": { "labels": { "risk": "read" } },
    "vm.restart": { "labels": { "risk": "device" }, "grantable": { "scope": "session", "max_uses": 5 } },
    "vm.terminate": {}
  }
}
```

`vm.restart` expands to `"consent": "per_call"` and keeps its grant; `vm.terminate` is unlabeled, so it is `destructive`, needs an approver other than the requester and loses any `grantable`. The presets are not part of `@anijani/writ` or the WebAssembly build, which accept only layer 1: expand first and load the expanded file.

A policy that extends a preset cannot set the policy-level `"mode": "log_only"` (`writ check` reports `extends_log_only`). To shadow a rollout, write `"mode": "log_only"` on each of your own actions instead.

## How labels resolve

- Label values are strings, also in `mcp-annotations`: `"read_only": "true"`, not `true`.
- An action that does not label a dimension takes that dimension's strictest (last) value, so every rule on that dimension applies to it. Leaving labels out is never a way to loosen a preset.
- When an action is named in several files, each dimension takes the strictest value over the files that name it, a file that does not label the dimension counting as the strictest value.
- Rules only add strictness: they raise `consent`, cap or forbid `grantable`, force `retry_after_unknown` to false (and, in `mcp-annotations`, `idempotent` too) and add `flags`. An action can be stricter than its labels imply, never weaker.
- A rule's consent names no roles, so any approver role can approve. Your policy must declare `approver_roles`, or no one can approve.

## generic-tiers

One dimension, `risk`: `read`, `navigate`, `device`, `spend`, `destructive`.

| When | Requires |
|---|---|
| `risk >=device` | `consent: per_call` |
| `risk >=destructive` | `consent: { quorum: 1, human_only: true, exclude_requester: true }`, `grantable: null` |

A `destructive` action therefore needs one approval from a human approver other than the requester, and it is never grantable.

## mcp-annotations

The MCP tool annotations, each with MCP's pessimistic default as its strictest value, so a tool without annotations is treated as MCP says a client must assume: not read-only, destructive, not idempotent, open world.

| Dimension | Order | MCP annotation |
|---|---|---|
| `read_only` | `true`, `false` | `readOnlyHint` |
| `destructive` | `false`, `true` | `destructiveHint` |
| `idempotent` | `true`, `false` | `idempotentHint` |
| `open_world` | `false`, `true` | `openWorldHint` |

| When | Requires |
|---|---|
| `read_only >=false` | `consent: per_call` |
| `destructive >=true` | `consent: per_call`, `grantable: null` |
| `idempotent >=false` | `idempotent: false`, `retry_after_unknown: false` |
| `open_world >=true` | `flags: ["sends_external"]` |

Annotations come from the tool server and are untrusted: label from them only to raise strictness, never to lower what you would otherwise require. `writ import mcp` drafts a policy from a `tools.json` that extends this preset and labels every tool at these strictest values, whatever its annotations claim; it copies the claims into each action's `source.annotations` and names on stderr each one it did not apply, for you to review before lowering a label by hand (`docs/formats.md`, Import from MCP).

## mcp-risk-metadata

The risk metadata of the MCP draft SEP-2793.

| Dimension | Order | SEP-2793 field |
|---|---|---|
| `risk_level` | `low`, `medium`, `high`, `critical` | `riskLevel` |
| `blast_radius` | `self`, `team`, `org`, `public` | `blastRadius` |
| `reversibility` | `reversible`, `partially`, `irreversible` | `reversibility` |
| `approval_recommendation` | `none`, `single`, `multi` | `approvalRecommendation` |

| When | Requires |
|---|---|
| `risk_level >=high` | `consent: per_call` |
| `approval_recommendation >=single` | `consent: per_call` |
| `approval_recommendation >=multi` | `consent: { quorum: 2 }` |
| `reversibility >=irreversible` | `grantable: null` |
| `blast_radius >=public` | `flags: ["sends_external"]` |

The conditions of one rule all have to hold, so "high risk or a recommended approval" is two rules.

## axes

Five independent axes.

| Dimension | Order |
|---|---|
| `effect` | `none`, `read`, `write`, `delete` |
| `reversibility` | `reversible`, `partially`, `irreversible` |
| `audience` | `self`, `internal`, `external` |
| `value` | `none`, `low`, `high` |
| `data` | `public`, `internal`, `private` |

| When | Requires |
|---|---|
| `effect >=write` | `consent: per_call` |
| `effect >=delete` | `grantable: null` |
| `reversibility >=irreversible` | `grantable: null` |
| `audience >=external` | `flags: ["sends_external"]` |
| `data >=private` | `flags: ["reads_private"]` |
| `value >=high` | `consent: { quorum: 1, human_only: true, exclude_requester: true }` |

An action with `effect >=write` and `value >=high` gets two consent groups, `per_call` and the one above. The kernel checks every group against the same approvals, so one approval from a human approver other than the requester satisfies both: one approval, not two.

## Quorum 2

Only `mcp-risk-metadata` can produce a quorum of 2, from `approval_recommendation: multi`. Such an action needs two different human approvers at runtime (`human_only` defaults to true), one of whom may be the requester, so `multi` is not a four-eyes rule against the requester. The deployment needs at least two people who hold an approver role, and the action loses any `grantable`, because a grant stands in for one approval. `writ check` does not count your approvers.

## Using several presets

The presets' dimensions have different names except `reversibility`, which `mcp-risk-metadata` and `axes` declare with the same order and the same rule, so a policy can extend any combination of them. A dimension declared with two different orders is a `conflicting_dimension` error, so if you edit a copy of one of them, keep its `reversibility` order or a policy extending both fails to check. Every action is resolved on every dimension of every extended preset, so label all of them, or the unlabeled ones count as their strictest values.

## Tests

`tests/cli/presets/` has a small policy extending each preset, one extending both `axes` and `mcp-risk-metadata`, and an unlabeled action in each. `scripts/cli-test.sh` expands them (`tests/cli/expand-preset-*.case`), checks each expanded policy, and checks each preset on its own (`tests/cli/check-preset-*.case`). The presets need no new proofs: theorem 13 holds for any labels and rules.
