# Standard corpus

The standard corpus is generated from the fixture policies in `fixtures/` by `writ traces` (spec
section 9, `docs/formats.md` Trace generator). The generated traces are never committed:
`scripts/corpus.sh` writes them to `build/corpus/standard/<fixture>.jsonl`, checks them against
`manifest.json`, replays them with the hand-written corpora and checks that every reason code in
`schema/reasons.json` is reached. `scripts/corpus.sh --tar` packs the generated and hand-written
corpora, the digest vectors and these READMEs into `build/writ-corpus-<version>.tar.gz`.

`manifest.json` pins, per fixture, the depth and `max_states` it is explored with and what that gives:
the number of traces and abstract states, whether `max_states` cut the search short (it never does
here) and the SHA-256 of the generated file. The output is deterministic, so any difference means
the fixture, the explorer or the kernel changed. Review it, then run `scripts/corpus.sh --update`.
`uncovered.json` lists the reason codes that no replayed verdict reaches, each with a reason; it is
empty.

Every fixture has at most 4 actions and passes `writ check` without errors (`retry.json` and
`meters-settle.json` each with one warning, below). The state space grows about fivefold per level
of depth, so most fixtures run at depth 3; `retry` and `escalation`, which need a dispatch and an
outcome before the event they are for, run at depth 4 with one or two actions; `basic` and `meters`
run at depth 2, which reaches every reason they are for (`meters` at depth 3 would blow the budget of
25000 traces on its own). `manifest.json` gives each fixture's depth and trace count.

| Fixture | What it uses | Reasons only it reaches in the generated corpus |
|---|---|---|
| `basic` | a free action with a permission, a `per_call` action with a guard, an action with `exposed: false`, `binding: immutable`, `kill_scope: principal` | `edit_not_allowed`, `permission_missing` |
| `quorum` | consent as two `groups`, one needing quorum 2; a `distinct` group of two clauses with roles, `exclude_requester` and `human_only` false; a turn-grantable action whose only consent comes from a grantable escalator | `already_approved` |
| `grants` | a `turn` grant with `max_uses` 1, a `session` grant with `max_uses`, `max_duration_ms` and `any_args` | `grant_invalid` |
| `meters` | a session money meter with `max_per_call` on a `consent_if_cost_over` action whose `any_args` session grants are allowed on it by `allow_any_args_metered` (grants carry `max_cost`), a principal money meter in a second currency with a window, a principal calls meter with a window | `currency_mismatch` |
| `meters-settle` | one action on a windowed principal money meter and a session calls meter without a cap (the `meter_without_cap` warning), explored to its results: commits, releases and overruns | the `overrun` decision |
| `lifecycle` | a policy authorization TTL and a per-action approval TTL, step, proposal and approval limits per turn | `proposal_limit`, `step_limit`, `approval_budget` |
| `shadow` | policy-wide `log_only` with an `enforce` action and an unexposed one; session proposal and approval limits | `session_proposal_limit`, `session_approval_budget` |
| `retry` | two `idempotent` actions with `retry_after_unknown`, one with `max_attempts` 2 and one with the default 1 (the `retry_without_attempts` warning, which is the point: its retry is refused) | `idempotency_key_mismatch`, `attempt_limit` |
| `escalation` | one free action with tool-scoped escalation after one failure and its own `escalation_roles` | `retry_not_allowed`, `escalated` |

The reasons every fixture reaches (the envelope checks, call stages, approvals, unknown ids and
grants, the ledger probes) are not listed. `already_reconciled` needs depth 5 (a proposal, a
dispatch, an unknown outcome, a reconcile, then a second dispatch or reconcile), so the generated
corpus does not reach it; `corpus/examples/device-split.jsonl` does (`device-never-reports`), which
is why `uncovered.json` stays empty.

One requirement feature is in no fixture: `max_failures_per_session`, which
`corpus/examples/payments.jsonl` uses (any failure escalates its sessions); a fixture that reaches a
session's failure total would exceed the budget. The fields the kernel never reads (`review`,
`messages`, `source`, `flags`) are in no fixture either.

The spec lists failure limits, retries and session limits under one lifecycle fixture. Failure
limits and `escalation_roles` live in `escalation` and retries in `retry`, because both need depth 4.
The session limits live in `shadow`: next to `lifecycle`'s per-turn limits, a session limit is reached
only in a second turn, beyond depth 3. So `lifecycle` keeps the TTLs and the per-turn limits.
