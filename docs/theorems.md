# Section 8 statement map

This page is for a reviewer who checks section 8 of `docs/design.md` without reading proofs or the kernel. For each theorem it quotes the spec sentence, lists the Lean results that discharge it with a plain reading of each, says what each result assumes and which of those hypotheses go beyond section 8's own assumptions, and says what no listed result states. Check each spec sentence against the listed statements: `lake build`, then `scripts/print-statements.sh` prints every pinned statement without its proof, and `scripts/print-statements.sh --defs` adds the `WritProofs` definitions those statements use. The plain readings below are a guide; the printed statements are what is proved. All names are in the namespace `Writ.Proofs`, and every named result is pinned in `WritProofs/Axioms.lean`, so its axioms are checked to be among `propext`, `Classical.choice` and `Quot.sound` (`scripts/check-proofs.sh`).

## Reading the statements

**The kernel's shape.** `step p s e` is the kernel: policy `p`, state `s`, event `e`, giving the next state `(step p s e).fst` and the verdict `(step p s e).snd`. `run` folds `step` over a list of events. The statements speak about these two functions, the data types in `Writ/Core/*.lean`, and the `WritProofs` definitions printed by `--defs`.

**Words used throughout.**

- `Reachable p d s`: `s` is reached from `State.initial d` by stepping any finite list of events, accepted or rejected, under `p`. This is section 8's "the trace is any finite event sequence from the initial state". `d` is the policy digest the session expects; no statement ties it to `p`.
- `after p d es`: the state after running `es` from `State.initial d`.
- `trace p s es`: one entry per event of `es`, holding the state before the event, the event and its verdict. `#print` shows a recursive definition such as `trace` or `interleave` in compiled form, so `--defs` prints its equations after it.
- `Verdict.claimed v`: `v` is `ok dispatch_claimed`, section 8's "claimed dispatch". `Verdict.accepted v`: `v` is `ok`.
- `entriesOf p s m`: the meter entries of meter `m` as session `s` sees them: its copy of the principal ledger for a principal-scope meter, else its session entries. `usageAt spec es m t`: the usage of `m` at time `t`, counting an entry while `t` is below its time plus `window_ms`, and its excess while `t` is below `excess_at` plus `window_ms`, with no lower bound (section 6, Meters). `draw spec cost`: what a call draws, its cost amount on a money meter and 1 on a calls meter. `ownEntries p s m k`: the entries of `entriesOf p s m` that belong to this session and call `k`.

A statement with no `Reachable`, `after` or `trace` from `State.initial` hypothesis holds from every state, reachable or not, which is stronger than section 8 asks.

**Definitions outside `WritProofs`.** Besides fields and constructors, the statements and the `WritProofs` definitions use these functions, which `--defs` does not print. Read them in the named file. `--defs` ends with the current list (`== outside WritProofs`, one function and its module per line), so check this table against it.

| Function | File | Note |
|---|---|---|
| `step`, `stepEnvelope` | `Writ/Kernel/Step.lean` | `stepEnvelope` only in `envelope_iff`, which ties `EnvelopeOk` to it |
| `run` | `Writ/Kernel/Run.lean` | through `after` |
| `claim` | `Writ/Kernel/Step/Dispatch.lean` | only in `claim_post` |
| `Meter.usage` | `Writ/Kernel/Meter.lean` | only in `usageAt_eq`, which says `usageAt` is it |
| `Ledger.setTombstone` | `Writ/Kernel/Step/Control.lean` | only in `storeLedger_eq` |
| `State.eligibleFor`, `State.satisfied` | `Writ/Kernel/Eligibility.lean` | only in `eligibleFor_sound`, `satisfied_sound` and `ConsentInv.quorum` (`consentInv_reachable`) |
| `Policy.WF`, `Policy.check` | `Writ/Author/Check.lean` | `p.WF` is `p.check = []`: the policy check reports no error |
| `Policy.action?`, `Policy.meter?`, `Policy.modeOf`, `Policy.approvalTtl`, `Policy.authorizedTtl`, `Consent.clauses`, `Consent.single`, `Consent.none`, `GrantScope.le` | `Writ/Core/Policy.lean` | `modeOf` is `enforce` for an undefined or unexposed tool, else the action's own mode, else the policy's mode; the TTLs are the action's value, else the policy's |
| `Consent.join`, `Requirements.effectiveConsent`, `Requirements.grantConsent` | `Writ/Core/Consent.lean` | effective consent: the base consent (or none under `consent_if_cost_over`) joined with every fired escalator's consent, a missing escalator counting as fired |
| `Consent.le`, `Requirements.le`, `Require.le`, `GrantLe`, `GrantCap.le`, `BoolLe`, `ListLe`, `ModeLe`, `CostLe`, `EscLe`, `Escalator.le`, `DurLe`, `Requirements.joinStrict`, `Requirements.joinReq`, `GrantCap.apply`, `grantJoin`, `guardJoin`, `flagJoin`, `modeJoin`, `costJoin`, `escJoin`, `escAt`, `Escalator.join`, `durMeet` | `Writ/Author/Join.lean` | only in theorem 13 and its lattice laws; see that section |
| `expand`, `explicitReq`, `mergedDims`, `mergedActionLabels`, `Rule.matches`, `Policy2.check`, `Policy2.problems` | `Writ/Author/Expand.lean` | only in theorem 13; see that section |
| `CallStatus.terminal` | `Writ/Core/State.lean` | every status except Awaiting, Authorized and Dispatched; Unknown is terminal |
| `lookupFlag` | `Writ/Core/Event.lean` | a guard value by name |
| `State.initial` | `Writ/Core/State.lean` | the state before `session_start` |
| `Profile.McpToolApproval.errors`, `Profile.McpToolApproval.problems` | `Writ/Profile/McpToolApproval.lean` | only in `profile_unknown_final` (`problems` through `errors`, so `--defs` lists `errors` alone); `problems p` lists, for each action in order, `profile_retry_after_unknown` when it sets `retry_after_unknown`, else `profile_max_attempts` when its `max_attempts` is above 1; `errors p` keeps the first kind, the errors |

**Hypotheses that narrow a statement.** Section 8 assumes `Policy.WF`, a trace from the initial state and an action in `enforce` mode. The sections below say which of these each result carries, and list every other hypothesis that narrows it. The recurring ones:

- `Reachable p d s`, or a state written `after p d es`: section 8's trace assumption. Results about one step from `s` carry it when they read an invariant that only reachable states have.
- `p.WF`: section 8's policy assumption. Carried where a fact the policy check guarantees is needed (attempt limits at least 1, positive windows and failure limits, meters defined, `max_per_call` only on money meters).
- `p.modeOf tool = .enforce`: section 8's mode assumption, carried where a `log_only` action would make the statement false (its decisions that would deny are recorded and the call goes on). `steps_per_turn` carries the policy-level `p.mode = .enforce` instead.
- `hfresh`: in `no_claim_over_cap`, `ledger_cap` and `multi_cap`, the call is Authorized (a first attempt) or every one of its own entries on the meter has left the window (a retry that must fit the cap again). A retry inside the window reserves nothing new (section 6, Meters), so it is outside "no reservation is accepted that would bring usage above the cap".
- `Disciplined p log` (`DisciplinedP pol log` over several policies): every commit of the interleaving that changes the ledger version, other than `ledger_sync` and `session_start`, was taken on a state whose ledger equals the stored ledger before it. This is theorem 9's own hypothesis, what the two-version compare-and-swap of section 7 gives; it is a duty of the binding, not something Lean proves of any binding.
- `MeterAgree pol m`: every two session policies that define `m` as a principal meter give it the same unit (kind and currency) and the same `window_ms`. This is theorem 9's own condition for sessions of different policies.
- `¬ Op.store false ∈ ops`: no out-of-band clear of the stored tombstone anywhere in the schedule (only `multi_kill_event`); `multi_kill_after` asks it only of the ops after the kill.
- `TimeOrdered ops`: the event times of the schedule's step ops never decrease along it (only `multi_window_ordered`). This is section 10's trusted monotone clock shared by the sessions.

**What no statement covers.** The statements are about Lean values of `Writ.Event`, `Writ.Policy` and `Writ.State`, and for theorem 13 of `Writ.Policy2` and `Writ.File2`. No statement covers the JSON codec or its 512-byte string limit, the `writ` command, the WebAssembly build, the TypeScript package, or any host or binding duty: executing a tool only on a claim, storing with compare-and-swap, unique session ids, a trusted clock, the untrusted-report clamp and the state byte budget.

## Theorem 1: Consent

> 1. **Consent.** If a dispatch is claimed for a call whose recorded consent (the effective consent at propose, joined with the effective consent of every approver edit) is not `none`, then either (a) every group of that consent is satisfied by the approvals of the call's final generation (for every clause, at least k distinct principals eligible for the clause, and for a `distinct` group an assignment of distinct principals to all clause slots (approver role and a clause role, human if `human_only`, not the requester if `exclude_requester`, never `agent`)), each approval with reviewed digest and cost equal to the dispatched ones (for an approver's edit, the digest and cost it set), with matching `request_id`, within the action's `approval_ttl`, and no eligible approver rejected any generation of it; or (b) every clause has k at most 1 and no `distinct` group has more than one clause, every escalator that fired at propose is grantable, a grant created by an approver eligible for every clause covered the call at propose (including its `max_cost`) and is valid at dispatch (not revoked, same epoch, inside its time window and turn), and its use was reserved for this call.

| Result | File | Plain reading |
|---|---|---|
| `consent_claim` | `WritProofs/ConsentClaim.lean` | A claimed dispatch, after any trace from the initial state, of an enforced call `c` whose consent has a clause dispatches `c.digest` and `c.cost`, and either (a) `c` holds no grant, its tally meets the consent (`ConsentMet`), every tally entry is an accepted approval of the current generation (`ApprovedBy`), and no `reject` of the call was ever accepted; or (b) `c` holds grant `gid` that covers it now (`GrantCovers`), covered it at its propose (`GrantAtPropose`), and holds a reserved use (no attempt yet) or a consumed one (a retry), which the grant's counters count. |
| `consent` | `WritProofs/Consent.lean` | The step form over a reachable state: (a) no grant and the tally meets the consent (`ConsentMet`), without the approval history, or (b) `GrantCovers`. |
| `approvals` | `WritProofs/Approvals.lean` | A claim dispatches the recorded digest and cost, and every tally entry is `ApprovedBy`. |
| `no_reject_before_claim` | `WritProofs/Approvals.lean` | Before a claim of call `k`, no `reject` of `k` was accepted. |
| `consent_recorded_propose` | `WritProofs/ConsentClaim.lean` | An accepted `propose` of a new call of a defined action records it with the effective consent at propose whenever it is Authorized or Awaiting and enforced (or carries no would-deny shadow); a denied record holds that consent or the base consent. |
| `recorded_by_propose` | `WritProofs/ConsentClaim.lean` | A call record that did not exist before a step was made by a `propose` of that call id for a defined action. |
| `consent_recorded` | `WritProofs/ConsentClaim.lean` | An accepted `approve` with an edit sets the call's consent to its consent joined with the edited arguments' effective consent (the new cost, else the current one, and the edit's escalators); every other step leaves a recorded call's consent as it was. |
| `consent_claim_fired` | `WritProofs/ConsentClaim.lean` | Under `consent_claim`'s hypotheses, for a call holding grant `gid` (case (b)): the accepted `propose` that created the call carried its tool, digest and cost and was answered `allowed_by_grant gid`; the call's consent is the effective consent of that event's escalators and a single approval; and every escalator of the action that fired in that event (missing or true in its `escalators`) is grantable (`FiredAtPropose`). |
| `call_origin` | `WritProofs/Origin.lean` | After any trace from the initial state, every call record holds what events carried (`CallOrigin`): the accepted `propose` that created it, at a state with no record of the call, carried its tool, proposed digest and cost, and its `proposedEscalators` are that event's escalators filtered to the names the action defines; a call holding a grant was answered `allowed_by_grant` for it, has the effective consent of that event's escalators and is at generation 0; and its generations list holds one entry per generation, the first the proposed digest and cost, the last the current ones, each digest being the one the events carried for that generation (`GenerationDigest`). |
| `grant_origin` | `WritProofs/Grants.lean` | After any trace from the initial state, every grant record was created by an accepted `grant_create`, at a state with no grant of that id, that carried the record's approver, tool, digest, scope, `max_uses`, `max_cost`, `not_before`, `expires_at` and reviewed scope digest; its epoch and turn are the session's at that event and its principal the approver's attested principal; the create left it with zero counters and not revoked, so later steps changed only the use and cost counters and `revoked` (`GrantOrigin`). |
| `approver_origin` | `WritProofs/Approvers.lean` | After any trace from the initial state, every entry of the approver map, its principal, kind and roles, is one an accepted `session_start` listed for that id or one an accepted `approver_attest` of that id carried (`ApproverOrigin`). |
| `requester_origin` | `WritProofs/Approvers.lean` | After any trace from the initial state that started the session, the requester is the one an accepted `session_start` of the trace carried, and every accepted `session_start` of the trace carries it (`RequesterOrigin`). |
| `call_times` | `WritProofs/Times.lean` | After any trace from the initial state, every call record's times are event times (`CallTimes`). While the call is Awaiting, and once its tally is not empty, `requestedAt` is the time of the event that requested approval of its current generation (`RequestTime`): for generation 0 the accepted `propose` that created the call, answered `needs_approval`; for a later generation the accepted `approve` whose edit made it. Once `authorizedAt` is set, it is the time of the accepted `propose` that created the call, answered `allowed` or `allowed_by_grant`, or of an accepted `approve` of the call answered `authorized` (`AuthorizationTime`). |

How the definitions match the sentence: `ConsentMet` asks each group to be met (`GroupMet`): for a plain group, for every clause, `k` tally entries of distinct principals eligible for it; for a `distinct` group, distinct principals for all `k` slots of all clauses. `EligibleFor` is attested, principal not `agent`, an approver role, a clause role when the clause names roles, human if `human_only`, not the requester if `exclude_requester`. `ApprovedBy` is an accepted `approve` from that approver of this call, with the request's session and call, in the pre-state's generation of the call, at a time from the request to before the request plus `approval_ttl`, which either reviewed the current digest and cost of the current generation or is the edit that made it (new digest, new cost or else the reviewed cost). `GrantCovers` is `Consent.single`, every escalator not reported false grantable, the grant's tool and digest, its approver eligible for every clause, not revoked, same epoch, inside `[not_before, expires_at)`, and in the current turn for a `turn` grant. `GrantAtPropose` is the call's own `propose` answered `allowed_by_grant gid`, at which the grant matched, was valid, had a use left, fit `max_cost` in the same currency, and had an approver eligible for every clause. `GrantCovers` and `GrantAtPropose` read the grant's limits, window, scope, digest and epoch from its record, and `grant_origin` says those are the fields of the `grant_create` that created it. `GrantCovers` reads the fired escalators from the call record's `proposedEscalators`; `FiredAtPropose` reads them from the `propose` event itself, and `call_origin` says the record keeps exactly the event's escalators that the action defines, which are the only names `GrantCovers` looks up. An edit never changes `proposedEscalators`, and a call holding a grant is never edited (`call_origin`: generation 0). `EligibleFor` and `GroupMet` read the approver map and the requester from the state; `approver_origin` and `requester_origin` say those are what the `session_start` and `approver_attest` events carried. `ApprovedBy` bounds an approval by the record's `requestedAt` plus `approval_ttl`, for the dispatched record (whose tally is not empty) and for the Awaiting record the approval read; `call_times` (applied to the trace before the approval for the second) says that `requestedAt` is the time of the event that made the request.

**Assumes.**
- A trace from the initial state (`after p d es`): section 8's assumption.
- `p.modeOf c.tool = .enforce`: section 8's assumption. A `log_only` call goes on whatever its consent.
- `c.consent.clauses ≠ []`: the spec's "not `none`".
- `c.grant = some gid` in `consent_claim_fired`: case (b).
- `call_origin`, `grant_origin`, `approver_origin` and `call_times` assume only a trace from the initial state, with no mode hypothesis; `requester_origin` also assumes the session has started (before `session_start` the requester is the initial empty string).
- No `p.WF`: the results hold for every policy.

**Not claimed.**
- No single statement says that the consent `consent_claim` reads, `c.consent` at dispatch, is the effective consent at propose joined with every edit's. The reader composes `recorded_by_propose`, `consent_recorded_propose` (at propose, for an enforced call proposed Authorized or Awaiting) and `consent_recorded` (every later step) along the trace. For a call holding a grant, which is never edited, `consent_claim_fired` states it directly: the consent is the effective consent of the `propose` event's escalators.
- An approver's edit counts as an approval of the generation it created, although the digest it reviewed is the old one: `ApprovedBy` admits an `approve` with an edit whose request echoes generation `c.generation - 1` (`rid.generation + 1 = c.generation`) when its new digest is `c.digest` and its new cost (else the reviewed cost) is `c.cost`. This is section 6's rule that an edit counts as that approver's approval of the new generation, and the spec sentence's "(for an approver's edit, the digest and cost it set)": for an edit, the digest and cost equal to the dispatched ones are its new digest and cost, not its `reviewed_digest`.
- Eligibility in `ConsentMet` and `GrantCovers` is read against the state at dispatch, not at approval or grant creation. `consentInv_reachable` (fields `approvers` and `requester`) says no step changes or removes an attested approver, or changes the requester once the session has started, which is what makes the two agree; `approver_origin` and `requester_origin` say both came from the `session_start` and `approver_attest` events.
- (b) says the grant's approver is eligible for every clause of the call's consent at propose and at dispatch. It does not restate eligibility at grant creation; `accepted_iff_grantCreate` covers that, against the action's base consent and every grantable escalator's.
- `RequestTime` and `AuthorizationTime` name an accepted event of the right kind for the call (and generation) at the recorded time; they do not say it is the only such event in the trace. The kernel's checks make it so (a call id is created once and never removed, `calls_keep`; an `approve` must echo the current generation, `approve_fresh`, and an edit moves the generation on), but no statement composes this.
- `call_times` says nothing of `requestedAt` for a call that was never Awaiting and has no approval (proposed Authorized or denied); the kernel leaves it 0, and no statement reads it.

## Theorem 2: Grant accounting

> 2. **Grant accounting.** At all times a grant's consumed plus reserved uses are at most `max_uses`, and its consumed plus reserved cost is at most `max_cost`; at most `max_uses` claimed first attempts use the grant, and their costs sum to at most `max_cost`; a use returned by a call that ended without dispatch can be reused; retries of an Unknown call consume no extra use.

| Result | File | Plain reading |
|---|---|---|
| `grantInv_reachable` | `WritProofs/Grants.lean` | At every reachable state, each grant's `reserved` and `consumed` counters equal the number of its calls that are Authorized with no attempt and that were dispatched at least once; with `max_cost`, its reserved and consumed cost equal those calls' costs; consumed plus reserved uses are at most `max_uses`, and consumed plus reserved cost at most `max_cost`; and every grant a call names exists. |
| `grant_uses` | `WritProofs/Grants.lean` | After any trace from the initial state, the claimed first attempts that use grant `gid` (claimed dispatches of a call Authorized with that grant before the event) number at most the grant's `max_uses`. |
| `grant_cost` | `WritProofs/Grants.lean` | For a grant with `max_cost`, the declared costs of those claims sum to at most its amount; a claim with no declared cost counts as 0 (`getD 0`). |
| `retry_no_use` | `WritProofs/Grants.lean` | A claimed retry of an Unknown call leaves every grant exactly as it was. |
| `grant_origin` | `WritProofs/Grants.lean` | Every grant record's `max_uses`, `max_cost`, window, scope, digest, tool and approver are those of the accepted `grant_create` that created it; only the use and cost counters and `revoked` change afterwards (`GrantOrigin`, see theorem 1). |
| `grant_use_returned` | `WritProofs/Reuse.lean` | From a reachable state, an accepted `cancel`, `reject` or unclaimed `dispatch` of a call that is Authorized with a reserved use of grant `gid` leaves `gid`'s record with one reserved use fewer and, with `max_cost`, its reserved cost lower by the call's cost, every other field and every other grant as they were. The grant then has room for one more use (consumed plus reserved below `max_uses`) and, with `max_cost`, for the call's cost. |
| `grant_released_all` | `WritProofs/Reuse.lean` | An accepted `kill`, `reset` or `session_end`, or an accepted `ledger_sync` that brings a tombstone the session did not have, from a reachable state leaves every grant with no reserved use and, with `max_cost`, no reserved cost, its consumed counters and limits unchanged. |

**Assumes.**
- `Reachable` for `grantInv_reachable`, `grant_use_returned` and `grant_released_all`, a trace from the initial state for `grant_uses`, `grant_cost` and `grant_origin`: section 8's assumption. `retry_no_use` holds from any state.
- In `grant_use_returned`, the event is accepted and is not a claim, and the call is Authorized with the grant: the spec's "a call that ended without dispatch" holding a use. These are the events that end such a call one at a time; `grant_released_all` covers those that end every pending call.
- No `p.WF` and no mode hypothesis: the results hold for every policy and in `log_only` mode too.

**Not claimed.**
- "can be reused" is stated as the use leaving the grant's counters at the event that ends the call (`grant_use_returned`, `grant_released_all`). After `grant_use_returned` the grant's counters have room for one more use (the room `GrantAtPropose` reads); `grant_released_all` says only that no use or cost stays reserved. No statement shows a later proposal answered `allowed_by_grant`: that also needs the grant valid (not revoked, inside its window, the session's epoch, a turn grant's turn), a matching tool and digest and an eligible approver, which returning the use does not decide. After a `reset` or `session_end` the grant is revoked as well. An `approval_expire` never ends such a call (it applies to Awaiting calls, which hold no grant); an expired authorization ends it at dispatch, the unclaimed `dispatch` case.
- `grant_uses` and `grant_cost` read the grant record at the end of the trace (`grants[gid]? = some g`), whose `max_uses` and `max_cost` are those the `grant_create` carried (`grant_origin`); for a trace after which that record does not exist they say nothing, and a reader applies them to the prefix where it does.
- `grant_cost` sums amounts without comparing currencies; the same currency is checked at propose (`GrantAtPropose`, theorem 1 (b)).

## Theorem 3: Permission

> 3. **Permission.** A proposal with a non-denied disposition (new or repeated; `existing` reports a call's past and is not a disposition here), and a claimed dispatch, only occur while the action's permission is held; every held permission was attested at `session_start` or added by an attested approver holding an approver role whose principal is not `agent`.

| Result | File | Plain reading |
|---|---|---|
| `permission_propose` | `WritProofs/Permission.lean` | A `propose` of an enforced action that names permission `perm`, new or repeated, answered `allowed`, `allowed_by_grant`, `needs_approval` or `authorized` (`Decision.nonDenied`), happens only from a state that holds `perm`. |
| `permission_claim` | `WritProofs/Permission.lean` | A claimed dispatch of an enforced action that names `perm` happens only from a state that holds `perm`. |
| `permission_origin` | `WritProofs/Permission.lean` | After any trace from the initial state, every held permission was in the permissions of an accepted `session_start`, or added by an accepted `permission_add` whose approver was attested at that point with a principal other than `agent` and an approver role (`PermissionOrigin`). |
| `approver_origin` | `WritProofs/Approvers.lean` | Every attested approver, in particular the one `PermissionOrigin` reads at the `permission_add`, was attested by an accepted `session_start` or `approver_attest` carrying that principal, kind and roles (`ApproverOrigin`, see theorem 1). |

**Assumes.**
- `p.modeOf t = .enforce` in the first two: section 8's assumption.
- A trace from the initial state for `permission_origin` and `approver_origin`. The first two hold from any state.

**Not claimed.**
- Nothing beyond the spec sentence. "Held" is read as membership in the state's `permissions` before the event. "Attested approver" in `PermissionOrigin` is an entry of the approver map at the `permission_add` (`s₀.approvers`); `s₀` is the state after a prefix of the trace, and `approver_origin` applied to that prefix says the entry was attested by a `session_start` or `approver_attest` with that principal and roles.

## Theorem 4: At most once

> 4. **At most once.** For actions without `retry_after_unknown`, at most one claimed dispatch per call, ever. For actions with it, claimed dispatches are at most 1 plus the number of accepted `outcome_unknown` events for that call, never more than `max_attempts`, with strictly increasing attempt numbers, each retry preceded by an Unknown.

| Result | File | Plain reading |
|---|---|---|
| `at_most_once` | `WritProofs/AtMostOnce.lean` | After any trace from the initial state, for a recorded call of a defined action: without `retry_after_unknown` at most one claim; at most 1 plus the accepted `outcome_unknown` events of the call; at most `max_attempts`; and the claims' attempt numbers are exactly 1, 2, ..., n. |
| `claims_need_call` | `WritProofs/AtMostOnce.lean` | A call id with no record has no claims. |
| `retry_after_unknown` | `WritProofs/AtMostOnce.lean` | A claim of a call that was claimed before is preceded, in the trace, by an accepted `outcome_unknown` of that call after which no claim of it came. |
| `traceInv` | `WritProofs/AtMostOnce.lean` | The invariant behind them, at every trace. |

**Assumes.**
- `p.WF` in `at_most_once`: section 8's assumption (a `max_attempts` of 0 is a check error).
- A trace from the initial state.
- No mode hypothesis: the result holds in `log_only` mode too.

**Not claimed.**
- Nothing beyond the spec sentence; a call recorded for an undefined tool cannot exist (`denyInv_reachable`), and an unrecorded call has no claims (`claims_need_call`).

## Theorem 5: Terminal absorption

> 5. **Terminal absorption.** Once a call reaches a terminal disposition, no event changes it, except the Unknown retry edge.

| Result | File | Plain reading |
|---|---|---|
| `terminal_absorbing` | `WritProofs/Lifecycle.lean` | From any state, a step leaves a terminal call's status as it was, except that a claimed dispatch of that call takes Unknown to Dispatched. |
| `calls_keep` | `WritProofs/Calls.lean` | No step removes a call record. |
| `calls_terminal` | `WritProofs/Calls.lean` | The weaker form: a terminal status other than Unknown never changes. |

**Assumes.** Nothing: all three hold from any state, for any policy and mode.

**Not claimed.**
- Only the status is claimed to stay. Other fields of a terminal call's record may change (section 6: `reconcile` records evidence on an Unknown call and adjusts meters).
- Which statuses are terminal is `CallStatus.terminal` in `Writ/Core/State.lean`.

## Theorem 6: Epoch and freshness

> 6. **Epoch and freshness.** No claimed dispatch uses a call from an earlier epoch; no approval is accepted with a stale `request_id` or outside the action's `approval_ttl`; no dispatch (first attempt or retry) is claimed outside the action's `authorized_ttl`.

| Result | File | Plain reading |
|---|---|---|
| `claim_epoch` | `WritProofs/Lifecycle.lean` | A claimed dispatch from a reachable state uses a call of the state's epoch. |
| `approve_fresh` | `WritProofs/Lifecycle.lean` | An accepted `approve` is of an Awaiting call of the current epoch, echoes exactly the current request id (session, call, generation), and comes before the call's `requestedAt` plus `approval_ttl`. |
| `claim_authorized_ttl` | `WritProofs/Lifecycle.lean` | A claimed dispatch of an enforced call, first attempt or retry, from a reachable state, happens before the call's `authorizedAt` plus `authorized_ttl`. |
| `claim_keeps_authorizedAt` | `WritProofs/Lifecycle.lean` | A claim moves the call to Dispatched and leaves `authorizedAt` as it was. |
| `authorizedAt_kept` | `WritProofs/Lifecycle.lean` | No step moves `authorizedAt` of a call that is not Awaiting, so a retry's TTL runs from the same time as the first attempt's. |
| `call_times` | `WritProofs/Times.lean` | An Awaiting call's `requestedAt` is the time of the event that requested approval of its current generation, and `authorizedAt`, once set, the time of the event that authorized the call (`CallTimes`, see theorem 1). |
| `approve_fresh_event` | `WritProofs/Times.lean` | An accepted `approve` after any trace from the initial state answers the current request of an Awaiting call, at or after the time `t₀` of the event that made that request (`RequestTime`) and before `t₀` plus `approval_ttl`. |
| `claim_authorized_ttl_event` | `WritProofs/Times.lean` | A claimed dispatch of an enforced call after any trace from the initial state, first attempt or retry, comes at or after the time `t₀` of the event that authorized the call (`AuthorizationTime`) and before `t₀` plus `authorized_ttl`. |

**Assumes.**
- `Reachable` in `claim_epoch` and `claim_authorized_ttl`: section 8's assumption. The others hold from any state.
- `p.modeOf c.tool = .enforce` in `claim_authorized_ttl`: section 8's assumption.
- A trace from the initial state in `call_times`, `approve_fresh_event` and `claim_authorized_ttl_event`, and `p.modeOf c.tool = .enforce` in `claim_authorized_ttl_event`: section 8's assumptions.

**Not claimed.**
- `approve_fresh` and `claim_authorized_ttl` measure from the record's `requestedAt` and `authorizedAt`. `call_times` says those are the times of the `propose` or edit that requested approval and of the `propose` or `approve` that authorized the call, and `approve_fresh_event` and `claim_authorized_ttl_event` state both TTLs over those event times. `RequestTime` and `AuthorizationTime` do not say their event is the only one of its kind in the trace (see theorem 1).

## Theorem 7: Kill

> 7. **Kill.** No claimed dispatch after an accepted `kill`, or while the principal tombstone is set.

| Result | File | Plain reading |
|---|---|---|
| `kill` | `WritProofs/Kill.lean` | After any trace from the initial state in which a `kill` was accepted, no later event is a claim. |
| `no_claim_tombstone` | `WritProofs/Kill.lean` | From any state whose ledger carries the tombstone, no step is a claim. |
| `killed_stays`, `kill_accepted_sets`, `no_claim_killed` | `WritProofs/Kill.lean` | The session's killed flag stays set, an accepted `kill` sets it, and no step from a killed state is a claim. |

**Assumes.** A trace from the initial state for `kill`; nothing else. No mode hypothesis.

**Not claimed.**
- "the principal tombstone" here is the tombstone in the session's own copy of the ledger. That no session claims while the stored ledger carries it is theorem 9 (`multi_kill`, `ledger_kill_stored`).

## Theorem 8: Bounds

> 8. **Bounds.** Under a policy-level `enforce` mode, per turn and per session, non-denied new proposals (a repeated proposal changes nothing and is not counted), `step_start` events and new `needs_approval` dispositions stay within their limits. For each meter with a cap, no reservation is accepted that would bring usage (within the window) above the cap, and no single call reserves more than `max_per_call`. Usage can exceed the cap only through an overrun (a result or reconcile reporting an actual cost above the reservation, which is committed in full because the money is already spent, and counted from the time it was reported), a reservation by a `log_only` action, or a `ledger_sync` or `session_start` that brings in a principal ledger whose usage is above the cap; every overrun counts as a failure for escalation, and while usage is above the cap no further first-attempt dispatch on that meter is claimed, nor a retry whose reservation has left the window (a retry inside the window reuses its existing reservation). Accounting invariant: every entry belongs to exactly one dispatched call of an action that uses that meter; every dispatched call, and every Unknown call not yet reconciled, has one uncommitted entry on each of its action's meters; a reconciled call that was not released keeps a committed entry, and a committed entry stays until pruning drops it outside its meter's window.

**Limits.**

| Result | File | Plain reading |
|---|---|---|
| `proposals_per_turn`, `proposals_per_session` | `WritProofs/Limits.lean` | In any trace from any state, the accepted proposals of a new call of an enforced action that are not denied (`newAllowed`) number at most the turn's (`sinceTurn`) or the session's proposal limit. |
| `approvals_per_turn`, `approvals_per_session` | `WritProofs/Limits.lean` | The proposals of a new call answered `needs_approval` (`newNeedsApproval`) number at most the turn's or the session's approval-request limit. |
| `steps_per_turn` | `WritProofs/Limits.lean` | Under a policy-level `enforce` mode, the accepted `step_start` events of the turn number at most the step limit. |

`sinceTurn` is the part of the trace after its last accepted `turn_start`, or all of it when there is none: the current turn. Each earlier turn is the current turn of a prefix of the trace.

**Meter caps and `max_per_call`.**

| Result | File | Plain reading |
|---|---|---|
| `meter_room` | `WritProofs/Meters.lean` | A claimed first attempt of an enforced call found, on each capped meter of its action, usage at the event time plus its draw within the cap. |
| `meter_cap` | `WritProofs/Meters.lean` | After a claimed first attempt, usage at the event time is within the cap. |
| `meter_room_retry` | `WritProofs/Meters.lean` | A claimed retry whose own entries all left the window found room for its draw again. |
| `meter_cap_retry` | `WritProofs/Accounting.lean` | After such a retry, from a reachable state, usage at the event time is within the cap. |
| `meter_cap_retry_of` | `WritProofs/Meters.lean` | The step form of `meter_cap_retry`, with the accounting facts it needs as hypotheses. |
| `meter_reuse` | `WritProofs/Accounting.lean` | A claimed retry with an own entry still inside the window leaves usage at the event time unchanged, in either mode. |
| `meter_per_call` | `WritProofs/Meters.lean` | Every entry a claimed first attempt of an enforced call adds has an amount at most `max_per_call`. |
| `reserved_per_call` | `WritProofs/Accounting.lean` | At every reachable state, every entry of an enforced call has an amount at most `max_per_call`, a partial capture included. |

**Overruns.**

| Result | File | Plain reading |
|---|---|---|
| `over_cap_only_by` | `WritProofs/Accounting.lean` | If an accepted step leaves usage at its time above the cap, then usage was already above it, or the step is an overrun naming the meter, a dispatch of a `log_only` call, a `ledger_sync` or a `session_start`. |
| `overrun_fails` | `WritProofs/Meters.lean` | An overrun verdict comes from a `result` or `reconcile` of a recorded call and raises the session's failure total and that call's tool counter by one each. |
| `overrun_commits_actual` | `WritProofs/Reports.lean` | An accepted `result` or `reconcile` that does not release and reports an actual cost `a` above the call's draw on a money meter of its action turns the call's single uncommitted entry on that meter into one committed entry whose amount plus excess is `a`: the amount is the reservation, at the reservation's time, and the excess is dated at the report. Pruning cannot drop it, because its excess is inside the window. |
| `overrun_verdict` | `WritProofs/Reports.lean` | Such a report is answered `overrun` naming the meter, and raises the session's failure total and the call's tool counter by one each. |
| `report_commits_actual` | `WritProofs/Reports.lean` | An accepted `result` or `reconcile` that does not release and reports no actual cost, or one at most the call's draw on a money meter of its action, decides nothing (no overrun on any meter) and turns the call's entry on that meter into one committed entry of exactly the reported cost (the reservation when none is reported) with no excess, or pruning drops it at once because the reservation's time is outside the window. |
| `report_commits_calls` | `WritProofs/Reports.lean` | On a calls meter of the call's action, such a report, whatever cost it reports, turns the call's single uncommitted entry (amount 1) into one committed entry of amount 1 with no excess and the reservation's time, or pruning drops it at once because that time is outside the window. |
| `no_claim_over_cap` | `WritProofs/Meters.lean` | While usage at the event time is above the cap, no first attempt of an enforced call on that meter is claimed, nor a retry whose own entries all left the window. |

**Accounting invariant**, for the session's own entries, which are all the entries of a session-scope meter.

| Result | File | Plain reading |
|---|---|---|
| `accounting_reachable` | `WritProofs/Accounting.lean` | At every reachable state (`Accounting`): each call has at most one own entry per meter; each own entry belongs to a call dispatched at least once whose action uses the meter; a call that holds its reservation (`Holds`: Dispatched, or Unknown and not reconciled) has exactly one own entry on each meter of its action, uncommitted, with no excess and amount equal to its draw; and every own entry of a call that no longer holds is committed. |
| `settle_commits` | `WritProofs/Accounting.lean` | A `result` or `reconcile` that does not release (no `no_effect`, outcome not `declined`) of a call that holds turns its single uncommitted entry on each meter into one committed entry with the same time, an amount no larger, and either the old excess or the same amount with its excess dated at the report; or pruning drops the entry at once because it is outside its window. |
| `committed_stays` | `WritProofs/Accounting.lean` | A committed own entry leaves its meter's list only at a `ledger_sync`, or when it is outside its window at the event time (both its reserved part and its excess). |
| `session_entries_own` | `WritProofs/Reports.lean` | At every reachable state, every entry of the session-scope meter list carries the session's own id. |
| `accounting_session` | `WritProofs/Reports.lean` | The accounting invariant for every entry of a session-scope meter `m`, with no own-id hypothesis: at every reachable state each entry of `m` carries the session's id and is the only entry of its call on `m`, that call was dispatched at least once and its action uses `m`, and the entry is uncommitted with no excess and the call's draw while the call holds its reservation, committed once it does not. |

**Assumes.**
- `p.WF`: carried by `meter_cap`, `meter_cap_retry`, `meter_cap_retry_of`, `meter_reuse`, `meter_per_call`, `reserved_per_call`, `over_cap_only_by`, `overrun_commits_actual`, `overrun_verdict`, `report_commits_actual`, `report_commits_calls`, `accounting_reachable`, `accounting_session`, `settle_commits` and `committed_stays`. Section 8's assumption. `session_entries_own` needs none.
- `Reachable`: `meter_cap_retry`, `meter_reuse`, `reserved_per_call`, `over_cap_only_by`, `overrun_fails`, `overrun_commits_actual`, `overrun_verdict`, `report_commits_actual`, `report_commits_calls`, `accounting_reachable`, `session_entries_own`, `accounting_session`, `settle_commits`, `committed_stays`. Section 8's assumption. The limit results hold for a trace from any state.
- `p.modeOf c.tool = .enforce`: `meter_room`, `meter_cap`, `meter_room_retry`, `meter_cap_retry`, `meter_cap_retry_of`, `meter_per_call`, `reserved_per_call` and `no_claim_over_cap`. Section 8's assumption. `meter_reuse`, `over_cap_only_by`, `overrun_fails`, the four report results and the accounting results hold in every mode.
- `p.mode = .enforce` (policy level): only `steps_per_turn`, as the spec says. The proposal and approval limits carry no policy-level mode; the proposal count includes only enforced actions.
- `c.status = .authorized` (a first attempt): `meter_room`, `meter_cap`, `meter_per_call`. Retries have their own results, as listed.
- `hfresh` in `no_claim_over_cap`: the spec's "first-attempt dispatch ... nor a retry whose reservation has left the window".
- In `settle_commits`, `overrun_commits_actual`, `overrun_verdict`, `report_commits_actual` and `report_commits_calls`, `no_effect` false and an outcome other than `declined`: the spec's "not released". The report results state nothing about a release, which reports no overrun (section 6, Meters).
- `spec.unit = .money cur` in `overrun_commits_actual`, `overrun_verdict` and `report_commits_actual`: section 6 commits the actual cost on money meters only. `spec.unit = .calls` in `report_commits_calls`: a calls meter commits its reservation whatever the report says.
- `spec.scope = .session` in `accounting_session`: the principal ledger also holds other sessions' entries, which have no accounting invariant.
- In `report_commits_actual`, the verdict `ok none` (no overrun on any meter) follows from the hypothesis on one money meter because every money meter of a call reserves the same amount, the call's cost.

**Not claimed.**
- Proposals of `log_only` actions are not counted by `proposals_per_*`, even under a policy-level `enforce` mode.
- An edit that makes a new request (generation g+1, verdict `pending`) is not counted by `approvals_per_*`; only new calls answered `needs_approval` are.
- Events after a `turn_end` and before the next accepted `turn_start` count in the turn that ended, because only `turn_start` resets the turn counters.
- `over_cap_only_by` lists a `ledger_sync` or a `session_start` as a cause without saying how the ledger it brings got above the cap: it was written elsewhere, and nothing ties a `session_start`'s or `ledger_sync`'s ledger to the store. Across sessions, theorem 9 covers claims; no statement bounds the stored ledger's usage between claims, or says it exceeds a cap only through an overrun or a `log_only` reservation.
- "committed in full" is stated for money meters by `overrun_commits_actual` (amount plus excess equals the reported `actual_cost`) and, for a report at or below the reservation, by `report_commits_actual` (exactly the reported cost, or the reservation when none is reported). The kernel commits a partial capture as reported: the clamp that commits at least the reservation for an untrusted executor is a binding duty (section 6, Meters), outside every statement. On a calls meter, `report_commits_calls` says the committed amount is exactly the reservation, 1.
- The accounting invariant covers this session's entries (`en.session = s.sessionId`). On a session-scope meter these are all the entries (`session_entries_own`), and `accounting_session` states the invariant for every entry of such a meter. The principal ledger's entries written by other sessions have no accounting invariant.
- "a committed entry stays until pruning drops it" has one more exit in Lean: a `ledger_sync` may drop a committed own entry, which `accepted_iff_ledgerSync` admits only when the stored ledger lacks it (another session pruned it). That such a pruning respected the window is theorem 9 (`multi_window`), for entries of other session ids.
- "every entry belongs to exactly one dispatched call" is stated as: each own entry names a call dispatched at least once, and no call has two entries on a meter.

## Theorem 9: Ledger

> 9. **Ledger.** Consider any interleaving of steps from several sessions of one principal, with distinct session ids, in which each committed step that changed the stored ledger (a `ledger_sync` never does; it only brings the state up to it) was taken on a state whose ledger equals the last committed ledger (what `session_start`, `ledger_sync` and the two-version compare-and-swap of section 7 provide; every claim changes the ledger). Principal meter caps and the principal kill hold across the whole interleaving, as they do for one session. Sequential chains of sessions are the special case of one live session at a time. The sessions may run different policies (a live policy and retired ones, or the policies of two gates during a rolling deploy) when every principal meter they share has the same kind, currency and window: each claim stays within its own policy's cap, and no session prunes an entry another still counts at the time of the pruning step or later. These cross-session claims assume the sessions share the trusted monotone clock of section 10 and the binding stamps each commit attempt, compare-and-swap retries included, from it, so commits are ordered by time. The host may also set or clear the tombstone out of band: no session claims on a stored ledger that carries it, and a session that has seen it never claims again, even after it is cleared.

The model. `interleave p d L S sched` runs a schedule of `(i, e)` pairs: session `i` takes event `e` from its current state, starting from `S i`; each step is recorded as a `Commit` with the state before it, the event, the verdict and the stored ledger before and after. A step other than `ledger_sync` and `session_start` that changes the ledger version writes the session's ledger to the store; every other step leaves the store as it was. Only session `i` changes when it steps. `interleaveP pol L S ops` is the same with session `i` under policy `pol i`, and with `Op.store b` among the operations: an out-of-band write of the stored tombstone (`storeLedger`, which bumps the version only when the tombstone changes; `storeLedger_eq` ties it to the kernel's `Ledger.setTombstone`). A `session_start` or `ledger_sync` may carry any ledger: nothing ties it to the store, and the discipline hypothesis is what makes a writing step read the stored ledger. `Op.event?` is the event of a step op (none for a store op), and `TimeOrdered ops` says the times of those events never decrease along the schedule.

| Result | File | Plain reading |
|---|---|---|
| `interleave_reachable` | `WritProofs/Interleave.lean` | Every commit of `interleave` with all sessions starting at `State.initial d` is taken on a reachable state, so the one-session theorems apply to each session. |
| `ledger_cap` | `WritProofs/Interleave.lean` | Under the discipline, a claim of an enforced call on a capped principal meter (first attempt or a retry whose entries left the window) found usage on the stored ledger it read, plus its draw, within the cap, and the stored ledger after its commit is within the cap at the event time (`claim_stored` says the claim wrote that ledger). |
| `ledger_kill` | `WritProofs/Interleave.lean` | Under the discipline, once a commit stores the tombstone, no later commit of any session is a claim. |
| `ledger_kill_event` | `WritProofs/Interleave.lean` | Under the discipline, after an accepted `kill` in a policy with `kill_sets_tombstone`, no later commit of any session is a claim. |
| `ledger_kill_stored` | `WritProofs/Interleave.lean` | Under the discipline, from sessions in any reachable states, if the stored ledger starts with the tombstone, no commit is a claim. |
| `storeLedger_eq` | `WritProofs/Interleave.lean` | `storeLedger` is the kernel's `Ledger.setTombstone`. |
| `interleave_eq` | `WritProofs/Interleave.lean` | `interleave p d L S sched` is `interleaveP` with every session under `p` and the schedule's pairs as step ops, no store op; `interleave_reachable`, `ledger_cap`, `ledger_kill`, `ledger_kill_event` and `ledger_kill_stored` are proved from the several-policy results through it. |
| `disciplined_eq` | `WritProofs/Interleave.lean` | `Disciplined p` is `DisciplinedP` with every session under `p`, so the one-policy discipline is the several-policy one. |
| `multi_reachable` | `WritProofs/Interleave.lean` | Every commit of session `i` in `interleaveP` is taken on a state reachable under `pol i` and digest `dig i`. |
| `multi_cap` | `WritProofs/Interleave.lean` | `ledger_cap` over several policies, against the claiming session's own policy's meter and cap. |
| `multi_kill` | `WritProofs/Interleave.lean` | Under the discipline, no commit taken while the stored ledger carries the tombstone, set by a `kill` or out of band, is a claim. |
| `multi_kill_event` | `WritProofs/Interleave.lean` | Under the discipline and with no out-of-band clear in the schedule, after an accepted `kill` under the killing session's `kill_sets_tombstone`, no later commit of any session is a claim. |
| `multi_window` | `WritProofs/Interleave.lean` | Under the discipline and `MeterAgree pol m`, a commit never drops from the stored ledger an entry on principal meter `m`, written under another session id, that `m`'s usage (under any session policy that defines `m` as a principal meter) still counts at a time `t` no earlier than the commit. |
| `multi_cleared` | `WritProofs/Interleave.lean` | Once a session's own ledger carried the tombstone at one of its commits, none of its later commits is a claim, whatever is stored later, out-of-band clears included. No discipline needed. |
| `claim_stored` | `WritProofs/Interleave.lean` | Under the discipline, a claim read the stored ledger, stored the ledger its step produced, at a higher version, and that stored ledger holds the call's uncommitted entry, with no excess and the call's draw, under the claiming session's id on each principal meter of its action. For a first attempt the entry is new: it is dated at the claim, and the stored ledger before had no entry of that session and call on the meter. |
| `multi_window_ordered` | `WritProofs/Interleave.lean` | `multi_window` for every later commit: when the schedule is `TimeOrdered`, a commit never drops from the stored ledger an entry on principal meter `m`, written under another session id, that `m`'s usage still counts at the time of that commit or of any later commit. |
| `multi_kill_after` | `WritProofs/Interleave.lean` | `multi_kill_event` with the no-clear hypothesis only on the ops after the kill: the schedule splits at the kill's op, the commits before the kill commit are those of the ops before it, and with no out-of-band clear after it no later commit of any session is a claim. Clears before the kill are allowed. |

**Assumes.**
- `Disciplined` / `DisciplinedP`: the spec's own hypothesis on committed steps (see Reading the statements). It is a duty of the binding, not proved of the TypeScript gate.
- `p.WF` (one policy) or `(pol x.session).WF` (the claiming session's policy) in `ledger_cap`, `multi_cap` and `claim_stored`: section 8's assumption. The kill and window results need no `WF`.
- `p.modeOf c.tool = .enforce` (the claiming session's policy) in `ledger_cap` and `multi_cap`: section 8's assumption.
- `hfresh` in `ledger_cap` and `multi_cap`: as in theorem 8; a retry inside the window reserves nothing.
- `spec.scope = .principal`: these results are about principal meters; session meters are theorem 8.
- `p.killSetsTombstone = true` in `ledger_kill_event` and `multi_kill_event`: section 6, "when the policy says so".
- `MeterAgree pol m` in `multi_window`: the spec's same-kind, same-currency, same-window condition. `multi_cap` does not need it.
- `¬ Op.store false ∈ ops` in `multi_kill_event`: the schedule has no out-of-band clear anywhere, before the kill as well as after it. `multi_kill_after` drops the part before the kill: `ops = opsPre ++ .step x.session x.event :: opsPost` with `pre.length` equal to the number of step ops in `opsPre` (so `x` is the kill op's commit), and `¬ Op.store false ∈ opsPost`.
- `TimeOrdered ops` in `multi_window_ordered`: section 10's trusted monotone server clock, shared by the sessions, so commit order matches time order. `multi_window` does not need it and covers only times no earlier than the pruning commit.
- `en.session ≠ x.pre.sessionId` and `x.event.time ≤ t` in `multi_window`: only entries of other session ids, counted at the time of the step or later.
- Distinct session ids are not a hypothesis of any result; sessions are told apart by their index `i`.

**Not claimed.**
- "Principal meter caps hold" is stated at each claim: the stored ledger before it had room for the draw, and the stored ledger after it is within the cap at the claim's time; `claim_stored` says that stored ledger is the claim's own and holds its entry. No statement says the stored ledger's usage exceeds a cap only through an overrun or a `log_only` reservation (the multi-session form of `over_cap_only_by`), and the accounting invariant (theorem 8) is not extended to other sessions' entries.
- Under clock skew the window protection holds only at the pruning commit's time or later (`multi_window`). A session whose clock runs ahead may prune an entry that a session behind it still counts, and that session's claim then finds room the window should not have: the witness `clockLog 1990` in `WritProofs/Interleave.lean` reaches 130 inside one session's window against a cap of 100. `multi_window_ordered` rules this out when the sessions share the trusted monotone clock (`TimeOrdered`), which the spec sentence assumes. Sharing that clock, and stamping each commit attempt, compare-and-swap retries included, from it, is a host duty (section 10), outside every statement.
- `multi_window` says nothing about entries carrying the pruning session's own id, including entries of another session that reused that id. Distinct ids (a binding duty, section 6) are what rule that out.
- "as they do for one session" for the other one-session theorems is by `interleave_reachable` and `multi_reachable`: each commit's state is reachable under its session's policy, so theorems 1 to 8 apply to it. The trace-based theorems (1, 2, 4) are stated for the session's own event list from `State.initial`; that a session's state in the interleaving equals `after` of its own events follows from the equations of `interleave`, not from a pinned statement.
- `multi_cap` bounds the number that `usageAt` computes over every stored entry named `m` under the claiming session's spec. Without `MeterAgree`, entries written under another policy with a different unit are summed into that number all the same.
- "a session that has seen it" is read as: the tombstone was on that session's own ledger at one of its commits. `multi_cleared` covers the session's commits after that one; the commit whose pre-state carries the tombstone is covered by `no_claim_tombstone` (theorem 7), so a reader composes the two. That composition needs the commit's verdict to be the verdict of `step` on its pre-state and event, which follows from the equations of `interleaveP`, not from a pinned statement.

## Theorem 10: Default deny

> 10. **Default deny.** Unknown and unexposed actions are never authorized and never claimed, whatever the policy-level or action-level mode.

| Result | File | Plain reading |
|---|---|---|
| `default_deny_claim` | `WritProofs/DefaultDeny.lean` | A claimed dispatch from a reachable state is of a recorded call whose action is defined and exposed. |
| `default_deny_propose` | `WritProofs/DefaultDeny.lean` | Every accepted `propose`, new or repeated, from a reachable state, of an undefined or unexposed tool is answered `denied`. |
| `default_deny_status` | `WritProofs/DefaultDeny.lean` | At every reachable state, a recorded call of an unexposed action is Denied. |
| `denyInv_reachable` | `WritProofs/DefaultDeny.lean` | At every reachable state, every recorded call has a defined action, and is Denied if that action is unexposed. |

**Assumes.** `Reachable`; no `p.WF` and no mode hypothesis, so they hold whatever the modes.

**Not claimed.** Nothing beyond the spec sentence: a call that is Denied at every reachable state is never Authorized, and an undefined tool never has a record.

## Theorem 11: Escalation

> 11. **Escalation.** Once the session failure total reaches its limit, or a tool's consecutive-failure counter reaches its limit under session scope, no proposal (new or repeated) has a non-denied disposition and no dispatch is claimed until an accepted `escalation_ack` from an eligible approver that echoes the escalation count current at the acknowledgment. Under tool scope, the same holds for that tool's proposals and dispatches.

| Result | File | Plain reading |
|---|---|---|
| `escalationInv_reachable` | `WritProofs/Escalation.lean` | At every reachable state: a session failure total at its limit has escalated the session; under session scope, a tool counter at its limit has escalated the session; under tool scope, a tool counter at its limit has blocked that tool. |
| `blocked_propose` | `WritProofs/Escalation.lean` | While the session is escalated or tool `t` blocked (`Blocked s t`), every accepted `propose` of enforced tool `t`, new or repeated, is answered `denied`. |
| `blocked_claim` | `WritProofs/Escalation.lean` | While `Blocked s c.tool`, no dispatch of an enforced call is claimed. |
| `unblock` | `WritProofs/Escalation.lean` | A step that lifts `Blocked s t` is an accepted `escalation_ack` that echoes the state's escalation count, from an approver attested with a principal other than `agent` and an escalation role (`EscalationEligible`; by default any approver role). |
| `approver_origin` | `WritProofs/Approvers.lean` | The approver map `EscalationEligible` reads holds only entries an accepted `session_start` or `approver_attest` carried (`ApproverOrigin`, see theorem 1). |
| `failed_fails` | `WritProofs/Escalation.lean` | An accepted `result` with outcome `failed`, or an accepted `outcome_unknown`, raises the session failure total and the call's tool counter by one each. |
| `overrun_fails` | `WritProofs/Meters.lean` | So does an overrun (theorem 8). |
| `failure_total_step` | `WritProofs/Reports.lean` | The session failure total rises by exactly one at a step that counts a failure (`CountsFailure`: an accepted failed `result`, an accepted `outcome_unknown`, or an accepted `result` or `reconcile` answered `overrun`; a report that is both failed and an overrun counts once), is reset to 0 by an accepted `escalation_ack` (`Acks`), and is unchanged by every other step, rejected or accepted. |
| `failure_tool_step` | `WritProofs/Reports.lean` | A step that counts a failure of call `k` raises the counter of `k`'s tool by exactly one; an accepted `result` of `k` with outcome `succeeded` and no overrun (`Succeeds`) resets that tool's counter to 0; an accepted `escalation_ack` resets every counter to 0; every other step leaves every counter unchanged, and no step changes the counter of another tool. |
| `escalations_step` | `WritProofs/Reports.lean` | A step that counts a failure raises the escalation count by one when the session is escalated or some tool blocked after it, and leaves it unchanged otherwise; every other step, an `escalation_ack` included, leaves it unchanged. |
| `WF.failureLimit_pos`, `WF.sessionFailureLimit_pos` | `WritProofs/WF.lean` | A checked policy has no failure limit of 0. |

**Assumes.**
- `p.WF` and `Reachable` in `escalationInv_reachable`: section 8's assumptions (a limit of 0 is a check error).
- `p.modeOf t = .enforce` in `blocked_propose` and `blocked_claim`: section 8's assumption.
- A trace from the initial state for `approver_origin`.
- `failure_total_step`, `failure_tool_step` and `escalations_step` carry no hypothesis: they hold for every step from every state.

**Not claimed.**
- The counting rules of section 6 are stated per step by `failure_total_step`, `failure_tool_step` and `escalations_step`: a `declined` result, a `reconcile` without an overrun and an Unknown made by `reset` or `session_end` are none of `CountsFailure`, `Succeeds` and `Acks`, so they change no counter. No statement over traces says that N failures without an acknowledgment escalate the session; such a statement would combine `failure_total_step` with `escalationInv_reachable`.
- `escalations_step` states the kernel's rule for the escalation count: one per counted failure that leaves anything blocked. A failure that newly blocks something while something else is already blocked, or blocks the session and a tool at once, adds one, as section 6's "the escalation count rises by one for each counted failure that leaves the session escalated or a tool blocked" says.

## Theorem 12: Rejection memory

> 12. **Rejection memory.** Once a `(tool, digest)` is rejected in a session (the digest as proposed, as current, or of the generation the reject echoed), until a `user_initiated` turn starts no call with that pair is newly authorized (by propose, approval or edit) and no first-attempt dispatch with that pair is claimed, whether the call was proposed before or after the rejection.

| Result | File | Plain reading |
|---|---|---|
| `reject_records` | `WritProofs/Rejection.lean` | An accepted `reject` puts the call's tool with its proposed digest, its current digest and the digest of the generation it echoed into the rejection memory. |
| `memory_persists` | `WritProofs/Rejection.lean` | A pair leaves the memory only at an accepted `turn_start` with `user_initiated` true. |
| `rejected_propose` | `WritProofs/Rejection.lean` | A `propose` of a new call of an enforced action whose pair is in the memory is answered `denied`. |
| `rejected_approve` | `WritProofs/Rejection.lean` | An accepted `approve`, in any mode, is of a call whose current pair is not in the memory, and an edit's new pair is not in it either. |
| `rejected_claim` | `WritProofs/Rejection.lean` | A claimed first attempt of an enforced call has a pair not in the memory, whenever the call was proposed. |
| `memory_origin` | `WritProofs/Rejection.lean` | After any trace from the initial state, every pair in the memory was recorded by an accepted `reject` of the trace from the record of the call it rejected: the call's tool with its proposed digest, its current digest or the digest of the generation the reject echoed; and that digest is one the events carried for a generation of the call (`GenerationDigest`). |
| `rejected_until_user_turn` | `WritProofs/Rejection.lean` | After an accepted `reject` of call `k` echoing generation `rid.generation`, with no accepted `turn_start` with `user_initiated` true after it, a `propose` of a new call of an enforced action with `k`'s tool and the digest the events carried for `k`'s generation 0, for the echoed generation, or for its last generation before the reject, is answered `denied`. |
| `call_origin` | `WritProofs/Origin.lean` | A call record's proposed digest is the digest of the `propose` that created it, its current digest is that of its last generation, and each generation's digest in the record is the one the `propose` or an accepted edit carried for that generation (`CallOrigin`, see theorem 1). |
| `generation_recorded` | `WritProofs/Origin.lean` | Conversely, a digest the events carried for generation `g` of call `k` (`GenerationDigest`) is entry `g` of `k`'s record, which has the tool the `propose` carried. |

How the definitions match the sentence: `GenerationDigest p d es k t g dg` says generation 0 of call `k` has the digest of the accepted `propose` that created `k` with tool `t` (`Proposed`: no record of `k` before it, and an action the policy defines), and generation `g + 1` has the new digest of an accepted `approve` of `k` whose edit echoed the request of generation `g`. The spec's "as proposed, as current, or of the generation the reject echoed" is generation 0, the last generation before the reject, and `rid.generation`.

**Assumes.**
- `p.modeOf t = .enforce` in `rejected_propose` and `rejected_claim`: section 8's assumption.
- `s.calls[k]? = none` in `rejected_propose`: a new call. A repeated `propose` returns the call's current disposition and authorizes nothing new (section 6).
- `c.status = .authorized` in `rejected_claim`: a first attempt, as the spec says.
- `rejected_propose`, `rejected_approve`, `rejected_claim`, `reject_records` and `memory_persists` assume no `Reachable` and no `p.WF`: they hold from any state. `memory_origin`, `rejected_until_user_turn`, `call_origin` and `generation_recorded` assume a trace from the initial state, and no `p.WF`.
- In `rejected_until_user_turn`: `p.modeOf t = .enforce` (section 8's assumption); a new call id, read as no record of `k'` before the `propose`, as in `rejected_propose`; the generation is 0, the echoed one, or the last one the events carried before the reject (every generation they carried is at most it); and no accepted `turn_start` with `user_initiated` true among the events after the reject, which is the spec's "until".

**Not claimed.**
- "until a `user_initiated` turn starts" is stated over a trace only for a new `propose` (`rejected_until_user_turn`). For approvals, edits and first-attempt claims the reader composes `rejected_approve` and `rejected_claim`, which read the memory at that state, with `reject_records` and `memory_persists`. No statement says such a turn does clear the memory, which the theorem does not need.

## Theorem 13: Expansion soundness

> 13. **Expansion soundness.** If `writ check` accepts a layer-2 policy, then `check (expand p)` succeeds; `expand` is total; it is monotone (comparing resolved labels, missing labels as top, and explicit requirements excluding `permission` and `meter`); it is never weaker than any matching rule, explicit requirement, or `extends` parent. Lattice laws for each field's join are proved as lemmas.

| Result | File | Plain reading |
|---|---|---|
| `expand_check` | `WritProofs/Expand.lean` | If `Policy2.check` accepts a leaf policy and the files it extends, the expanded policy passes `Policy.check`. |
| `expand_actions` | `WritProofs/Expand.lean` | The expanded policy has the leaf's policy-level fields, and defines an action exactly for each name that the leaf or a file it extends writes under `actions`. |
| `expand_explicit` | `WritProofs/Expand.lean` | For every entry that the leaf or a file it extends writes for action `n`, the expanded policy defines `n`, at least as strict as that entry (`Requirements.le`). |
| `expand_rule` | `WritProofs/Expand.lean` | For a rule of any file, and an entry of any file for action `n` that the rule matches under that file's labels (a missing or unknown label read as its dimension's last value): the expanded policy defines `n`, at least as strict as everything the rule sets (`Require.le`). |
| `expand_rule_resolved` | `WritProofs/Expand.lean` | The same for a rule that matches the labels `expand` resolves for `n` (`labelsOf`), with no hypothesis on the policy. |
| `expand_rule_checked` | `WritProofs/Expand.lean` | `expand_rule` for a leaf and files whose layer-2 problems (`Policy2.problems`, the first part of `Policy2.check`) are none, in place of its duplicate-value hypothesis. |
| `expand_mono` | `WritProofs/Expand.lean` | For two actions `n` and `m` of one layer-2 policy: if on every declared dimension each file's label for `n` is at or below some file's label for `m` (missing or unknown labels read as the last value), and `n`'s explicit requirements, joined across the files that name it (`explicitReq`), are below `m`'s, then `n`'s expansion is below `m`'s. |
| `expand_mono_resolved` | `WritProofs/Expand.lean` | The same, comparing the labels `expand` resolves (`labelsOf`) instead of each file's, with no hypothesis on the policy. |
| `expand_mono_checked` | `WritProofs/Expand.lean` | `expand_mono` for a leaf and files whose layer-2 problems are none, in place of its duplicate-value hypothesis. |
| `expand_parent` | `WritProofs/Expand.lean` | For any file `q` among the leaf's files (one the leaf extends, or the leaf itself), expanded together with any files `qs` among them (for example the files `q` extends): every action `q`'s expansion defines, the leaf's expansion defines too, at least as strict. With `q` the leaf and `qs` empty, extending files never weakens the leaf's own expansion. |
| `expand_parent_checked` | `WritProofs/Expand.lean` | `expand_parent` for a leaf and files whose layer-2 problems are none, in place of both its hypotheses. |

How the definitions match the sentence. `expand parents p` expands the leaf `p` with `parents`, every file it extends, already resolved and flattened. Each action is built in four steps: the join (`Requirements.joinStrict`) of every file's entry for it (`explicitReq` over `actionEntries parents p n`); then every rule of every file whose `when` holds for the resolved labels (`Rule.matches`), joined in with `Requirements.joinReq`; then `grantable` dropped when the consent needs more than one approval; then, for an action without `grantable`, its escalators made non-grantable and those with no consent groups that were grantable dropped. The last two steps only raise strictness, and the proofs carry them. `labelRank d labels dim` is where `labels` puts `dim` in order `d`, a missing or unknown value taking the last position, as section 5 says ("an action missing a label on a declared dimension gets that dimension's strictest value"). `labelsOf parents p n` is the labels the rules see: per declared dimension (`mergedDims`, each dimension's first declaration, leaf first), the highest `labelRank` over every file that names `n`, so a file that extends another can never resolve an action lower than any file does. "Monotone (comparing resolved labels, missing labels as top, and explicit requirements excluding `permission` and `meter`)" is `expand_mono`: labels compared per file with a missing label at the top, explicit requirements by `Requirements.le`, which leaves out `permission` and `meters`. "Never weaker than any matching rule, explicit requirement, or `extends` parent" is `expand_rule`, `expand_explicit` and `expand_parent`. A parent's rules reach an action that only the leaf names through `expand_rule` (or `expand_rule_checked`), since every file's rules apply to every action; `expand_parent` covers the actions the parent's own expansion defines. A three-file chain witness (a leaf extending `team`, which extends `org`, with `q` = `team` and `qs` = [`org`]) checks `expand_parent` on a flattened chain. `expand` is total because it is a Lean function with no partiality: it returns a policy for every input, which no theorem needs to state; `expand_actions` says which actions that policy defines.

The non-vacuity witnesses are `#guard` lines in `WritProofs/Expand.lean`, which `lake build` checks; they have no name, so they are not pinned. On an organization baseline and a team policy that extends it and tries to loosen `files.write` (ten grant uses over the baseline's five, and the label `read` over the baseline's `write`), the layer-2 check passes, each theorem's hypotheses hold, and each conclusion relates two different requirements strictly: the expanded `files.write` keeps five uses and the baseline's per-call consent, and gains the team's guard. Two more policies show the hypotheses below are needed, and that `Policy2.problems` reports each.

**Assumes.**
- `Policy2.check parents leaf = []` in `expand_check`: section 8's "if `writ check` accepts". That `writ check` and `writ expand` run `Policy2.check` on a layer-2 document, and that `writ expand` prints a policy only when it reports nothing, is code in `WritCli/Expand.lean`, not a theorem.
- In `expand_rule`, `expand_mono` and `expand_parent`: every declared label order lists no value twice (`d.2.order.Nodup` for each `d` of `mergedDims`). The JSON codec refuses a duplicate value (`Writ/Codec/Layer2.lean`), and `Policy2.problems` reports one in any file (`duplicate_label_value`), so the `_checked` forms assume `Policy2.problems parents leaf = []` instead. It is needed: `expand` writes the resolved label as a value and reads its position back as the value's first position, so with the order `["low", "high", "low"]` an unlabeled action resolves to `low`, below `high`. A `">=high"` rule then matches an action one file labels `high` but not an unlabeled one, though the unlabeled one is higher on every file's labels (the `dupOrder` witness). For `expand_parent` the same happens across files: a parent with that order labels an action `high` and its `">=high"` rule hides it, and a leaf that names the action without a label, declaring no dimension, makes it resolve to `low`, so the leaf's expansion is weaker than the parent's (the `dupParent` and `dupLeaf` witness). `expand_rule_resolved` and `expand_mono_resolved` compare the labels `expand` resolves and need nothing.
- In `expand_parent`: no label dimension is declared with two different orders across the leaf and its files, the `conflicting_dimension` problem of `Policy2.problems`. It is needed: when the leaf declares `risk` as `["high", "mid", "low"]` over a parent's `["low", "mid", "high"]`, the parent's `">=mid"` rule stops matching an action the parent labels `high` (the `ascending` and `descending` witness). `expand_parent_checked` assumes `Policy2.problems parents leaf = []` instead, which implies both this and the duplicate-free orders, so a policy that passes the layer-2 check needs no side condition for any clause: `expand_check`, `expand_explicit`, `expand_rule_checked`, `expand_mono_checked` and `expand_parent_checked` assume only what the check reports.
- `expand_actions`, `expand_explicit`, `expand_rule_resolved` and `expand_mono_resolved` carry no hypothesis.
- In `expand_rule_checked`, `expand_mono_checked` and `expand_parent_checked`: `Policy2.problems parents leaf = []`, which `Policy2.check parents leaf = []` implies; the policies are the files' (`leaf.policy` and `parents.map (·.policy)`).

**Not claimed.**
- `expand_check` holds by construction of the layer-2 check: `Policy2.check` reports the layer-2 problems and then runs `Policy.check` on the expanded policy, so the theorem unfolds that definition. It says nothing about which layer-2 policies the check accepts.
- Totality is not stated as a theorem; it is a property of every Lean function without `partial`.
- "At least as strict" is `Requirements.le` and `Require.le`, orders on the policy's syntax. No statement connects them to the kernel: none says that an expanded action admits fewer calls than a weaker one (see the lattice laws' Not claimed for `Consent.le`).
- `permission`, `meters`, `review` and `messages` are outside the comparison. The expanded action's `permission` and `meters` are the first that a file sets; files that set different ones are a `conflicting_field` problem, which no statement reads.
- Monotonicity compares two actions of one layer-2 policy, under the same rules, dimensions and files. Adding files is `expand_parent`; changing a rule or a dimension's order is covered by no statement.
- "Never weaker than a parent" is about the parent's rules and per-action requirements. Policy-level fields come from the leaf (`expand_actions`); a parent that writes one is a `parent_policy_field` problem. The leaf's policy-level settings can still loosen what those requirements do at runtime: its `approver_roles` and `escalation_roles` decide who may approve, and its meters, caps and limits, TTL limits included, are its own. A policy-level `mode: log_only` would shadow every action; `Policy2.problems` reports it for a leaf that extends at least one file (`extends_log_only`), and no statement is about any of these settings.
- `expand_parent` compares the leaf's expansion with a parent's own expansion, in which a parent's rule or label on a dimension that the parent and the files it extends do not declare never takes effect. That the leaf cannot declare such a dimension in an order that turns the parent's rule off is a check (`Policy2.problems` checks each extended file's labels and rules against the dimensions of its own `extends` closure), not a statement.
- `parents` is a list of resolved policies. Resolving `extends` paths, cycles and the depth limit is code in `WritCli`, as are `writ check` and `writ expand` themselves.

How the orders match section 5. Every order `le a b` reads "`b` is at least as strict as `a`" and every join is the least strict value at least as strict as both arguments. `Consent.le c d`: every group of `c` is implied by a group of `d`. A group is implied by a group that is `distinct` when it is, and in which each of its clauses is implied by some clause; when the weaker group is `distinct`, which needs a different principal for every slot, its clauses must be implied by pairwise different clauses of the stricter group (`Clause.Matches`, an injective matching), so `distinct` on two clauses is stricter than on one. A clause is implied by a clause with a k at least as large, a subset of its roles (no `roles` meaning every approver role), and `human_only` and `exclude_requester` true where it has them. The consent join is the kernel's `Consent.join`: the union of groups, equal groups kept once. `GrantLe`: an absent `grantable` is the strictest; otherwise `turn` is stricter than `session`, smaller `max_uses` and `max_duration_ms` are stricter (no `max_duration_ms` is the least strict), and `any_args` and `allow_any_args_metered` false are stricter; the join is the field-wise meet. A rule's `grantable` is a `GrantCap`: `forbid` (JSON null) removes `grantable`, a cap meets it with each limit the cap sets, and neither ever adds one (`GrantCap.apply`, `GrantCap.le`). `BoolLe`: false is stricter (`exposed`, `idempotent`, `retry_after_unknown`), joined by `&&`. `ModeLe`: `log_only`, then an action without a mode (it takes the policy's mode, whichever that is), then `enforce`. `ListLe`: inclusion of members (`guards`, `flags`), joined by union, sorted and deduplicated. Rules set only those fields; five more are joined only across the files that name an action, a file that does not write one taking the layer-1 default. `CostLe`: no `consent_if_cost_over` is the strictest (consent is always asked), a lower threshold in the same currency is stricter, thresholds in different currencies are unordered; the join is the smaller amount in a shared currency and absent otherwise. `EscLe`: escalators only raise strictness, so every reason must add at least as much consent (`escAt`, all of a list's escalators for one reason joined, nothing and grantable when there are none) and be grantable only where the weaker is; the join (`escJoin`) is the union by reason, a shared reason getting both consents and `grantable` only if both have it. `max_attempts`: fewer is stricter, joined by `min`. `approval_ttl_ms`, `authorized_ttl_ms` (`DurLe`, a shorter TTL stricter): the join (`durMeet`) is the min over the TTLs files write; a file that writes none expresses no opinion, and the action then defers to the leaf's policy-level limit, which the leaf owns. `Requirements.le` compares all of these fields, not `permission` and `meters` (which files must agree on, as on `review` and `messages`, which `Requirements` does not hold); `Requirements.joinStrict a b` joins them and keeps `a`'s `permission` and `meters`; `Requirements.joinReq a r` joins a rule's `require` `r` in, a field the rule does not set leaving `a`'s as it is, and `Require.le r b` says `b` is at least as strict as everything `r` sets. Dropping `grantable` when a join makes consent need more than one approval is part of `expand`, not of these joins.

### Lattice laws

Each join is commutative, associative and idempotent, is at least as strict as each argument, and is the least such (`join a b ⊑ c` when `a ⊑ c` and `b ⊑ c`). The docstring of each law says whether it is an equality or holds up to the order's equivalence (`⊑` both ways). The consent join keeps the groups and not their order, so its laws, and the `Requirements` laws built on it, hold up to equivalence. The `guards` and `flags` joins return a canonical list (sorted, deduplicated), so their commutativity and associativity are equalities, and idempotence is an equality on that canonical form (joining a join's result with itself gives that result). The `grantable`, Bool and mode joins satisfy all three as equalities, as do the `max_attempts` (`min`) and TTL (`durMeet`) joins. The `consent_if_cost_over` and escalator joins hold up to equivalence.

| Field | Results | File |
|---|---|---|
| `consent` | `consent_le_refl`, `consent_le_trans`, `consent_none_le` (no groups is the bottom), `consent_mem_join`, `consent_join_nodup` (equal groups once), `consent_le_join_left`, `consent_le_join_right`, `consent_join_le`, `consent_join_comm`, `consent_join_assoc`, `consent_join_idem` | `WritProofs/Join.lean` |
| `grantable` | `grant_le_refl`, `grant_le_trans`, `grant_le_join_left`, `grant_le_join_right`, `grant_join_le`, `grant_join_comm`, `grant_join_assoc`, `grant_join_idem`; a rule's cap: `grant_le_apply` (never looser), `cap_le_apply` (within the cap), `cap_apply_le` (the least such), `cap_le_trans` | `WritProofs/Join.lean` |
| `exposed`, `idempotent`, `retry_after_unknown` | `bool_le_refl`, `bool_le_trans`, `bool_le_join_left`, `bool_le_join_right`, `bool_join_le`, `bool_join_comm`, `bool_join_assoc`, `bool_join_idem` | `WritProofs/Join.lean` |
| `mode` | `mode_le_refl`, `mode_le_trans`, `mode_le_join_left`, `mode_le_join_right`, `mode_join_le`, `mode_join_comm`, `mode_join_assoc`, `mode_join_idem` | `WritProofs/Join.lean` |
| `guards`, `flags` | `list_le_refl`, `list_le_trans`, `guard_le_join_left`, `guard_le_join_right`, `guard_join_le`, `guard_join_nodup`, `guard_join_comm`, `guard_join_assoc`, `guard_join_idem`, and the same for `flag_` | `WritProofs/Join.lean` |
| `consent_if_cost_over` | `cost_le_refl`, `cost_le_trans`, `cost_le_join_left`, `cost_le_join_right`, `cost_join_le`, `cost_join_comm`, `cost_join_assoc`, `cost_join_idem` | `WritProofs/Join.lean` |
| `escalate` | `escLe_iff` (the order read over every reason), `esc_le_refl`, `esc_le_trans`, `esc_le_join_left`, `esc_le_join_right`, `esc_join_le`, `esc_join_comm`, `esc_join_assoc`, `esc_join_idem` | `WritProofs/Join.lean` |
| `max_attempts` | `attempts_le_join_left`, `attempts_le_join_right`, `attempts_join_le`, `attempts_join_comm`, `attempts_join_assoc`, `attempts_join_idem` | `WritProofs/Join.lean` |
| `approval_ttl_ms`, `authorized_ttl_ms` | `ttl_le_refl`, `ttl_le_trans`, `ttl_le_join_left`, `ttl_le_join_right`, `ttl_join_le`, `ttl_join_comm`, `ttl_join_assoc`, `ttl_join_idem` | `WritProofs/Join.lean` |
| Requirements | `req_le_refl`, `req_le_trans`, `req_le_joinStrict_left`, `req_le_joinStrict_right`, `joinStrict_le`, `joinStrict_comm`, `joinStrict_assoc`, `joinStrict_idem`, `joinStrict_mono` | `WritProofs/Join.lean` |
| A rule's `require` | `req_le_joinReq` (never weaker than the action), `require_le_joinReq` (never weaker than the rule), `joinReq_le` (the least such), `require_le_trans`, `joinReq_mono`, `joinReq_swap` (rules apply in any order), `joinReq_idem` | `WritProofs/Join.lean` |

The `flag_` results are `flag_le_join_left`, `flag_le_join_right`, `flag_join_le`, `flag_join_nodup`, `flag_join_comm`, `flag_join_assoc` and `flag_join_idem`.

**Assumes.** Nothing: every law holds for all values.

**Not claimed.** No law here is about `expand` or the layer-2 check (the results above are), and none is about the layer-2 JSON. The orders are syntactic. `Consent.le` is meant to be sufficient for the kernel's consent semantics: approvals that satisfy the stricter consent satisfy the weaker, since a principal eligible for a clause is eligible for every clause it implies, and the injective matching turns a distinct assignment for the stricter group into one for the weaker. No Lean result states this: nothing connects `Consent.le` to `State.satisfied`. The order is also not complete: a consent can be at least as strict in that sense without being related. For example, the `distinct` group of `{ quorum: 1, roles: ["a"] }` and `{ quorum: 1, roles: ["b"] }` always brings two different principals holding `a` or `b`, so it implies `{ quorum: 2, roles: ["a", "b"] }`, but no clause of it has a quorum of 2, so `Consent.le` does not relate the two. A clause with an empty role set, which nobody can satisfy, is likewise not above everything (it is a check error).

## Supporting results

> Supporting results, also v0.1:
> - **Characterization lemmas**: for every event kind, `accepted ↔` an explicit condition. Together with the witness traces, these rule out a kernel that is safe by refusing everything.
> - **Witness traces**: for each disposition and reason code, a concrete trace reaching it under a witness policy, proved by `decide +kernel`.
> - **Frame lemma**: a rejected event leaves the state unchanged.
> - **Policy check soundness for degenerate limits**: `writ check` refuses zero windows, zero failure limits, unexposed actions whose own mode is `log_only` and mixed-currency money meters; the aim is that no theorem is vacuous or false for a checked policy.
> - **Origin independence**: for each step, the verdict and state do not depend on `origin`.
> - **Monotone time and seq** are enforced by the kernel.
> - The well-formedness invariant `Inv` (call status consistent with records, reservations match calls, tallies duplicate-free, epochs bounded, no calls before `session_start`) holds on every reachable state.

| Result | File | Plain reading |
|---|---|---|
| `accepted_iff_*` (22: `sessionStart`, `sessionEnd`, `turnStart`, `turnEnd`, `stepStart`, `propose`, `approve`, `reject`, `approvalExpire`, `grantCreate`, `grantRevoke`, `approverAttest`, `permissionAdd`, `permissionRevoke`, `result`, `outcomeUnknown`, `reconcile`, `cancel`, `escalationAck`, `ledgerSync`, `reset`, `kill`) | `WritProofs/Accept.lean` | For each event kind but `dispatch`, from any state: accepted exactly when the envelope checks pass (`EnvelopeOk`) and the kind's own condition holds. |
| `dispatch_accepted_iff`, `dispatch_claimed_iff` | `WritProofs/Dispatch.lean` | A `dispatch` is accepted exactly when the envelope passes, the call is recorded and fits the protocol (`ProtocolOk`), and, for an enforced call, either re-evaluation passes (`AuthOk`, `ReadyOk`) or the call is Authorized and `AuthOk` fails (it ends `DeniedAtDispatch`); it is claimed exactly when the envelope, protocol and, for an enforced call, both checks pass. |
| `envelope_iff` | `WritProofs/Envelope.lean` | `EnvelopeOk` is exactly the kernel's envelope check passing. |
| `claim_post` | `WritProofs/Dispatch.lean` | The state after a claim is the kernel's `claim` result with the event's seq and time and the next version. |
| witness `example`s | `WritProofs/Witness.lean` | For the witness policy `wp`, which is checked (`example : wp.WF`), and variants of it with other limits, a list of traces whose last verdict is each given verdict, and a list of traces that leave a call in each given status, each checked by `decide +kernel`; then a proof by cases that every `Reason`, every `Decision`, every `Shadow` and every `CallStatus` constructor appears in those lists. |
| `frame` | `WritProofs/Basic.lean` | From any state, a step whose verdict is not accepted leaves the state unchanged. |
| `Policy.WF.facts` | `WritProofs/WF.lean` | A checked policy has (`WFacts`): `max_attempts` at least 1, duplicate-free action meters, every action meter defined, no window of 0, `max_per_call` only on money meters, no failure limit of 0 (consecutive or per session), no unexposed action whose own mode is `log_only`, and one currency across each action's money meters. |
| `WF.maxAttempts_pos`, `WF.window_pos`, `WF.meters_nodup`, `WF.perCall_money` | `WritProofs/WF.lean` | Single fields of `WFacts`, used by the theorems above. |
| `origin_independent` | `WritProofs/Support.lean` | A step's state and verdict are the same whatever the event's `origin`. |
| `accepted_seq_time` | `WritProofs/Support.lean` | An accepted event has a `seq` above and a `time` no earlier than the state's, and the state records both. |
| `trace_seq_time` | `WritProofs/Support.lean` | Along any trace from any state, the accepted events have strictly increasing `seq` and nondecreasing `time`. |
| `wellFormed_reachable` | `WritProofs/Support.lean` | At every reachable state of a checked policy (`WellFormed`): no calls before `session_start`, call epochs at most the session's, duplicate-free tally principals, an Awaiting call with no grant and no attempt, an Authorized call with no attempt and an authorization time, a Dispatched or Unknown call with attempts from 1 to `max_attempts` and an authorization time, the accounting invariant (`Accounting`) and the grant counters (`GrantInv`). |
| `profile_unknown_final` | `WritProofs/Profile.lean` | Under a policy with no `mcp-tool-approval` profile error (`errors p = []`, which holds in particular when `problems p = []`), from any state, a `dispatch` of a call whose status is Unknown is not accepted: SEP-2848's "outcome-unknown is final" (`docs/formats.md`, MCP SEP-2848 profile). It follows from `dispatch_accepted_iff`: an accepted retry needs `retry_after_unknown` on the call's action, and the profile reports every action that sets it. |

The witness traces are `example`s, which have no name, so `scripts/print-statements.sh` does not print them and `WritProofs/Axioms.lean` does not pin them; `lake build` checks them. Read their statements in `WritProofs/Witness.lean`: each `example` line before `:= by`.

**Assumes.**
- `p.WF` and `Reachable` in `wellFormed_reachable`: section 8's assumptions.
- The characterization lemmas, the frame lemma, origin independence and the seq and time results hold from any state, for any policy.
- `profile_unknown_final` holds from any state, for any policy with no profile error; it needs neither `p.WF` nor a mode hypothesis. Its hypothesis reads `Writ.Profile.McpToolApproval.errors`, a definition outside the kernel.

**Not claimed.**
- The characterization lemmas characterize acceptance, not the decision. `accepted_iff_propose` says when a `propose` is accepted, not when it is `allowed` rather than `denied`, and nothing characterizes when a `result` or `reconcile` decides `overrun`. So by themselves they rule out a kernel that rejects everything, but not one that accepts every `propose` and denies it. The witness traces (`WritProofs/Witness.lean`) reach every decision, including `allowed`, `allowed_by_grant` and `dispatch_claimed`, and every call status under the witness policy or a variant of it, which is what rules out a kernel that refuses everything; they show nothing for another policy, and no statement says a policy other than the witness policy ever allows a call.
- That each characterization's condition is the one section 6 describes is for the reviewer to check against section 6, rule by rule; no statement relates them.
- The witness traces reach each verdict and status under the witness policy and its variants only, not under every policy.
- "the aim is that no theorem is vacuous or false for a checked policy" is an aim, not a Lean statement. `WFacts` lists what the check guarantees; it does not say that the hypotheses of every theorem can be met.
- `WFacts` refuses an unexposed action whose own `mode` field is `log_only`, as the spec sentence says; such an action with no mode of its own under a policy-level `log_only` is not refused. (`modeOf` treats every unexposed action as `enforce`, and theorem 10 holds in every mode.)
- That `writ check` runs `Policy.check`, so that `writ check p = ok` gives `p.WF`, is code in `WritCli/Check.lean`, not a theorem.
- Origin independence is stated for one step; for a whole run it follows by induction, which no pinned statement does.
- The well-formedness invariant is stated over reachable states of a checked policy, as the spec sentence says, not as preservation from any state that satisfies it.
- `profile_unknown_final` is about the kernel's acceptance only. That a server built on Writ never re-invokes a tool whose call is Unknown also needs the host to run tools only on `dispatch_claimed` (section 8's assumption), and that the profile's strings and envelopes say what SEP-2848 and SEP-2643 mean is checked by the guards in `WritTests/Profile.lean` against section 6's table, not by a theorem.

## Other pinned results

These are pinned too and appear in the tables above, or are steps toward them:

| Result | File | Plain reading |
|---|---|---|
| `claimed_dispatch` | `WritProofs/Basic.lean` | From a reachable state, only a `dispatch` can be claimed. |
| `no_claimed_decision` | `WritProofs/Basic.lean` | No call record at a reachable state carries the decision `dispatch_claimed`. |
| `calls_tool` | `WritProofs/Calls.lean` | A step keeps every call record and its tool. |
| `eligibleFor_sound` | `WritProofs/ConsentMeaning.lean` | The kernel's eligibility check passing for an attested approver gives `EligibleFor`. |
| `satisfied_sound` | `WritProofs/ConsentMeaning.lean` | The kernel's quorum check passing on an attested tally gives `ConsentMet`. |
| `consentInv_reachable` | `WritProofs/Consent.lean` | At every reachable state (`ConsentInv`): tally entries attested, attested approvers and the requester never changed by a step, an enforced active call without a grant has a consent the kernel's quorum check accepts and one with a grant has `GrantFacts`, an Awaiting call holds no grant, grants have attested approvers, nothing recorded before `session_start`. |
| `approvalInv` | `WritProofs/Approvals.lean` | After any trace from the initial state, every tally entry is `ApprovedBy`, and every call's `requestedAt` is no later than the state's last time. |
| `usageAt_eq` | `WritProofs/Usage.lean` | `usageAt` is the kernel's `Meter.usage`. |

## Review

An independent reviewer who read only the spec (`docs/design.md` and `docs/formats.md`), this page, the printed statements and the `WritProofs` definitions they use, the core data types, the declarations and definitions of `WritProofs/Witness.lean` and the definition of `Policy.WF`, never a proof or the kernel, checked section 8 against the Lean statements on 2026-10-20 and found 19 gaps: 4 high, 9 medium and 6 low; 7 missing statements, 7 weaker statements and 5 spec sentences that did not say what is proved; no vacuous hypothesis and no wrong quantifier. Each line gives the clause, the kind and severity, the resolution and the commit. A changed spec sentence is marked as such.

- **F1.** Theorem 8, an overrun "committed in full" and counted as a failure: the reported actual cost was in no conclusion (missing, high). Proved `overrun_commits_actual`, `overrun_verdict` and `report_commits_actual` (c8adfce), and `report_commits_calls` (2819e00).
- **F2.** Theorems 1 (b) and 2, a grant's limits, window, scope and digest: read from a record no statement tied to its `grant_create` (missing, high). Proved `grant_origin` (ae39841).
- **F3.** Theorem 1 (b), "every escalator that fired at propose is grantable": read from a call record field no statement tied to the `propose` (missing, high). Proved `call_origin`, and `consent_claim_fired`, which states (b) over the `propose` event's escalators (ae39841).
- **F4.** Theorem 12, the rejected digests: the memory's digests were not tied to the proposed, current or echoed digests (missing, high). Proved `call_origin`, `generation_recorded`, `memory_origin` and `rejected_until_user_turn` (ae39841).
- **F5.** Theorems 1, 3 and 11, attested approvers and the requester: not tied to `session_start` or `approver_attest` (missing, medium). Proved `approver_origin` and `requester_origin` (7642855).
- **F6.** Theorem 11, the failure counters and the escalation count: not shown to count failures (weaker, medium). Proved `failure_total_step`, `failure_tool_step` and `escalations_step` (05adfa1); section 6 now says the escalation count rises by one for each counted failure that leaves the session escalated or a tool blocked (fef2ef4), and no longer keeps the older sentence that counted each newly blocked tool or session (spec wording, confirmed by the owner's delegation on 2026-10-22). No statement over traces says N failures escalate; disclosed under theorem 11.
- **F7.** Theorem 9, "every claim changes the ledger": no statement put a claim's entry into the store (missing, medium). Proved `claim_stored` (4b95a15).
- **F8.** Theorem 9, pruning protected only "at the time of the pruning step or later", open under clock skew (spec, medium). Proved `multi_window_ordered` under `TimeOrdered`, with the skew witness `clockLog` (4b95a15); theorem 9 now says its cross-session claims assume the sessions share the trusted monotone clock of section 10 (4b95a15) and that the binding stamps each commit attempt, compare-and-swap retries included, from it, and section 6 (Meters) says an entry dated after a session's last event was written meanwhile by another session instead of by one whose clock runs ahead (fef2ef4, e2898a6; spec wording, confirmed by the owner's delegation on 2026-10-22).
- **F9.** Theorems 1 (a) and 6, the TTLs: measured from record times no statement tied to the request or the authorization (weaker, medium). Proved `call_times`, `approve_fresh_event` and `claim_authorized_ttl_event` (7642855).
- **F10.** Theorem 9, the kill across sessions: `multi_kill_event` excluded an out-of-band clear anywhere in the schedule (weaker, medium). Proved `multi_kill_after`, which excludes only a clear after the kill (4b95a15).
- **F11.** Theorem 2, "a use returned by a call that ended without dispatch can be reused" (missing, medium). Proved `grant_use_returned` and `grant_released_all` (6af4097). Not claimed, and disclosed under theorem 2: that a later proposal is answered `allowed_by_grant`, which also needs the grant valid, a matching tool and digest and an eligible approver.
- **F12.** Theorem 8, causes of usage above the cap beyond the spec's list, and no cross-session form (weaker, medium). Theorem 8 and section 6 (Meters) now list a `ledger_sync` or `session_start` that brings in a principal ledger above the cap, as `over_cap_only_by` does (fef2ef4; spec wording, confirmed by the owner's delegation on 2026-10-22). Not claimed, and disclosed under theorems 8 and 9: that the stored ledger exceeds a cap only through an overrun or a `log_only` reservation.
- **F13.** Supporting results, the characterization lemmas "rule out a kernel that is safe by refusing everything": they constrain acceptance, not the decision (weaker, medium). The sentence now credits the characterization lemmas together with the witness traces (fef2ef4), and so does the goal in section 2 (e2898a6) (spec wording, confirmed by the owner's delegation on 2026-10-22); that the witness traces cover only the witness policy and its variants is disclosed under Supporting results.
- **F14.** Section 6 and theorem 8, a failed result that also overruns: one failure or two was not said (spec, low). Section 6 says such a report counts once (05adfa1; spec wording, confirmed by the owner's delegation on 2026-10-22), as `failure_total_step` states.
- **F15.** Section 6 (Dispatch), the rejection check: read as applying to retries, which theorem 12 and the kernel exempt (spec, low). Section 6 now says first attempts only, a retry of an Unknown call not blocked (fef2ef4; spec wording, confirmed by the owner's delegation on 2026-10-22), as `AuthOk` and `rejected_claim` state.
- **F16.** Theorem 1 (a), "reviewed digest and cost equal to the dispatched ones": an edit counts for the digest it set, not the one it reviewed (spec, low). The sentence now says "for an approver's edit, the digest and cost it set" (fef2ef4), and so does section 6's "Every counted approval therefore reviewed exactly the digest and cost that will be dispatched" (e2898a6) (spec wording, confirmed by the owner's delegation on 2026-10-22), as `ApprovedBy` states.
- **F17.** Theorem 8, the accounting invariant: session-list entries with another session id were unconstrained (weaker, low). Proved `session_entries_own` and `accounting_session` (2819e00).
- **F18.** Proof architecture, which theorems are stated over traces: the list was wrong (spec, low). Rewritten from the printed statements (fef2ef4; spec wording, confirmed by the owner's delegation on 2026-10-22).
- **F19.** Supporting results wording: witness traces by `decide`, the policy check's `log_only` clause, "no theorem is vacuous", origin independence, `Inv` preserved by every event (weaker, low). The sentences now say `decide +kernel` under a witness policy, unexposed actions whose own mode is `log_only`, that no vacuous theorem is an aim, origin independence for each step, and `Inv` on every reachable state (fef2ef4; spec wording, confirmed by the owner's delegation on 2026-10-22).
