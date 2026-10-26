# Attack traces

Hand-written `writ.trace/1` traces of the attacks spec section 9 names for the standard corpus: the
red-team scenarios and the ASU attack catalogue. They follow the conventions of
`corpus/examples/README.md`: one minified trace per line, one policy per file, every event with an
`expect` that pins at least the verdict, the decision and the reason, request id or grant when there
is one, and `policy_digest` given explicitly on the first trace's session start only. Each trace
shows the attack failing, except `cross-session-escape/replayed-grant-not-stopped`, which pins what
the kernel accepts and names the host rule (section 10) that stops it. `lake build` replays them
(`WritTests/Corpus.lean`), and `scripts/corpus.sh` replays them with the generated corpus and counts
them toward reason coverage. Section numbers below refer to `docs/design.md`.

Loopjacking (arXiv 2609.21081), the substitution of an approved call's arguments on resume, stays in
`corpus/examples/langgraph-resume.jsonl` as `argument-swap`; `asu/ab10-post-approval-substitution`
covers the same class against a dispatch.

## Red-team scenarios

`cross-session-escape.jsonl`: an approval or grant from one session replayed into another session
of the same principal. `session-a` approves a payment, adds a session grant and runs a second payment
on it, then kills the principal (`kill_scope: principal`). `session-b` starts from the ledger session
a had stored after its first payment. Starting under session a's id is rejected `already_started`
(the reused-id rule, section 6 Ledger and Identifiers). Under its own id the same payment needs a new
approval, because grant `g1` lives in session a's state (section 6 Grants); session a's approval
dialog is rejected `stale_request`, because a request id names its session (section 6
Identifiers); the dispatch is rejected `call_awaiting`. Its `ledger_sync` brings in session a's final
ledger, whose tombstone cancels the awaiting payment, after which the approval is rejected and new
proposals denied `killed` (section 6 Kill and Ledger, theorems 7 and 9). `WritTests/Corpus.lean`
checks that the synced ledger is the one session a ends with. `replayed-grant-not-stopped` is the
half of the scenario the kernel does not stop: a `grant_create` names no session and no request, so
to the kernel a replay of session a's grant message in session c is a fresh grant by the attested
owner. It is accepted and the payment runs on it. A replayed `permission_add` has the same gap.
Refusing replayed approval-plane messages is the host's job under section 10 (approvers are
authenticated by the host, and the agent cannot cause approval-plane events), for example by binding
`reviewed_scope_digest` to the session id. Shedding rejection memory or escalation by opening a
fresh session is not something the kernel can see: sessions are created by the host's control
plane, and section 7's gateway profile makes that a binding obligation.

`rollback.jsonl`: a stale state version or ledger after a commit. `stale-state-version` claims a
4000 payout against a 5000 principal meter; the same dispatch from a worker holding the pre-claim
state is rejected `state_version_mismatch`, and from the current state `call_dispatched`; a second
payout against the pre-claim state, when the meter still had room, is `state_version_mismatch`, and
against the current state it is denied `meter_exceeded`. A redelivered event is `stale_seq` and a
clock that went backwards `time_decreasing` (section 6 Events and Protocol errors, section 7 single
writer per session, theorem 4). `stale-ledger` syncs a ledger older than the one the claim produced,
then a newer copy that lost the session's reservation, then, after an out-of-band principal kill
arrives, a stored ledger rolled back to clear the tombstone: each is rejected `ledger_conflict`
(section 6 Ledger, section 7 several live sessions per principal, theorem 9), and the session stays
killed. `ledger_conflict` has retry class `never`: a binding ends the session there; the trace goes
on only to show that the rejected syncs left the state as it was. What the kernel cannot see is a
session started from a stale snapshot, or a client replaying an older sealed state: the
compare-and-swap on both versions and the freshness check on client-carried state (sections 7
and 10) are what stop those; `corpus/examples/mcp-gateway.jsonl` (`double-spend-session-a` and
`double-spend-session-b`) shows a session that started from a stale snapshot recovering through
`ledger_sync`.

`quorum-edit-laundering.jsonl`: an approver edit that tries to keep a prior approval.
`edit-voids-tally` has Carol approve a two-reviewer migration and Dave edit it while approving. The
edit starts generation 1 and counts only Dave, so the dispatch is `call_awaiting`, Carol's old dialog
`stale_request`, and Dave's second approval, also from a second approver id of the same principal,
`already_approved`, because quorum counts principals (section 6 Approve and Quorum, Principals). When
Dave edits back to the original digest, Carol's approval of it from generation 0 does not come back;
she has to approve generation 2. `edit-cannot-lower` has an over-the-limit payment that needs two
finance approvers other than the requester; Erin edits it below the limit with `over_limit` false,
but an edit only joins the edited arguments' consent into the call's (section 6 Approve, theorem 1),
so the call stays pending, the requester's own approval fills no slot of the escalated clause
(`exclude_requester`), and only Frank's approval completes it.

`stale-dialog.jsonl`: an approval with an old request id or generation. `old-generation` refuses an
approval from a dialog opened before an edit (`stale_request`), a refreshed request id whose card
still showed the old arguments (`digest_mismatch`), a forged future generation and another call's
request id (`stale_request`) and an `approval_expire` of the old generation (`stale_request`)
(section 6 Identifiers and Approve, theorem 6). A late reject on the generation 0 dialog still vetoes
the authorized call, so its dispatch is `call_ended`: a stale approval never counts, a stale veto
always does (section 6 Quorum). `expired-and-reset` refuses an approval at its TTL
(`approval_expired`, section 5 limits), an approval of a call the host's `reset` cancelled
(`call_ended`, section 6 Reset), and the cancelled call's request id used on the fresh call that
replaces it (`stale_request`); a repeat of the cancelled proposal reports it `existing`, status
`cancelled`.

`rejection-shopping.jsonl`: re-proposing a rejected call in the same turn. `same-turn` rejects an
email; asking again is denied `previously_rejected`, a second approver cannot approve a copy proposed
before the rejection, an agent-initiated turn does not clear the memory, and an approver edit that
turns another email into the rejected one is refused `previously_rejected`. A `reset` does not clear
the memory either (section 6 Reset: rejection memory carries over); only a `user_initiated` turn lets
the model ask again (section 6 Propose step 9 and Approve, theorem 12).
`earlier-approval-falls` shows the memory reaching back: a call approved before a duplicate of it was
rejected is `dispatch_denied` `previously_rejected` at dispatch, and a turn grant created afterwards
for the same digest does not cover it, because step 9 runs before consent. The memory is keyed on
`(tool, call_digest)`, so a model that changes the arguments asks a new question; the approval
budgets bound how often it can (`asu/ab11-flooding`).

## ASU catalogue

ASU, "Approve What, Exactly? Effect Binding and Trusted Rendering for Agent Step-Up Authorization"
(arXiv 2610.21063), defines twelve attacks on the approval path, AB1 to AB12 in its Table 3, read
from the paper's arXiv HTML page. `asu.jsonl` has one trace per attack whose kernel-level part Writ
can express, all under one payments policy: a `per_call` payment waived below 5000, a `new_payee`
escalator that is not grantable, digest-bound session grants of at most 3 uses, a principal money
meter of 20000 and a calls meter of 5 per 10 minutes (ASU's packaged default of five effects or
200 USD per 600 seconds, in cents), and approval budgets of 3 per turn and 5 per session.

| Attack | Trace | What stops it |
|---|---|---|
| AB1 amount cancellation | `asu/ab1-amount-cancellation` | A call declares one cost, an amount with no sign, which the host derives from the arguments; the kernel never sums argument values. A missing cost is denied `cost_missing`, an approval or a dispatch under a netted cost is `cost_mismatch` (section 6 Propose step 8, Approve, Dispatch; theorem 1). Deriving the cost from the arguments correctly is the host's part (section 10). |
| AB3 grant stretching | `asu/ab3-grant-stretching` | A grant covers only the digest it names, so another payee or a larger amount needs approval; a fired escalator that is not grantable is never covered; a grant above the action's `max_uses` is `grant_not_allowed`, and a spent grant covers nothing more (section 6 Grants, theorems 1 and 2; ASU's L5 and L5b). This assumes payments are not granted `any_args`, or that such grants are bounded by `max_cost`: an `any_args` grant covers any payee, by design. |
| AB7 enrollment squatting | `asu/ab7-enrollment-squatting` | An unattested approver is `unknown_approver`; an approver whose principal is the reserved `agent` is never eligible (`approver_not_eligible`), even for an action that admits automated approvers; an attested approver id cannot be re-pointed (`approver_changed`) (section 5 `approver_roles`, section 6 Principals). That attestation is control plane, out of the agent's reach, is section 10's trust boundary, which is ASU's closed-enrollment hypothesis H2. |
| AB10 post-approval substitution | `asu/ab10-post-approval-substitution` | Dispatch requires the authorized digest (`digest_mismatch`), a call id cannot be re-proposed with other arguments (`duplicate_call`), and a call is claimed once (`call_dispatched`, then `call_ended`) (section 6 Identifiers and Dispatch, theorems 1 and 4; ASU's L1 and L2). |
| AB11 flooding within one run | `asu/ab11-flooding` | Identical repeats merge into one request; `approval_budget` per turn and `session_approval_budget` per session cap the requests; a rejected call asked again is `previously_rejected` (section 5 limits, section 6 Propose steps 9 and 10, theorems 8 and 12). ASU reports that flooding still succeeds 0.45 to 0.60 of the time against a modeled human; Writ bounds the number of requests, not an approver's fatigue. |
| AB12 threshold splitting | `asu/ab12-threshold-splitting` | Windowed principal meters bound the total: pieces under the approval threshold run until the money meter is full (`meter_exceeded`), and small pieces hit the calls meter (section 5 meters, section 6 Meters, theorem 8). ASU forces a fresh challenge when the window is crossed; Writ denies until the window frees room. A host that wants step-up instead can report a host-computed escalator. |

The other six attacks target the approval display, the authenticator ceremony or the digest
encoding, which the kernel does not see: it compares digests for equality and never reads arguments
or renders anything (section 3, section 6 Call digests).

| Attack | Why there is no kernel trace |
|---|---|
| AB2 decoy-field recipient | Adding a `bcc` changes the arguments and so the digest: after approval that is AB10; before it, the trusted renderer must list every recipient (section 10), which no event can show. ASU's AB2 also targets the grant check, and that half is kernel-visible: the extra recipient changes the digest, so a digest-bound grant does not cover the call (the other-payee step of `asu/ab3-grant-stretching`). |
| AB4 padding and hidden text | A rendering attack on the approval card. Section 10 requires a renderer that shows the canonical arguments without truncation and flags confusable and invisible characters. |
| AB5 label spoofing | A rendering attack: agent-chosen argument names imitating trusted labels. The renderer, not the kernel, decides the card layout (section 10). |
| AB6 non-injective rendering | Two effects with one card is a property of the renderer; distinct effects already have distinct digests under `writ-call-v1`, whose canonical JSON is covered by the vectors in `corpus/digests`. |
| AB8 challenge ambiguity | About the bytes an authenticator signs. Writ's request id is a structured `{session, call, generation}` compared field by field, and approval signatures are the host's (audit fields, section 6 Events). |
| AB9 ceremony control | The page driving the authenticator shows one effect while the device signs another. That is a matter for the host's UI. ASU blocks the agent-reachable part and assigns the rest to its hypothesis H3. |
