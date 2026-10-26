# Example traces

Hand-written `writ.trace/1` traces (spec section 9), one minified trace per line. Each file models one
adopter setup with a single policy, and every event carries an `expect` that pins at least the verdict,
the decision, and the reason, request id or grant when there is one. `lake build` replays all of them
(`WritTests/Corpus.lean`), so they cannot drift from the kernel. Session starts omit `policy_digest`;
it defaults to the digest of the trace's policy. The first trace of each file instead gives `policy_digest` explicitly on its session start, equal to `writ digest` of its policy, so a port tests its digest computation; a wrong digest there would be refused as `policy_digest_mismatch`. A few steps per file also pin `retry` and `state_version`, on a denial and on a rejected event.

These are one of three corpora. `corpus/attacks` holds hand-written traces of the red-team scenarios and
the ASU attacks, in the same conventions (`corpus/attacks/README.md`). `corpus/standard` holds the fixture
policies from which `writ traces` generates the standard corpus, which is not committed but pinned by
`corpus/standard/manifest.json` (`corpus/standard/README.md`). `scripts/corpus.sh` replays all three
together and checks that they reach every reason code. Two things come only from these files:
`already_reconciled`, which the generated corpus does not reach, from `device-split.jsonl`, and
`max_failures_per_session`, which no fixture uses, from `payments.jsonl`.

`web-chat.jsonl` models a chat assistant whose user approves actions in the chat window: web search
and calendar reads are free, sending email needs the user's approval. `parallel-calls` proposes three
calls in one model step, two run while the email waits for approval. `stop-twice` has the user press
Stop on two calls in a row; declines are not failures, so the session does not escalate even with
`max_consecutive_failures` 2. `reload-repeat` re-sends an identical propose after page reloads and gets
the call's current disposition each time (`needs_approval`, `authorized`, then `existing`).
`reject-then-retry` shows a rejected email denied `previously_rejected` when the model asks again,
until the user starts a new turn, and a repeat of the last event is rejected `stale_seq`.

`coding-agent.jsonl` models a coding agent whose host classifies shell commands with the
`not_allowlisted` (grantable) and `dangerous` (not grantable) escalators. `allowlisted-runs-free` runs
an allow-listed command and a file read without asking, and shows that an unreported escalator counts
as fired. `allow-for-session` approves an unlisted command with "allow for this session", and the next
run of the same command is `allowed_by_grant`. `dangerous-still-asks` uses an any-arguments session
grant: unlisted commands run on it, a dangerous one still asks. `kill-stops-everything` kills the
session with calls running, authorized and awaiting approval; everything after is out of order or
denied `killed`.

`langgraph-resume.jsonl` models a LangGraph graph that interrupts for approval and re-runs the node on
resume. `approval-hours-later` approves a deploy five hours later within its 48 hour per-action TTL,
while a ticket comment under the 10 minute policy TTL has expired. `edit-restarts-tally` has a second
reviewer edit a two-reviewer migration, which voids the first approval, makes the old dialog stale and
needs a fresh approval of the new generation. `resumed-repeat-edited-digest` shows a resumed repeat
returning `authorized` for both the edited and the original digest, and only the edited digest
dispatching. `argument-swap` is the Loopjacking attack (arXiv 2609.21081): the resumed node proposes
the approved call id with swapped arguments, the propose is rejected `duplicate_call` and the dispatch
with the swapped digest `digest_mismatch`, so nothing runs that the reviewer did not see.

`mcp-gateway.jsonl` models an MCP gateway with no turns, where principal meters stand in for
session limits. `rate-limit-window` meters `github.search` at 3 calls per rolling minute: a call over
the cap is denied at propose or refused at dispatch until the oldest call leaves the window.
`double-spend-session-a` and `double-spend-session-b` are two sessions of one principal against a
5000 per day meter: session b started from an older ledger, syncs to session a's final ledger with
`ledger_sync`, and its 3000 purchase is then refused, so the principal cannot spend 8000.

`payments.jsonl` models an agent paying vendors and charging a card against a 10000 per day principal
meter, with any failure escalating the session. `manager-and-finance` needs the requester's manager
and a different finance approver; one person holding both roles fills only one slot.
`partial-capture` commits a 4200 capture of a 5000 hold, which leaves room for a later 5800 charge.
`overrun-counts-as-failure` settles a 3000 charge at 3500, which escalates the session until an owner
acknowledges it. `grant-max-cost` runs two 1000 charges on a grant with `max_cost` 2500 and sends the
third to approval.

`device-split.jsonl` models a desktop app whose kernel runs on the server: the app confirms actions,
executes device-local tools on a server-issued ticket and reports back when it reconnects.
`device-confirms-result-later` approves in the app, claims the dispatch and reports `succeeded` a
turn later. `device-decline` reports a decline from the app's trusted approval renderer, which does
not count as a rejection. `device-never-reports` times an offline app out with `outcome_unknown`;
its late report is refused as a `result`, accepted as `reconcile`, and the call is never retried.

`mcp-approval.jsonl` models an MCP server that gates `payments.refund` on an out-of-band approval, as
SEP-2848 describes, while `docs.read` runs free. There is one trace per kernel-decidable conformance
statement of the SEP (`docs/sep-2848.md`, `corpus/sep-2848.json`). `s1-pending-not-executed` answers
`needs_approval` and refuses a dispatch while the approval is pending. `s2-approved-once` claims the
approved refund once and refuses a second dispatch. `s3-denied-not-executed` contrasts a rejected call,
which never claims, with an approved one reported `failed` after its claim. `s4-changed-arguments`
refuses a dispatch or a re-proposal with other arguments and shows an approver's edit authorizing only
the digest it set. `s5-cancelled-or-expired` cancels one refund, lets another's approval TTL lapse and
dispatches a third after its authorized TTL: none claims.
