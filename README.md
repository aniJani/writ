# Writ

Writ is a Lean 4 library for the policy kernel of a tool-using AI agent: the small piece of logic that decides whether a proposed tool call may run, needs people to approve it, or is refused, and that tracks what happened afterwards (dispatch, results, retries, meters, grants, kill and escalation). The kernel is a pure function `step : Policy → State → Event → State × Verdict`, written so that its safety rules can be proved in Lean. It does not verify the model, and it does not verify host application code.

## Trust boundary

Writ's guarantees hold only if:
- every side effect goes through the kernel (complete mediation), and the mapping from a raw tool call to a Writ `tool` name is part of the host's trusted code;
- the agent cannot cause approval-plane or control-plane events, and cannot write the policy (the policy comes from outside the agent's reach, for example a pinned file or a config service; loosening it should itself require approval);
- the host computes digests per the spec and executes the exact bytes it digested; on an approver edit, the host recomputes `new_digest` from the edited arguments and `new_cost`, and a host that relays an end user's edit must not let that user lower the declared cost of their own call without the policy's consent;
- a trusted renderer, not the agent, builds the approval display from the canonical arguments, without truncation, flagging confusable and invisible characters;
- approver identities, kinds and roles are authenticated by the host, and so is the freshness of the messages that carry an approver's decision: `approve` and `reject` echo a request id, but `grant_create`, `permission_add` and `escalation_ack` name no request (`escalation_ack` carries only the escalation count it reviewed), so the kernel takes a replayed one for a fresh one, and the host must refuse one replayed from another session or from an earlier decision (for example by binding a grant's `reviewed_scope_digest` to the session id);
- event times come from a trusted, monotone server clock;
- every store is a compare-and-swap on the session state version and on the version of the principal ledger the step read (atomic over both when several sessions of a principal are live), and post-dispatch state is stored before execution;
- state carried on the client is sealed and also checked for freshness: the host keeps each session's latest `state_version` on the server, compare-and-swaps it on every step, and refuses a sealed state whose version differs (sealing gives integrity, not freshness), and never takes the principal ledger from client-carried state;
- `dispatch` immediately precedes execution, and kill is delivered with priority and aborts in-flight tools where possible;
- guard values, escalator values (on `propose` and on approver edits; they decide whether a session grant may stand in for a call), declared and actual costs, and outcomes (`declined`, `no_effect`) are reported by trusted code, or clamped by the binding as section 6 describes (from an untrusted executor, a release becomes a commit of at least the reservation, and a `declined` becomes `failed` unless the decline came through the trusted approval renderer).

Writ is built so that the kernel and the policy compiler can be proved in Lean. Theorems 1 (consent), 2 (grant accounting), 3 (permission), 4 (at most once), 5 (terminal absorption), 6 (epoch and freshness), 7 (kill), 8 (bounds), 9 (ledger), 10 (default deny), 11 (escalation) and 12 (rejection memory) are proved over the shipped kernel in the `WritProofs` library, and theorem 13 (expansion soundness) over the layer-2 expansion (see [Proof status](#proof-status)); the rest of the kernel is tested: unit guards, a spec-derived fuzzer and conformance traces. With the WASM or native build, the decision logic in the host is that same Lean kernel; the glue (digests, event encoding, persistence) is tested against the corpus and the oracle.

## What v0.1-preview contains

This is a preview, `0.1.0-preview.1`. What works today:

- the kernel, covering every v0.1 rule of the policy format's layer 1, with theorems 1 to 12 and the supporting results of spec section 8 proved (see [Proof status](#proof-status));
- the `writ` command: `check`, `digest`, `replay`, `oracle` and `explain`;
- the hand-written conformance corpus in `corpus/examples`: six adopter trace files (web chat, coding agent, LangGraph resume, MCP gateway, payments, device split) and the SEP-2848 traces in `mcp-approval.jsonl`, with the call digest vectors in `corpus/digests`;
- the kernel compiled to WebAssembly (`writ.wasm`);
- `@anijani/writ`, the TypeScript package, with the gate, the minimal path (`@anijani/writ/simple`), the Vercel AI SDK adapter (`@anijani/writ/ai-sdk`) and a Firestore store. It is ready to publish but not on npm yet;
- the LangGraph example (`examples/langgraph`), which uses the gate directly, and the AI SDK example (`examples/ai-sdk`);
- a browser playground for local use (`playground`).

On main since the preview, not yet released (`CHANGELOG.md` lists each change under Unreleased):

- layer 2 of the policy format (labels, rules and `extends`), checked by `writ check` and expanded by `writ expand`, with theorem 13 proving the expansion sound, and the four presets from the spec (`generic-tiers`, `mcp-annotations`, `mcp-risk-metadata`, `axes`) as layer-2 files in `schema/presets/`;
- the `writ-tool-v1` tool digest (also `toolDigest` in `@anijani/writ`) and the optional per-action `source` field that records it;
- `writ import mcp`, which drafts a layer-2 policy from an MCP tool list, and `writ check --tools`, which reports each action whose MCP tool definition changed since its `source.tool_digest` was recorded;
- `writ diff`, which replays recorded events under two policies and lists the verdicts that changed;
- `writ traces`, which explores a policy's states and emits the shortest trace for every abstract transition, and `writ replay --coverage`, which lists the reasons and decisions a replay reached;
- the standard corpus: nine fixture policies in `corpus/standard`, from which `scripts/corpus.sh` generates 23764 traces that, with the hand-written ones, reach every reason code. The generated traces are not committed: `corpus/standard/manifest.json` pins them by count and SHA-256, and `scripts/corpus.sh --tar` packs them with the hand-written corpora into the corpus tarball the next release ships;
- hand-written attack traces in `corpus/attacks`: the red-team scenarios of spec section 9 and the ASU attacks the kernel can express;
- `writ-fuzz --judge`, which checks every verdict and state of a trace file against the spec-side checkers in `WritSpec`, and judges the whole corpus in `scripts/corpus.sh`;
- the MCP SEP-2848 profile `mcp-tool-approval`, outside the kernel: the SEP-2848 disposition of each terminal call status and the SEP-2643 structured-denial envelope of each verdict, `writ check --profile` and `writ explain --profile`, WebAssembly function 10, `kernel.profile` and `mcpToolApproval` in `@anijani/writ`, and `profile_unknown_final`, which proves that under a policy with no profile error the kernel accepts no dispatch of a call whose outcome is unknown;
- `writ-kernel`, the Python binding (`packages/writ-py`), which runs a standalone link of the same WebAssembly kernel in wasmtime: the kernel, canonical JSON, the call and tool digests, the gate with its store protocol and `MemoryStore`, the minimal path and the profile;
- the release workflow (`.github/workflows/release.yml`), `scripts/check-version.sh` and the local rehearsal `scripts/release-dryrun.sh`. The workflow has been rehearsed locally with `scripts/release-dryrun.sh` (every asset on macOS; build, tests and corpus in a linux/arm64 container) and has never run on GitHub (see [Releasing](#releasing)).

What does not exist yet:

- framework adapters other than the AI SDK one, a LangGraph adapter included, any Python framework adapter, and the MCP gateway gate;
- the trace converters (ITF, Dogwood, Cedar test JSON);
- release binaries, `@anijani/writ` on npm and `writ-kernel` on PyPI, which wait for the first tagged release, and a Reservoir listing, which follows once the repository and the tag are public: build from source.

Section 15 of `docs/design.md` says which later milestone takes each, and section 11 covers the release binaries.

## Using the CLI

The `writ` command checks policies, drafts them from MCP tool lists, generates and replays conformance traces, compares two policies on recorded traffic and steps the kernel over events, with no Lean code to write. `writ --help` lists the commands, and `docs/formats.md` describes the JSON formats they read and write.

Install from source with the pinned toolchain (there are no dependencies):

```sh
lake build writ
```

The binary is `.lake/build/bin/writ`. Exit codes for every command: 0 success, 1 findings (check errors, replay failures), 2 usage, IO, parse or decode errors.

`writ check` decodes a policy and reports authoring errors and warnings (`--json` for machine output), and with `--tools <tools.json>` reports each action whose MCP tool definition changed since its `source.tool_digest` was recorded. `schema/writ.policy-0.1.schema.json` is a JSON Schema for editors, and `schema/examples/assistant.json` is a sample policy for a general-purpose assistant.

```sh
$ writ check schema/examples/assistant.json
ok
```

Here a server rewrote the description of `web.fetch` under the same name after the policy recorded its digest:

```sh
$ writ check tests/cli/tools/child.json --tools tests/cli/tools/web-poisoned.json
error: web.fetch: tool "web.fetch" changed: source.tool_digest is sha256:2090263f72e715d1bcdc3e8c2dbba75a65f0567b365ee68a8f371b5a9a6b1cab, the tool list has sha256:17964b625595c02034011bd7f85b9bff78931e8109e2ba8971e2ab4f7d794e26
1 error, 0 warnings
```

`writ expand` turns a layer-2 policy (labels, rules and `extends`, see `docs/formats.md`) into the layer-1 policy the kernel runs, printed as canonical JSON on one line (`--out` writes it to a file). `writ check` checks a layer-2 policy and the policy it expands to. A team policy that extends an organization baseline can never weaken the baseline's rules and per-action requirements, and cannot turn on policy-wide `log_only`. The team still owns the policy-level settings (`approver_roles`, `escalation_roles`, meter definitions and caps, and limits, TTL limits included), so whoever deploys a policy must vet those and confirm that it extends the intended baseline. Here the team lowers a refund's quorum, exposes it and allows more grant uses on `repo.push`, and the expansion keeps the baseline's quorum-2 group, `exposed: false` and three turn-scoped uses.

```sh
$ writ expand tests/cli/layer2/team.json
{"actions":{"payments.refund":{"consent":{"groups":[{"all":[{"quorum":1,"roles":["finance"]}]},{"all":[{"quorum":2,"roles":["finance"]}]}]},"exposed":false,"guards":["change_window"],"permission":"payments.refund","review":{"title":"Refund a payment"}},"repo.push":{"consent":"per_call","grantable":{"max_uses":3,"scope":"turn"},"messages":{"guard_false":{"user":"Pushes wait for the change window."}}},"repo.read":{}},"approver_roles":["finance","dev"],"limits":{"approval_ttl_ms":600000},"writ":"0.1"}
```

`writ import mcp` drafts a layer-2 policy from an MCP server's tool list. Tool annotations are the server's untrusted claims, so the draft labels every tool at the strictest value of each `mcp-annotations` dimension, copies the claims into each action's `source` with the tool digest, and names on stderr each claim it did not apply. Its expansion requires consent for every tool until you review a tool and lower its labels by hand.

```sh
$ writ import mcp tests/cli/import/claims.json --preset-dir ../../../schema/presets --out tests/cli/import/claims-draft.json
web.fetch: the server says readOnlyHint true; read_only left "false" (lower it after review)
notes.put: the server says destructiveHint false; destructive left "true" (lower it after review)
notes.put: the server says idempotentHint true; idempotent left "false" (lower it after review)
notes.put: the server says openWorldHint false; open_world left "true" (lower it after review)
```

`writ digest` prints the policy digest, the SHA-256 of the canonical JSON of the policy as written. Every `session_start` event carries it.

```sh
$ writ digest schema/examples/assistant.json
sha256:b12b208c49103e9b7f52c460b896ccca196729bfdb7d227db73f6888c164834d
```

`writ replay` replays conformance traces (`writ.trace/1`, one per line) and compares each step with its expected verdict fields.

```sh
$ writ replay corpus/examples/payments.jsonl
ok payments/manager-and-finance
ok payments/partial-capture
ok payments/overrun-counts-as-failure
ok payments/grant-max-cost
4 traces, 0 failed
```

With `--coverage`, a last line lists the reason codes and decisions the replayed verdicts reached.

```sh
$ writ replay corpus/examples/payments.jsonl --coverage | tail -1
{"reasons":["already_approved","escalated","meter_exceeded"],"decisions":["allowed_by_grant","authorized","denied","dispatch_claimed","needs_approval","overrun","pending"]}
```

`writ explain` prints one line per step of a trace (`--id` picks one trace from a file).

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

`--profile mcp-tool-approval` applies the MCP SEP-2848 profile (`docs/formats.md`, MCP SEP-2848 profile; `docs/sep-2848.md`). On `writ check` it reports the settings SEP-2848 forbids: `retry_after_unknown` is an error, because a call whose outcome is unknown must never run again, and `max_attempts` above 1 without it a warning.

```sh
$ writ check tests/cli/policies/profile-retry.json --profile mcp-tool-approval
error: payments.refund: retry_after_unknown is true, but under SEP-2848 outcome-unknown is final: a call whose outcome is unknown must never run again
warning: docs.read: max_attempts is above 1 without retry_after_unknown, so it has no effect: under SEP-2848 a call runs at most once
1 error, 1 warning
```

On `writ explain` it prints, under each step, the SEP disposition of every call the step made terminal and the SEP-2643 envelope of the verdict when it has one. Here an approver rejects `c1`, which is then refused at dispatch, and the approved `c2` is claimed and fails:

```sh
$ writ explain corpus/examples/mcp-approval.jsonl --profile mcp-tool-approval --id mcp-approval/s3-denied-not-executed | sed -n '10,11p;15,16p;19,21p'
  6 reject call_id=c1 approver=ops -> accepted none
      disposition call_id=c1 denied-not-executed
  10 dispatch call_id=c1 -> rejected (reason call_ended, retry never): That request has already finished.
      envelope {"reason":"insufficient_authorization","remediation":"unavailable","code":"call_ended","retry":"never","message":"This call has already finished. Do not repeat it; propose a new call if you need one."}
  12 dispatch call_id=c2 -> accepted dispatch_claimed
  13 result call_id=c2 outcome=failed -> accepted none
      disposition call_id=c2 execution-error
```

`writ oracle` reads one event per line on stdin and writes one verdict per line, keeping the state between lines (`--state` and `--state-out` load and save it). Bindings use it for differential testing.

```sh
$ writ oracle tests/cli/policies/formats-shop.json < tests/cli/formats-events-a.jsonl
{"verdict":"accepted","state_version":1}
{"verdict":"accepted","state_version":2}
{"verdict":"accepted","state_version":3}
{"verdict":"accepted","state_version":4,"decision":"needs_approval","request_id":{"session":"s1","call":"c1","generation":0}}
```

`writ diff` replays recorded events under two policies, each layer 1 or 2, and lists each event whose verdict changed, so you can see what a policy change does before you deploy it. Each run gets its own `state_version` and policy digest, so one changed verdict does not make every later event fail. Exit 1 when a verdict changed. Here the events were recorded under a policy where `buy` is free, and the new policy makes it need approval:

```sh
$ writ diff tests/cli/diff/old.json tests/cli/diff/tight.json tests/cli/diff/old-events.jsonl
line 4 seq 4 propose c1: {"verdict":"accepted","decision":"allowed"} -> {"verdict":"accepted","decision":"needs_approval","request_id":{"session":"s1","call":"c1","generation":0}} (first divergence)
line 5 seq 5 dispatch c1: {"verdict":"accepted","decision":"dispatch_claimed"} -> {"verdict":"rejected","reason":"call_awaiting"}
line 6 seq 6 result c1: {"verdict":"accepted"} -> {"verdict":"rejected","reason":"call_awaiting"}
3 of 11 events changed
```

`writ traces` explores a policy's states breadth-first over a small alphabet of events (spec section 9) and prints the shortest trace for every transition between abstract states, plus the first rejected event found for each event type and reason, each event pinning its whole verdict. `--depth` (default 4) bounds the events after `session_start`, `--max-states` (default 20000) bounds the search, and the output is the same bytes on every run. The summary goes to stderr:

```sh
$ writ traces tests/cli/traces/tiny.json --depth 3 > tiny.jsonl
states 434, traces 867 (accepted 699, rejected 168), depth 3
$ writ replay tiny.jsonl | tail -1
867 traces, 0 failed
```

`scripts/corpus.sh` runs `writ traces` on the fixture policies in `corpus/standard/fixtures`, fails if the output differs from `corpus/standard/manifest.json`, replays it with the hand-written corpora, judges it with `writ-fuzz --judge` and fails unless every reason code is reached. `scripts/corpus.sh --tar` also writes the corpus tarball, `build/writ-corpus-<version>.tar.gz`. `corpus/standard/README.md` and `docs/formats.md` (Standard corpus) describe it.

```sh
$ scripts/corpus.sh | tail -3
23808 traces, 0 failed
judged 23808 traces, 0 violations
every reason code is covered or listed in corpus/standard/uncovered.json (0 listed)
```

The 23808 traces are the 23764 generated ones and the 44 hand-written ones in `corpus/examples` and `corpus/attacks`.

## TypeScript

`packages/writ` is `@anijani/writ`, a TypeScript package around the kernel compiled to WebAssembly. It has a typed kernel wrapper (including `tombstone`, a read-only `inspect` of a session and `profile`, with `mcpToolApproval` for the MCP SEP-2848 profile), call digests (`callDigest`, vectors in `corpus/digests/call-v1.jsonl`), and a gate that commits every step through a compare-and-swap store before it returns. The gate narrows each result for the host (`propose` gives `kind` `allowed`, `needs_approval`, `denied` or `rejected`; `dispatch` gives `claimed`; reports give `overrun`), kills a principal across all its sessions (`killPrincipal`, `clearPrincipalKill`), bounds each session's stored state with headroom left for kill and end, settles sessions of a retired policy, and lists the calls left to settle after a crash (`inspect`). It also has sealed state with a freshness check for client-carried sessions, and a Firestore store. The package ships the kernel (`wasm/writ.wasm` and `wasm/writ.mjs`) in its tarball. Measured on 2026-10-25, `writ.wasm` is 2,215,471 bytes raw and 392,943 bytes gzipped, and a step takes about 0.2 ms in Node for a small state, growing linearly with the state size (see the package's Limits section). It is not on npm yet, so build it from the repository; see [packages/writ/README.md](packages/writ/README.md) and `build/wasm/README.md`. [examples/langgraph](examples/langgraph/README.md) replays the `langgraph-resume` traces through a real LangGraph.js graph that interrupts for approval and re-runs the node on resume. `@anijani/writ/ai-sdk` puts the gate in front of the Vercel AI SDK's tool execution, so an edited or replayed message history fails at dispatch ([examples/ai-sdk](examples/ai-sdk/README.md) runs it against the real SDK). [playground](playground/README.md) is a local browser page that runs the same WebAssembly kernel on a policy and events you choose, with no model and no server logic. `examples/` holds demos with their own dependencies (LangGraph, the AI SDK), `packages/writ/examples/` the package's own examples.

## Python

`packages/writ-py` is `writ-kernel` (import package `writ`, Python 3.10 or later), the second binding. It runs the same kernel objects, linked a second time as a standalone WebAssembly module (2,250,380 bytes, 381,709 gzipped, on 2026-10-25), in wasmtime, its only runtime dependency, and mirrors `@anijani/writ` module by module, synchronously and in snake_case: `load_kernel()` and a `Kernel` with every method of the TypeScript wrapper, `canonicalize` and `parse_strict` (RFC 8785 written in Python, not `json.dumps(sort_keys=True)`), `call_digest` and `tool_digest`, which pass every vector in `corpus/digests`, `create_gate` with the `Store` protocol and a thread-safe `MemoryStore`, the minimal path `simple_gate`, and `mcp_tool_approval` for the SEP-2848 profile. Its tests port the TypeScript gate and store suites test for test and compare the kernel verdict by verdict with `writ oracle`. It has no sealed state, Firestore store or framework adapter. It is not on PyPI yet: build the WebAssembly with `scripts/build-wasm.sh`, then `uv build` in `packages/writ-py` gives a wheel that carries the kernel; see [packages/writ-py/README.md](packages/writ-py/README.md). `scripts/py-test.sh` runs ruff, mypy (strict) and the tests.

## Building and testing

The toolchain is pinned in `lean-toolchain` (Lean 4.35.0); there are no Lake dependencies.

```sh
lake build
```

The tests are `#guard` commands in `WritTests/`, built as part of the default targets, so a failing test fails the build. They cover every reason code and disposition with a witness trace (`WritTests/Witness.lean`), the attack traces from review (`WritTests/Attacks.lean`), and the executable invariant `Inv.check` (`WritSpec/InvCheck.lean`), which is checked after every step of the checked traces. `lake build` also checks the proofs in `WritProofs`, where any warning, a `sorry` included, is an error.

The hand-written conformance traces in `corpus/examples` and `corpus/attacks` replay during the build too, and `docs/sep-2848.md` maps those in `corpus/examples` to the seven conformance statements of SEP-2848, the MCP draft for asynchronous approval of tool calls, a mapping that `WritTests/Sep2848.lean` checks.

`WritSpec/Checks.lean` holds trace checkers for the frame lemma and theorems 1 to 12, judged against a shadow model (`WritSpec/Shadow.lean`) written from the spec without reading the kernel. They run over interleavings of several live sessions of one principal that share a stored ledger under the compare-and-swap protocol of section 7. `WritTests/Fuzz.lean` runs them during the build on 400 fixed-seed random traces of 40 steps each (seeds 1 to 400), and checks that 200 generated policies pass `Policy.check` and that 200 policies with a planted defect are refused. For longer runs, build the driver (`WritTests/FuzzMain.lean`) with `lake build writ-fuzz` and run `.lake/build/bin/writ-fuzz --seed 1 --traces 100000 --length 60`. Flags: `--seed N` (first seed, default 1), `--traces N` (default 1000), `--length N` (steps per trace, default 60), `--reports N` (violations printed per checker, default 1), `--no-shrink` (print violations unshrunk), `--stop` (stop at the first violation), `--mutant NAME` (fuzz one mutant of the kernel from `WritTests/Fuzz/Mutants.lean`), `--mutants` (run the whole mutation set, report in how many traces and by which checkers each mutant is caught, and fail if any is caught in fewer than 5 traces), `--bad N` (check that `Policy.check` refuses N generated policies with a planted defect), and `--judge <traces.jsonl>...` (run each trace through the kernel and check every verdict and state with the same checkers, one session per trace; `scripts/corpus.sh` judges the whole corpus this way). A violation is shrunk and printed as `checkedScript` sessions plus their interleaving, ready to paste into a test.

Layout:

- `Writ/Core`: the data types (reasons, policy, events and state). `Core/Consent.lean` is the consent algebra (clause groups, join, effective consent).
- `Writ/Kernel`: the logic. Approver eligibility and quorum (`Kernel/Eligibility.lean`), meters, failure counters, grants and call lifecycle, one handler file per event family in `Kernel/Step/`, the `step` function and `run`.
- `Writ/Author`: tools for policy authors. The policy checker (`Author/Check.lean`: `Policy.check`, `Policy.WF`), the policy warnings (`Author/Warnings.lean`) and layer 2: its types (`Author/Layer2.lean`), the joins (`Author/Join.lean`), and `expand` with the layer-2 check (`Author/Expand.lean`).
- `WritSpec`: a library of its own, outside the kernel library `Writ`, holding the executable invariant (`InvCheck.lean`), the shadow model (`Shadow.lean`) and the trace checkers (`Checks.lean`), which judge theorems 1 to 12 in the fuzzer and in `writ-fuzz --judge` whether or not a theorem is proved.
- `WritTests`: the test suite, one file per kernel area, plus the fuzzer and the judge in `WritTests/Fuzz` (driver `WritTests/FuzzMain.lean`, executable `writ-fuzz` with the flags above).
- `WritProofs`: Lean proofs of section 8 theorems over the shipped kernel, with their axioms pinned in `WritProofs/Axioms.lean` (see [Proof status](#proof-status)).
- `Writ/Json` and `Writ/Codec`: the JSON parser, printer and SHA-256, and the codecs for the formats in `docs/formats.md`. `Writ/Api.lean` holds the JSON entry points the WebAssembly build exports.
- `Writ/Profile`: the MCP SEP-2848 profile (`McpToolApproval.lean`), outside the kernel; `Writ/Api.lean` and the `writ` command import it.
- `Writ/Explore`: the state explorer behind `writ traces` (alphabet, abstract key and search), outside the WebAssembly build.
- `WritCli`: the `writ` command.
- `WritWasm` and `build/wasm`: the Lean exports and the build inputs (C shims, the runtime patch, the smoke test) of the WebAssembly kernel, which `scripts/build-wasm.sh` writes to `packages/writ/wasm` and, as a standalone module for wasmtime, to `packages/writ-py/src/writ/wasm`.
- `packages/writ`: the TypeScript package; `packages/writ-py`: the Python package; `examples`: demos with their own dependencies (`examples/langgraph`, `examples/ai-sdk`).
- `playground`: a static browser page over the WebAssembly kernel, for local use (`node playground/build.mjs && node playground/serve.mjs`).
- `corpus`, `schema` and `docs`: the hand-written conformance traces (`corpus/examples`), the attack traces (`corpus/attacks`), the standard corpus fixtures and manifest (`corpus/standard`), the call and tool digest vectors (`corpus/digests`) and the profile vectors (`corpus/profiles`), the policy JSON schema, sample policies, the layer-2 presets (`schema/presets`) and reason list, and the spec, formats, theorem map and SEP-2848 mapping.
- `scripts`: `cli-test.sh` runs the CLI cases in `tests/cli`, `build-wasm.sh` builds the WASM kernel, `check-proofs.sh` checks that `WritProofs` has no `sorry`, `admit`, `native_decide`, `unsafe` or `axiom` and that every name the Proof status section cites as proved has a `#print axioms` line in `WritProofs/Axioms.lean`, `print-statements.sh` prints every pinned statement without its proof (`--defs` adds the `WritProofs` definitions they use), `corpus.sh` generates, checks, replays and judges the standard corpus (`--update` rewrites the manifest, `--tar` writes the corpus tarball), `py-test.sh` runs the Python package's checks and tests, `check-version.sh`, `release-build.sh` and `release-dryrun.sh` check the version, build one release asset and rehearse a release, and `tarball.py` writes the reproducible tarballs.
- `.github/workflows/ci.yml`: on every push and pull request, `lake build`, `scripts/cli-test.sh`, `scripts/check-proofs.sh`, `writ-fuzz --mutants`, `writ-fuzz --traces 1000` and `scripts/corpus.sh`. The WASM, npm and Python checks need the pinned emcc and run locally and in the release workflow.
- `.github/workflows/release.yml`: the release, on a pushed `v<version>` tag (see [Releasing](#releasing)).

## Releasing

A release publishes, from one tag, the binary tarballs for linux-x64, linux-arm64 and macos-arm64, `@anijani/writ` on npm, `writ-kernel` on PyPI and the corpus tarball, with a `SHA256SUMS` file, on a GitHub release. The workflow has been rehearsed locally but has never run on GitHub, so nothing has been published this way yet.

1. Set the version in `lakefile.toml`, `cliVersion` in `Writ/Core/Version.lean`, `packages/writ/package.json` and its `package-lock.json` (`npm version --no-git-tag-version <version>` writes both), and `packages/writ-py/pyproject.toml`, which writes it in PEP 440 form (`0.2.0-preview.1` is `0.2.0a1`), then run `(cd packages/writ-py && uv lock)` so that `packages/writ-py/uv.lock` records it too. Update `tests/cli/version.out`, and move the CHANGELOG's Unreleased section under a `## <version> (<date>)` heading. `scripts/check-version.sh` checks all of this and lists every mismatch.
2. Rehearse with `scripts/release-dryrun.sh`. It runs the checks the workflow runs, builds every asset into `build/release/out/` with `SHA256SUMS` and publishes nothing. `--linux` also builds and tests in a linux/arm64 Ubuntu container (Docker), including the corpus manifest check. A run cut off by a timeout resumes where it stopped when started again; `--fresh` starts over.
3. Merge to the default branch. Before the first tag, run the workflow by hand there (Actions, Release, Run workflow, with `dry_run` left true): its GitHub side (emsdk, the hosted runners, the npm and Python packaging) has never run, and a run by hand builds and checks every asset and publishes nothing.
4. Push the tag `v<version>` on the merged commit. `.github/workflows/release.yml` checks the tag against the version files, runs the green set and builds every asset, then waits for a reviewer to approve the `release` environment. It then creates a draft GitHub release, publishes to npm and PyPI, and publishes the draft. A failed publish can be re-run: each step skips what is already there.

Only a tag push can reach the publish job, so a run by hand publishes nothing whatever `dry_run` says.

The owner sets up, once: the GitHub environment `release`, with a required reviewer and a deployment rule admitting only `v*` tags; an npm token for `@anijani/writ` as that environment's secret `NPM_TOKEN`, or, the owner's choice, npm trusted publishing (OIDC) for `@anijani/writ`, naming this repository, the workflow `release.yml` and the environment `release`, which needs no stored token (the publish job already has `id-token: write`); npm sets it up only on a package that exists, so the first publish still takes the token; and on PyPI a trusted publisher (pending, until the project exists) for `writ-kernel`, naming this repository, the workflow `release.yml` and the environment `release`. npm provenance checks the repository URL in `packages/writ/package.json` (`github.com/aniJani/writ`) against the repository the workflow runs in, so the GitHub owner and name must match it, casing included.

## License

Apache-2.0. See `LICENSE`.

## Proof status

`docs/theorems.md` maps every theorem of section 8 to the Lean statements that prove it and lists what each one assumes; `scripts/print-statements.sh` prints those statements without their proofs.

The theorems are stated in section 8 of the design spec (`docs/design.md`). Where section 8's assumptions restrict a theorem to actions in `enforce` mode (for theorem 8's step limit, a policy-level `enforce` mode), its proof carries that hypothesis; the others carry none.

| # | Theorem | Status |
|---|---|---|
| 1 | Consent | proved: `consent_claim` in `WritProofs/ConsentClaim.lean`, from `consent` (`WritProofs/Consent.lean`), `approvals` and `no_reject_before_claim` (`WritProofs/Approvals.lean`); the recorded consent it reads is, for an enforced call proposed Authorized or Awaiting, the effective consent at propose joined with every edit's (`consent_recorded_propose`, `recorded_by_propose`, `consent_recorded` in `WritProofs/ConsentClaim.lean`); the grant fields and escalators it reads are those the grant_create and propose events carried (`grant_origin` in `WritProofs/Grants.lean`, `call_origin` in `WritProofs/Origin.lean`, `consent_claim_fired` in `WritProofs/ConsentClaim.lean`); the attested approvers and the requester that eligibility reads are those the session_start and approver_attest events carried (`approver_origin`, `requester_origin` in `WritProofs/Approvers.lean`), and the request and authorization times its TTL reads are event times (`call_times` in `WritProofs/Times.lean`) |
| 2 | Grant accounting | proved: `grantInv_reachable`, `grant_uses`, `grant_cost`, `retry_no_use` in `WritProofs/Grants.lean`, with the limits they read those of the grant's grant_create event (`grant_origin` in `WritProofs/Grants.lean`), and a use returned by a call that ended without dispatch (cancelled, vetoed, denied at dispatch, killed, reset, ended with the session, or voided by a tombstone a ledger_sync brings in) taken off the grant's reserved uses (`grant_use_returned`, `grant_released_all` in `WritProofs/Reuse.lean`) |
| 3 | Permission | proved: `permission_propose`, `permission_claim`, `permission_origin` in `WritProofs/Permission.lean`, with every attested approver attested by a session_start or approver_attest event (`approver_origin` in `WritProofs/Approvers.lean`) |
| 4 | At most once | proved: `at_most_once`, `retry_after_unknown` in `WritProofs/AtMostOnce.lean` |
| 5 | Terminal absorption | proved: `terminal_absorbing` in `WritProofs/Lifecycle.lean` and `calls_keep` in `WritProofs/Calls.lean` |
| 6 | Epoch and freshness | proved: `claim_epoch`, `approve_fresh`, `claim_authorized_ttl` in `WritProofs/Lifecycle.lean`, with the authorization time it reads kept by every later step, retries included (`claim_keeps_authorizedAt`, `authorizedAt_kept` in `WritProofs/Lifecycle.lean`), and both TTLs measured from the times of the events that requested approval and authorized the call (`call_times`, `approve_fresh_event`, `claim_authorized_ttl_event` in `WritProofs/Times.lean`) |
| 7 | Kill | proved: `kill`, `no_claim_tombstone` in `WritProofs/Kill.lean` |
| 8 | Bounds | proved: limits (`proposals_per_turn`, `proposals_per_session`, `approvals_per_turn`, `approvals_per_session`, `steps_per_turn` in `WritProofs/Limits.lean`), meter caps and max_per_call (`meter_cap`, `meter_room`, `meter_room_retry`, `no_claim_over_cap`, `meter_per_call` in `WritProofs/Meters.lean`; `meter_cap_retry`, `meter_reuse`, `reserved_per_call` in `WritProofs/Accounting.lean`), overruns (`overrun_fails` in `WritProofs/Meters.lean`; `over_cap_only_by` in `WritProofs/Accounting.lean`; `overrun_commits_actual`, `overrun_verdict`, `report_commits_actual`, `report_commits_calls` in `WritProofs/Reports.lean`) and the accounting invariant for the session's own entries (`accounting_reachable`, `committed_stays`, `settle_commits` in `WritProofs/Accounting.lean`), which are all of a session-scope meter's entries (`session_entries_own`, `accounting_session` in `WritProofs/Reports.lean`); several sessions are theorem 9 |
| 9 | Ledger | proved, including sessions of different policies that agree on each shared principal meter and a tombstone set or cleared out of band: `interleave_reachable`, `ledger_cap`, `ledger_kill`, `ledger_kill_event`, `ledger_kill_stored`, `multi_reachable`, `multi_cap`, `multi_kill`, `multi_kill_event`, `multi_window`, `multi_cleared`, `claim_stored`, `multi_window_ordered`, `multi_kill_after` in `WritProofs/Interleave.lean`; pruning is proved safe for every later commit when the sessions share the trusted monotone clock (`multi_window_ordered`), and under clock skew a session whose clock runs ahead may prune an entry that a session behind it still counts |
| 10 | Default deny | proved: `default_deny_claim`, `default_deny_propose`, `default_deny_status` and `denyInv_reachable` (no stored call ever has an undefined tool) in `WritProofs/DefaultDeny.lean` |
| 11 | Escalation | proved: `escalationInv_reachable`, `blocked_propose`, `blocked_claim`, `unblock` in `WritProofs/Escalation.lean`, with the counters it reads raised by each failed result and each accepted outcome_unknown (`failed_fails` in `WritProofs/Escalation.lean`) and each overrun (`overrun_fails` in `WritProofs/Meters.lean`), and changed by no other step except a success, which resets its tool's counter, and the acknowledgment, which resets the failure counters (`failure_total_step`, `failure_tool_step`, `escalations_step` in `WritProofs/Reports.lean`), and the approvers it reads attested by session_start or approver_attest events (`approver_origin` in `WritProofs/Approvers.lean`) |
| 12 | Rejection memory | proved: `reject_records`, `memory_persists`, `rejected_propose`, `rejected_approve`, `rejected_claim`, `memory_origin`, `rejected_until_user_turn` in `WritProofs/Rejection.lean`, with the record digests the memory holds tied to the events that carried them (`call_origin`, `generation_recorded` in `WritProofs/Origin.lean`) |
| 13 | Expansion soundness | proved: `expand_check` (by construction of the layer-2 check), `expand_actions`, `expand_explicit`, `expand_rule`, `expand_rule_resolved`, `expand_rule_checked`, `expand_mono`, `expand_mono_resolved`, `expand_mono_checked`, `expand_parent`, `expand_parent_checked` in `WritProofs/Expand.lean`; where they compare a file's labels they assume label orders that list no value twice, and `expand_parent` no label dimension declared with two different orders, both layer-2 check problems, so `expand_rule_checked`, `expand_mono_checked` and `expand_parent_checked` assume only that the layer-2 check reports no problem; the lattice laws of every field's join are in `WritProofs/Join.lean` |

Supporting results, also from section 8:

- Frame lemma: `frame` in `WritProofs/Basic.lean`.
- Characterization: `dispatch_accepted_iff` and `dispatch_claimed_iff` in `WritProofs/Dispatch.lean`, and one `accepted_iff_*` theorem for each other event kind (22) in `WritProofs/Accept.lean`.
- Witness traces: for each reason code, each disposition (every decision and every call status) and each shadow kind, a trace reaching it, all checked by kernel evaluation (`decide +kernel`) in `WritProofs/Witness.lean`, where a proof by cases on the Reason, Decision, CallStatus and Shadow types checks that every constructor has one.
- Policy check soundness for degenerate limits: `Policy.WF.facts` in `WritProofs/WF.lean`.
- Origin independence (`origin_independent`), monotone time and seq (`accepted_seq_time`, `trace_seq_time`) and the well-formedness invariant (`wellFormed_reachable`) in `WritProofs/Support.lean`.
- Beyond section 8, for the MCP SEP-2848 profile of section 13: under a policy with no `mcp-tool-approval` profile error, no dispatch of a call whose outcome is unknown is accepted (`profile_unknown_final` in `WritProofs/Profile.lean`).
