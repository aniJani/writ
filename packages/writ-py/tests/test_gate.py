"""The gate suite, ported from packages/writ/test/gate-suite.ts and gate.test.ts, one test per TypeScript test
under the same name. The TypeScript tests that hold a commit on a deferred promise to force an interleaving use
`Probe.hold_next` here: the held commit runs the other writer's whole call before it reaches the store."""

from __future__ import annotations

import hashlib
import json
import threading
import time
from collections.abc import Callable, Mapping
from dataclasses import replace
from types import MappingProxyType
from typing import Any, Generic, TypeVar, cast

import pytest
from helpers import REPO, compact, fixture, input_error

from writ import (
    Approver,
    Commit,
    Cost,
    Edit,
    Gate,
    GateResult,
    LedgerCommit,
    LedgerRecord,
    PrincipalKillResult,
    ProposeResult,
    Store,
    Stored,
    WritConflictError,
    WritInputError,
    WritPolicyChangedError,
    WritStateFullError,
    WritStoreError,
    canonicalize,
    create_gate,
    default_idempotency_key,
    load_kernel,
)
from writ.gate import Clock, KernelLike, _clamp_untrusted, propose_kind
from writ.store import CommitOutcome, LedgerCommitOutcome
from writ.types import StepResult

T = TypeVar("T")
Make = Callable[[], Store]

kernel = load_kernel()


class Held(Generic[T]):
    def __init__(self, during: Callable[[], T]) -> None:
        self.during = during
        self.ran = False
        self._value: T | None = None

    def run(self) -> None:
        self._value = self.during()
        self.ran = True

    @property
    def value(self) -> T:
        assert self.ran, "the held commit was never reached"
        return cast(T, self._value)


class Probe:
    """Counts commits and can hold the next one while another writer runs, to force an interleaving."""

    def __init__(self, inner: Store) -> None:
        self.inner = inner
        self.commits = 0
        self._held: Held[Any] | None = None

    @property
    def max_state_bytes(self) -> int | None:
        limit: int | None = getattr(self.inner, "max_state_bytes", None)
        return limit

    def load(self, session_id: str) -> Stored | None:
        return self.inner.load(session_id)

    def load_ledger(self, principal: str) -> LedgerRecord | None:
        return self.inner.load_ledger(principal)

    def commit_ledger(self, c: LedgerCommit) -> LedgerCommitOutcome:
        return self.inner.commit_ledger(c)

    def commit(self, c: Commit) -> CommitOutcome:
        self.commits += 1
        h = self._held
        if h is not None:
            self._held = None
            h.run()
        return self.inner.commit(c)

    def hold_next(self, during: Callable[[], T]) -> Held[T]:
        """The next commit first runs `during` to its end, then reaches the store."""
        h = Held(during)
        self._held = h
        return h


class Wrap:
    """A store that forwards to `inner` except where a replacement is given."""

    def __init__(self, inner: Store, *, load: Callable[[str], Stored | None] | None = None,
                 load_ledger: Callable[[str], LedgerRecord | None] | None = None,
                 commit: Callable[[Commit], CommitOutcome] | None = None,
                 commit_ledger: Callable[[LedgerCommit], LedgerCommitOutcome] | None = None,
                 max_state_bytes: int | None = None) -> None:
        self.load = inner.load if load is None else load
        self.load_ledger = inner.load_ledger if load_ledger is None else load_ledger
        self.commit = inner.commit if commit is None else commit
        self.commit_ledger = inner.commit_ledger if commit_ledger is None else commit_ledger
        self.max_state_bytes = max_state_bytes


def ledger_first(inner: Store) -> Store:
    """Reports a ledger conflict before a state conflict, an order `Store` allows."""

    def commit(c: Commit) -> CommitOutcome:
        rec = inner.load_ledger(c.principal)
        if (None if rec is None else rec.version) != c.expected_ledger_version:
            return "ledger_conflict"
        return inner.commit(c)

    return Wrap(inner, commit=commit)


def limited(inner: Store, max_state_bytes: int) -> Store:
    """A store that reports a byte limit of its own."""
    return Wrap(inner, max_state_bytes=max_state_bytes)


class StubKernel:
    """The real kernel with `step` replaced."""

    def __init__(self, step: Callable[[str, str, Mapping[str, Any]], StepResult]) -> None:
        self.step = step

    def __getattr__(self, name: str) -> Any:
        return getattr(kernel, name)


def stub(step: Callable[[str, str, Mapping[str, Any]], StepResult]) -> KernelLike:
    return cast(KernelLike, StubKernel(step))


def loaded(store: Store, session_id: str) -> Stored:
    s = store.load(session_id)
    assert s is not None
    return s


def ledger_of(store: Store, principal: str = "u1") -> LedgerRecord:
    rec = store.load_ledger(principal)
    assert rec is not None
    return rec


def state(store: Store, session_id: str) -> dict[str, Any]:
    s: dict[str, Any] = json.loads(loaded(store, session_id).state)
    return s


def entries(store: Store, *fields: str) -> list[tuple[Any, ...]]:
    return [tuple(e[f] for f in fields) for e in json.loads(ledger_of(store).text)["entries"]]


def utf8_bytes(s: str) -> int:
    return len(s.encode("utf-8"))


def reason(r: GateResult) -> str | None:
    v = r.verdict
    return str(v["reason"]) if v["verdict"] == "rejected" else None


def decision(r: GateResult) -> str | None:
    v = r.verdict
    return str(v["decision"]) if v["verdict"] == "accepted" and "decision" in v else None


def denied_reason(r: GateResult) -> str | None:
    return str(r.verdict["reason"]) if decision(r) == "denied" else None


def lost_race(v: dict[str, Any]) -> bool:
    return v["verdict"] == "rejected" or (v.get("decision") == "existing" and v["status"] == "dispatched")


def needs_request_id(r: GateResult) -> dict[str, Any]:
    assert decision(r) == "needs_approval", r.verdict
    rid: dict[str, Any] = r.verdict["request_id"]
    return rid


WEB_CHAT: dict[str, Any] = json.loads(
    (REPO / "corpus/examples/web-chat.jsonl").read_text(encoding="utf-8").split("\n")[0])

OPEN = compact({
    "writ": "0.1",
    "approver_roles": ["owner"],
    "limits": {"approval_ttl_ms": 600000},
    "actions": {
        "search": {"consent": "none"},
        "buy": {"consent": "per_call", "grantable": {"scope": "session", "max_uses": 5}},
    },
})

CALLS = compact({
    "writ": "0.1",
    "meters": {"calls": {"unit": "calls", "cap": 1, "scope": "principal", "window_ms": 86400000}},
    "actions": {"ping": {"meters": ["calls"]}},
})

SPEND = compact({
    "writ": "0.1",
    "meters": {"spend": {"currency": "USD", "cap": 5000, "scope": "principal", "window_ms": 86400000}},
    "actions": {"buy": {"meters": ["spend"]}},
})

PINGS = compact({
    "writ": "0.1",
    "meters": {"calls": {"unit": "calls", "cap": 10, "scope": "principal", "window_ms": 86400000}},
    "actions": {"ping": {"meters": ["calls"]}},
})

LIFETIME = compact({
    "writ": "0.1",
    "meters": {"calls": {"unit": "calls", "cap": 1, "scope": "principal"}},
    "actions": {"ping": {"consent": "none", "meters": ["calls"]}},
})

RETRY = compact({
    "writ": "0.1",
    "actions": {"ping": {"consent": "none", "idempotent": True, "retry_after_unknown": True, "max_attempts": 3}},
})

OWNER: dict[str, Approver] = {"owner": {"principal": "u2", "kind": "human", "roles": ["owner"]}}


def ticking(start: int = 1000) -> Clock:
    t = [start]

    def clock() -> int:
        t[0] += 10
        return t[0]

    return clock


def gate_for(policy_text: str, store: Store, **over: Any) -> Gate:
    opts: dict[str, Any] = {"kernel": kernel, "policy_text": policy_text, "store": store, "clock": ticking(), **over}
    return create_gate(**opts)


def opened(gate: Gate, session_id: str, requester: str = "u1") -> None:
    r = gate.start(session_id, requester=requester, permissions=[], approvers=OWNER, user_initiated=True)
    assert r.verdict["verdict"] == "accepted"
    assert r.state_version == 2


def bad_clock(v: object) -> Clock:
    return cast(Clock, lambda: v)


def via_gate(gate: Gate, e: dict[str, Any]) -> GateResult:
    sid = "s1"
    t = e["type"]
    if t == "session_start":
        return gate.start(e["session_id"], requester=e["requester"], permissions=e["permissions"],
                          approvers=e["approvers"])
    if t == "turn_start":
        return gate.turn_start(sid, e["user_initiated"])
    if t == "turn_end":
        return gate.turn_end(sid)
    if t == "step_start":
        return gate.step_start(sid)
    if t == "propose":
        return gate.propose(sid, call_id=e["call_id"], tool=e["tool"], call_digest=e["call_digest"],
                            cost=e.get("cost"), guards=e.get("guards"), escalators=e.get("escalators"))
    if t == "approve":
        return gate.approve(sid, call_id=e["call_id"], request_id=e["request_id"], approver_id=e["approver"],
                            reviewed_digest=e["reviewed_digest"], reviewed_cost=e.get("reviewed_cost"))
    if t == "dispatch":
        return gate.dispatch(sid, call_id=e["call_id"], attempt=e.get("attempt"), call_digest=e["call_digest"],
                             cost=e.get("cost"), guards=e.get("guards"), idempotency_key=e.get("idempotency_key"))
    if t == "result":
        return gate.result(sid, call_id=e["call_id"], outcome=e["outcome"], actual_cost=e.get("actual_cost"),
                           no_effect=e.get("no_effect"))
    raise AssertionError(f"no gate method in this test for {t}")


def test_a_full_lifecycle_gives_the_web_chat_traces_verdicts(make: Make) -> None:
    store = make()
    now = [0]
    gate = create_gate(kernel=kernel, policy_text=compact(WEB_CHAT["policy"]), store=store, clock=lambda: now[0])
    for i, step in enumerate(WEB_CHAT["events"]):
        e, expect = step["event"], step["expect"]
        now[0] = e["time"]
        r = via_gate(gate, e)
        for k, v in expect.items():
            assert k in r.verdict and r.verdict[k] == v, f"step {i} {k}"
        assert r.state_version == i + 1
    s = state(store, "s1")
    assert s["last_seq"] == len(WEB_CHAT["events"])
    assert s["calls"]["c3"]["status"] == "succeeded"


def test_a_clock_that_goes_back_still_gives_an_accepted_event_at_the_last_time(make: Make) -> None:
    store = make()
    times = [5000, 4000, 4000]
    gate = create_gate(kernel=kernel, policy_text=OPEN, store=store, clock=lambda: times.pop(0))
    gate.start("s1", requester="u1", permissions=[], approvers=OWNER)
    r = gate.turn_start("s1", True)
    assert r.verdict["verdict"] == "accepted"
    assert state(store, "s1")["last_time"] == 5000
    assert gate.step_start("s1").verdict["verdict"] == "accepted"
    assert state(store, "s1")["last_time"] == 5000


def test_the_default_clock_is_integer_milliseconds_and_a_fractional_clock_is_refused(make: Make) -> None:
    store = make()
    before = time.time_ns() // 1_000_000
    create_gate(kernel=kernel, policy_text=OPEN, store=store).start(
        "s1", requester="u1", permissions=[], approvers=OWNER)
    t = state(store, "s1")["last_time"]
    assert isinstance(t, int) and before <= t <= time.time_ns() // 1_000_000
    # Python adaptation: a float with an integral value is that int, as Kernel.inspect takes its time.
    whole = create_gate(kernel=kernel, policy_text=OPEN, store=make(), clock=bad_clock(1000.0))
    whole.start("s1", requester="u1", permissions=[], approvers=OWNER)
    t = state(whole._store, "s1")["last_time"]
    assert t == 1000 and type(t) is int
    # A bool, a str, an unsafe integer and a float that is not finite are refused too.
    for v in (1.5, True, "1000", 2**53, 2.0**53, float("inf"), float("nan")):
        bad = create_gate(kernel=kernel, policy_text=OPEN, store=make(), clock=bad_clock(v))
        with pytest.raises(TypeError, match="expected integer milliseconds"):
            bad.start("s1", requester="u1", permissions=[], approvers=OWNER)


def test_a_rejected_event_leaves_the_store_byte_identical_and_does_not_commit(make: Make) -> None:
    probe = Probe(make())
    gate = gate_for(OPEN, probe)
    opened(gate, "s1")
    before = probe.load("s1")
    commits = probe.commits
    r = gate.dispatch("s1", call_id="nope", attempt=1, call_digest="d", idempotency_key="k")
    assert r.verdict["verdict"] == "rejected"
    assert reason(r) == "unknown_call"
    assert r.state_version == 2
    assert probe.commits == commits
    assert probe.load("s1") == before
    assert probe.load_ledger("u1") is None


def test_an_event_on_a_session_that_was_never_started_is_rejected_without_a_commit(make: Make) -> None:
    probe = Probe(make())
    r = gate_for(OPEN, probe).turn_start("missing", True)
    assert reason(r) == "not_started"
    assert probe.commits == 0
    assert probe.load("missing") is None


def test_a_second_start_of_a_session_is_rejected_and_changes_nothing(make: Make) -> None:
    probe = Probe(make())
    gate = gate_for(OPEN, probe)
    opened(gate, "s1")
    before = probe.load("s1")
    commits = probe.commits
    r = gate.start("s1", requester="u9", permissions=[], approvers={})
    assert reason(r) == "already_started"
    assert probe.commits == commits
    assert probe.load("s1") == before


def test_a_kernel_input_error_leaves_the_store_untouched(make: Make) -> None:
    probe = Probe(make())
    with input_error("policy_text"):
        gate_for(fixture("policies/errors.json"), probe)
    with input_error("policy_text"):
        gate_for("{", probe)
    assert probe.commits == 0

    gate = gate_for(SPEND, probe)
    opened(gate, "s2")
    before = probe.load("s2")
    commits = probe.commits
    with input_error("event"):
        gate.propose("s2", call_id="c1", tool="buy", call_digest="d", cost={"amount": "1.5", "currency": "USD"})
    assert probe.commits == commits
    assert probe.load("s2") == before


def test_a_webassembly_trap_surfaces_as_an_error_without_a_commit(make: Make) -> None:
    probe = Probe(make())
    opened(gate_for(OPEN, probe), "s1")
    before = probe.load("s1")
    commits = probe.commits
    trap = RuntimeError("RuntimeError: unreachable")

    def step(policy_text: str, state_text: str, event: Mapping[str, Any]) -> StepResult:
        raise trap

    gate = create_gate(kernel=stub(step), policy_text=OPEN, store=probe)
    with pytest.raises(RuntimeError) as e:
        gate.step_start("s1")
    assert e.value is trap
    assert probe.commits == commits
    assert probe.load("s1") == before


def test_a_session_is_never_stepped_under_a_different_policy(make: Make) -> None:
    probe = Probe(make())
    opened(gate_for(OPEN, probe), "s1")
    before = probe.load("s1")
    commits = probe.commits
    other = gate_for(SPEND, probe)
    calls: list[Callable[[], object]] = [
        lambda: other.step_start("s1"),
        lambda: other.end("s1"),
        lambda: other.kill("s1"),
        lambda: other.start("s1", requester="u1", permissions=[], approvers={}),
        lambda: other.inspect("s1"),
    ]
    for call in calls:
        with pytest.raises(WritPolicyChangedError) as e:
            call()
        assert e.value.session_id == "s1" and e.value.policy_digest == kernel.digest(OPEN)
    assert probe.commits == commits
    assert probe.load("s1") == before


def test_start_puts_the_stored_principal_ledger_and_the_policy_digest_in_session_start(make: Make) -> None:
    store = make()
    gate = gate_for(CALLS, store)
    opened(gate, "s1")
    gate.propose("s1", call_id="c1", tool="ping", call_digest="d")
    gate.dispatch("s1", call_id="c1", attempt=1, call_digest="d", idempotency_key="k1")
    ledger = ledger_of(store)
    assert ledger.version > 0
    opened(gate, "s2")
    s2 = state(store, "s2")
    assert compact(s2["ledger"]) == ledger.text
    assert s2["policy_digest"] == kernel.digest(CALLS)
    assert s2["requester"] == "u1"
    r = gate.propose("s2", call_id="c1", tool="ping", call_digest="d")
    assert r.kind == "denied"
    assert denied_reason(r) == "meter_exceeded"


def test_two_gates_proposing_on_one_session_both_land_one_after_the_other(make: Make) -> None:
    probe = Probe(make())
    a = gate_for(OPEN, probe)
    b = gate_for(OPEN, probe)
    opened(a, "s1")
    v0 = loaded(probe, "s1").state_version
    held = probe.hold_next(lambda: b.propose("s1", call_id="cb", tool="search", call_digest="db"))
    ra = a.propose("s1", call_id="ca", tool="search", call_digest="da")
    rb = held.value
    assert rb.kind == "allowed"
    assert ra.kind == "allowed"
    assert rb.state_version == v0 + 1
    assert ra.state_version == v0 + 2
    s = state(probe, "s1")
    assert sorted(s["calls"]) == ["ca", "cb"]
    assert s["state_version"] == v0 + 2
    assert loaded(probe, "s1").state_version == v0 + 2
    # B's commit, A's lost commit, A's retried commit.
    assert probe.commits == 2 + 3


def test_two_gates_racing_to_dispatch_one_call_claim_it_once(make: Make) -> None:
    probe = Probe(make())
    a = gate_for(OPEN, probe)
    b = gate_for(OPEN, probe)
    opened(a, "s1")
    a.propose("s1", call_id="c1", tool="search", call_digest="d1")
    dispatch: dict[str, Any] = {"call_id": "c1", "attempt": 1, "call_digest": "d1", "idempotency_key": "k-s1-c1"}
    held = probe.hold_next(lambda: b.dispatch("s1", **dispatch))
    ra = a.dispatch("s1", **dispatch)
    rb = held.value
    assert decision(rb) == "dispatch_claimed"
    assert decision(ra) != "dispatch_claimed"
    lost = ra.verdict
    assert lost_race(lost), lost
    s = state(probe, "s1")
    assert s["calls"]["c1"]["attempts"] == 1
    assert s["calls"]["c1"]["status"] == "dispatched"


def test_two_sessions_of_one_principal_share_a_calls_meter_of_1_one_claim_then_meter_exceeded_after_ledger_sync(
        make: Make) -> None:
    probe = Probe(make())
    g1 = gate_for(CALLS, probe)
    g2 = gate_for(CALLS, probe)
    opened(g1, "s1")
    opened(g2, "s2")
    assert g1.propose("s1", call_id="c1", tool="ping", call_digest="d").kind == "allowed"
    assert g2.propose("s2", call_id="c1", tool="ping", call_digest="d").kind == "allowed"

    def d(sid: str) -> dict[str, Any]:
        return {"call_id": "c1", "attempt": 1, "call_digest": "d", "idempotency_key": f"k-{sid}-c1"}

    held = probe.hold_next(lambda: g2.dispatch("s2", **d("s2")))
    r1 = g1.dispatch("s1", **d("s1"))
    r2 = held.value
    assert decision(r2) == "dispatch_claimed"
    assert reason(r1) == "meter_exceeded"
    ledger = ledger_of(probe)
    s1 = state(probe, "s1")
    assert s1["ledger"]["version"] == ledger.version
    assert compact(s1["ledger"]) == ledger.text
    assert s1["calls"]["c1"]["status"] == "authorized"
    assert entries(probe, "session") == [("s2",)]


def test_a_ledger_that_can_no_longer_be_reconciled_ends_the_session(make: Make) -> None:
    store = make()
    gate = gate_for(CALLS, store)
    opened(gate, "s1")
    gate.propose("s1", call_id="c1", tool="ping", call_digest="d")
    gate.dispatch("s1", call_id="c1", attempt=1, call_digest="d", idempotency_key="k")
    stored = ledger_of(store)
    # An out-of-band clear: a newer ledger without this session's entry.
    cleared = LedgerRecord(f'{{"version":{stored.version + 5}}}', stored.version + 5)
    assert store.commit(Commit(session_id="admin", state="{}", state_version=1, expected_state_version=None,
                               principal="u1", ledger=cleared, expected_ledger_version=stored.version)) == "ok"
    r = gate.result("s1", call_id="c1", outcome="succeeded")
    assert reason(r) == "ledger_conflict"
    s = state(store, "s1")
    assert s["ended"] is True
    assert r.state_version == s["state_version"]
    assert store.load_ledger("u1") == cleared


def test_with_ledger_scope_none_the_gate_never_reads_or_writes_principal_ledgers(make: Make) -> None:
    inner = make()
    ledger_reads = [0]

    def load_ledger(p: str) -> LedgerRecord | None:
        ledger_reads[0] += 1
        return inner.load_ledger(p)

    def commit_ledger(c: LedgerCommit) -> LedgerCommitOutcome:
        raise AssertionError("commit_ledger under ledger_scope none")

    def commit(c: Commit) -> CommitOutcome:
        assert c.ledger is None
        assert c.expected_ledger_version is None
        return inner.commit(c)

    store = Wrap(inner, load_ledger=load_ledger, commit_ledger=commit_ledger, commit=commit)
    gate = gate_for(CALLS, store, ledger_scope="none")
    for sid in ("s1", "s2"):
        opened(gate, sid)
        gate.propose(sid, call_id="c1", tool="ping", call_digest="d")
        r = gate.dispatch(sid, call_id="c1", attempt=1, call_digest="d", idempotency_key="k")
        assert decision(r) == "dispatch_claimed"
    assert ledger_reads[0] == 0
    assert inner.load_ledger("u1") is None


def test_with_ledger_scope_none_a_stored_principal_ledger_fails_closed(make: Make) -> None:
    store = make()
    full = gate_for(CALLS, store)
    opened(full, "s1")
    full.propose("s1", call_id="c1", tool="ping", call_digest="d")
    full.dispatch("s1", call_id="c1", attempt=1, call_digest="d", idempotency_key="k")
    none = gate_for(CALLS, store, ledger_scope="none")
    with pytest.raises(WritConflictError):
        none.start("s2", requester="u1", permissions=[], approvers={})
    assert store.load("s2") is None


def test_a_store_that_always_conflicts_gives_writ_conflict_error_after_5_attempts(make: Make) -> None:
    inner = make()
    opened(gate_for(OPEN, inner), "s1")
    commits = [0]

    def commit(c: Commit) -> CommitOutcome:
        commits[0] += 1
        return "state_conflict"

    with pytest.raises(WritConflictError):
        gate_for(OPEN, Wrap(inner, commit=commit)).step_start("s1")
    assert commits[0] == 5


def test_store_errors_propagate_unchanged(make: Make) -> None:
    inner = make()
    opened(gate_for(OPEN, inner), "s1")
    boom = WritStoreError("store down")

    def fail(*_: object) -> Any:
        raise boom

    failing = Wrap(inner, commit_ledger=fail, commit=fail)
    with pytest.raises(Exception) as e:
        gate_for(OPEN, failing).step_start("s1")
    assert e.value is boom
    load_fails = Wrap(inner, load=fail, commit_ledger=fail, commit=fail)
    with pytest.raises(Exception) as e:
        gate_for(OPEN, load_fails).step_start("s1")
    assert e.value is boom
    with pytest.raises(Exception) as e:
        gate_for(OPEN, failing).kill_principal("u1")
    assert e.value is boom


def test_an_untrusted_declined_report_is_recorded_as_failed(make: Make) -> None:
    store = make()
    gate = gate_for(OPEN, store)
    opened(gate, "s1")
    for cid, trusted_decline, want in (("c1", False, "failed"), ("c2", True, "declined")):
        gate.propose("s1", call_id=cid, tool="search", call_digest=cid)
        gate.dispatch("s1", call_id=cid, attempt=1, call_digest=cid, idempotency_key=f"k-{cid}")
        r = gate.result("s1", call_id=cid, outcome="declined", untrusted=True, trusted_decline=trusted_decline)
        assert r.verdict["verdict"] == "accepted"
        assert state(store, "s1")["calls"][cid]["status"] == want


def test_trusted_decline_counts_only_when_it_is_true(make: Make) -> None:
    # Python only: TS checks `trustedDecline === true`, so a truthy value that is not True is no trusted decline.
    store = make()
    gate = gate_for(OPEN, store)
    opened(gate, "s1")
    for cid, flag in (("c1", "no"), ("c2", 1)):
        gate.propose("s1", call_id=cid, tool="search", call_digest=cid)
        gate.dispatch("s1", call_id=cid, attempt=1, call_digest=cid)
        r = gate.result("s1", call_id=cid, outcome="declined", untrusted=True, trusted_decline=flag)  # type: ignore[arg-type]
        assert r.verdict["verdict"] == "accepted"
        assert state(store, "s1")["calls"][cid]["status"] == "failed"
    assert _clamp_untrusted({"type": "result", "outcome": "declined"}, cast(bool, "no"), None)["outcome"] == "failed"


def test_mappings_and_sequences_are_copied_and_a_bare_str_is_refused(make: Make) -> None:
    # Python only: canonicalize takes only dicts and lists, so the gate copies any Mapping and sequence of strings.
    probe = Probe(make())
    gate = gate_for(OPEN, probe)
    approvers = MappingProxyType({"owner": MappingProxyType({"principal": "u2", "kind": "human", "roles": ("owner",)})})
    r = gate.start("s1", requester="u1", permissions=("p.read",), approvers=approvers,  # type: ignore[arg-type]
                   user_initiated=True)
    assert r.verdict["verdict"] == "accepted", r.verdict
    s = state(probe, "s1")
    assert s["approvers"]["owner"]["roles"] == ["owner"]
    flags = MappingProxyType({"ok": True})
    cost = MappingProxyType({"amount": "1", "currency": "USD"})
    p = gate.propose("s1", call_id="c1", tool="buy", call_digest="d1", guards=flags, escalators=flags)
    assert p.kind == "needs_approval", p.verdict
    rid = MappingProxyType(needs_request_id(p))
    edit: Edit = {"new_digest": "d2", "escalators": MappingProxyType({"x": False})}
    a = gate.approve("s1", call_id="c1", request_id=rid, approver_id="owner", reviewed_digest="d1", edit=edit)
    assert a.verdict["verdict"] == "accepted", a.verdict
    p2 = gate.propose("s1", call_id="c2", tool="buy", call_digest="d3")
    assert gate.reject("s1", call_id="c2", request_id=MappingProxyType(needs_request_id(p2)),
                       approver_id="owner").verdict["verdict"] == "accepted"
    p3 = gate.propose("s1", call_id="c3", tool="buy", call_digest="d4")
    assert gate.approval_expire("s1", call_id="c3", request_id=MappingProxyType(needs_request_id(p3))).verdict[
        "verdict"] == "accepted"
    gate.propose("s1", call_id="c4", tool="search", call_digest="d5")
    assert gate.dispatch("s1", call_id="c4", call_digest="d5", guards=flags).claimed is True
    g = gate.grant_create("s1", grant_id="g1", approver_id="owner", tool="buy", scope="session", max_uses=1,
                          reviewed_scope_digest="rs", max_cost=cost)  # type: ignore[arg-type]
    # The kernel's grant rule refuses a cost limit on an action without a money meter: the event was decoded.
    assert reason(g) == "grant_not_allowed", g.verdict
    assert gate.approver_attest("s1", approver_id="bot", principal="svc", kind="automated",
                                roles=("owner",)).verdict["verdict"] == "accepted"

    before = probe.load("s1")
    commits = probe.commits
    with input_error("roles"):
        gate.approver_attest("s1", approver_id="bot2", principal="svc", kind="automated", roles="owner")
    with input_error("permissions"):
        gate.start("s2", requester="u1", permissions="p.read", approvers={})
    with input_error("approvers.owner.roles"):
        gate.start("s2", requester="u1", permissions=[],
                   approvers={"owner": {"principal": "u2", "kind": "human", "roles": "owner"}})
    assert probe.commits == commits
    assert probe.load("s1") == before
    assert probe.load("s2") is None


def test_an_untrusted_report_commits_at_least_the_reservation_and_never_releases(make: Make) -> None:
    store = make()
    gate = gate_for(SPEND, store)
    opened(gate, "s1")
    cost: Cost = {"amount": "1200", "currency": "USD"}
    for cid in ("c1", "c2"):
        gate.propose("s1", call_id=cid, tool="buy", call_digest=cid, cost=cost)
        gate.dispatch("s1", call_id=cid, attempt=1, call_digest=cid, cost=cost, idempotency_key=f"k-{cid}")
    gate.result("s1", call_id="c1", outcome="succeeded", actual_cost="100", no_effect=True, untrusted=True)
    gate.result("s1", call_id="c2", outcome="succeeded", actual_cost="100", no_effect=True)
    assert entries(store, "call", "amount", "committed") == [("c1", "1200", True)]


def test_propose_kind_maps_each_decision(make: Make) -> None:
    store = make()
    gate = gate_for(OPEN, store)
    opened(gate, "s1")

    def p(call_id: str, tool: str, call_digest: str | None = None) -> ProposeResult:
        return gate.propose("s1", call_id=call_id, tool=tool, call_digest=call_digest or call_id)

    assert p("c1", "search").kind == "allowed"
    needs = p("c2", "buy")
    assert needs.kind == "needs_approval"
    waiting = p("c2", "buy")
    assert waiting.kind == "needs_approval"
    assert waiting.request_id == needs.request_id and needs.request_id is not None
    assert p("c3", "wire_money").kind == "denied"
    assert p("c3", "wire_money").kind == "denied"
    assert p("c1", "buy").kind == "rejected"
    g = gate.grant_create("s1", grant_id="g1", approver_id="owner", tool="buy", call_digest="dg", scope="session",
                          max_uses=1, reviewed_scope_digest="rs")
    assert g.verdict["verdict"] == "accepted"
    by_grant = p("c4", "buy", "dg")
    assert decision(by_grant) == "allowed_by_grant"
    assert by_grant.kind == "allowed"
    gate.dispatch("s1", call_id="c1", attempt=1, call_digest="c1", idempotency_key="k1")
    in_flight = p("c1", "search")
    assert decision(in_flight) == "existing" and in_flight.verdict["status"] == "dispatched"
    assert in_flight.kind == "denied"
    gate.result("s1", call_id="c1", outcome="succeeded")
    assert p("c1", "search").kind == "denied"
    rid = needs_request_id(needs)
    gate.approve("s1", call_id="c2", request_id=rid, approver_id="owner", reviewed_digest="c2")
    again = p("c2", "buy")
    assert decision(again) == "authorized"
    assert again.kind == "allowed"


def test_the_other_gate_methods_build_accepted_events(make: Make) -> None:
    store = make()
    gate = gate_for(OPEN, store)
    gate.start("s1", requester="u1", permissions=[], approvers=OWNER)

    def ok(r: GateResult) -> None:
        assert r.verdict["verdict"] == "accepted", r.verdict

    ok(gate.turn_start("s1", True))
    ok(gate.step_start("s1"))
    ok(gate.approver_attest("s1", approver_id="bot", principal="svc", kind="automated", roles=["owner"]))
    ok(gate.permission_add("s1", permission="p.x", approver_id="owner"))
    ok(gate.permission_revoke("s1", "p.x"))
    ok(gate.grant_create("s1", grant_id="g1", approver_id="owner", tool="buy", call_digest="dg", scope="session",
                         max_uses=1, reviewed_scope_digest="rs"))
    ok(gate.grant_revoke("s1", "g1"))
    n = gate.propose("s1", call_id="c1", tool="buy", call_digest="d1")
    ok(gate.reject("s1", call_id="c1", request_id=needs_request_id(n), approver_id="owner"))
    m = gate.propose("s1", call_id="c2", tool="buy", call_digest="d2")
    ok(gate.approval_expire("s1", call_id="c2", request_id=needs_request_id(m)))
    gate.propose("s1", call_id="c3", tool="search", call_digest="d3")
    ok(gate.cancel("s1", "c3"))
    gate.propose("s1", call_id="c4", tool="search", call_digest="d4")
    gate.dispatch("s1", call_id="c4", attempt=1, call_digest="d4", idempotency_key="k4")
    ok(gate.outcome_unknown("s1", "c4"))
    ok(gate.reconcile("s1", call_id="c4", outcome="succeeded"))
    ok(gate.turn_end("s1"))
    ok(gate.reset("s1"))
    ok(gate.kill("s1"))
    ok(gate.end("s1"))
    s = state(store, "s1")
    assert s["ended"] is True
    assert s["killed"] is True
    assert s["calls"]["c4"]["status"] == "unknown"


def test_escalation_ack_goes_through_the_gate(make: Make) -> None:
    policy = compact({
        "writ": "0.1", "approver_roles": ["owner"], "escalation_roles": ["owner"],
        "limits": {"max_consecutive_failures": 1}, "actions": {"search": {}},
    })
    store = make()
    gate = gate_for(policy, store)
    opened(gate, "s1")
    gate.propose("s1", call_id="c1", tool="search", call_digest="d")
    gate.dispatch("s1", call_id="c1", attempt=1, call_digest="d", idempotency_key="k")
    gate.result("s1", call_id="c1", outcome="failed")
    s = state(store, "s1")
    assert s["escalations"] > 0
    r = gate.escalation_ack("s1", approver_id="owner", escalation=s["escalations"])
    assert r.verdict["verdict"] == "accepted", r.verdict
    assert state(store, "s1")["escalated"] is False


def test_a_store_that_reports_ledger_conflict_before_state_conflict_still_gives_one_claim_and_a_live_session(
        make: Make) -> None:
    probe = Probe(ledger_first(make()))
    a = gate_for(CALLS, probe)
    b = gate_for(CALLS, probe)
    opened(a, "s1")
    a.propose("s1", call_id="c1", tool="ping", call_digest="d1")
    dispatch: dict[str, Any] = {"call_id": "c1", "attempt": 1, "call_digest": "d1", "idempotency_key": "k-s1-c1"}
    held = probe.hold_next(lambda: b.dispatch("s1", **dispatch))
    ra = a.dispatch("s1", **dispatch)
    rb = held.value
    assert decision(rb) == "dispatch_claimed"
    lost = ra.verdict
    assert lost_race(lost), lost
    s = state(probe, "s1")
    assert s.get("ended") is not True
    assert s["calls"]["c1"]["status"] == "dispatched"
    assert s["calls"]["c1"]["attempts"] == 1
    assert entries(probe, "call") == [("c1",)]


def test_kill_principal_stops_a_sibling_sessions_dispatch(make: Make) -> None:
    store = make()
    gate = gate_for(PINGS, store)
    opened(gate, "A")
    opened(gate, "B")
    assert gate.propose("B", call_id="c1", tool="ping", call_digest="d").kind == "allowed"
    assert state(store, "B")["calls"]["c1"]["status"] == "authorized"
    assert gate.kill_principal("u1") == PrincipalKillResult(1, True)
    d = gate.dispatch("B", call_id="c1", attempt=1, call_digest="d")
    assert reason(d) == "killed", d.verdict
    b = state(store, "B")
    assert b["calls"]["c1"]["status"] == "cancelled"
    assert b["ledger"]["tombstone"] is True
    p = gate.propose("A", call_id="c1", tool="ping", call_digest="d")
    assert denied_reason(p) == "killed"
    assert "entries" not in json.loads(ledger_of(store).text)
    assert gate.kill_principal("u1") == PrincipalKillResult(1, False)


def test_kill_principal_on_a_principal_without_a_ledger(make: Make) -> None:
    store = make()
    gate = gate_for(CALLS, store)
    assert gate.clear_principal_kill("u9") == PrincipalKillResult(0, False)
    assert store.load_ledger("u9") is None
    assert gate.kill_principal("u9") == PrincipalKillResult(1, True)
    rec = ledger_of(store, "u9")
    assert rec.version == 1
    assert json.loads(rec.text)["tombstone"] is True
    gate.start("s1", requester="u9", permissions=[], approvers={}, user_initiated=True)
    p = gate.propose("s1", call_id="c1", tool="ping", call_digest="d")
    assert denied_reason(p) == "killed"


def test_kill_principal_and_clear_principal_kill_refuse_ledger_scope_none_and_give_up_after_5_conflicts(
        make: Make) -> None:
    inner = make()
    none = gate_for(CALLS, inner, ledger_scope="none")
    with input_error("ledger_scope"):
        none.kill_principal("u1")
    with input_error("ledger_scope"):
        none.clear_principal_kill("u1")
    assert inner.load_ledger("u1") is None
    tries = [0]

    def commit_ledger(c: LedgerCommit) -> LedgerCommitOutcome:
        tries[0] += 1
        return "ledger_conflict"

    with pytest.raises(WritConflictError):
        gate_for(CALLS, Wrap(inner, commit_ledger=commit_ledger)).kill_principal("u1")
    assert tries[0] == 5
    assert inner.load_ledger("u1") is None


def test_kill_principal_retries_against_a_ledger_that_moved(make: Make) -> None:
    probe = Probe(make())
    gate = gate_for(CALLS, probe)
    opened(gate, "s1")
    gate.propose("s1", call_id="c1", tool="ping", call_digest="d")
    outcomes: list[str] = []

    def commit_ledger(c: LedgerCommit) -> LedgerCommitOutcome:
        if not outcomes:
            gate.dispatch("s1", call_id="c1", attempt=1, call_digest="d")
        out = probe.commit_ledger(c)
        outcomes.append(out)
        return out

    r = gate_for(CALLS, Wrap(probe, commit_ledger=commit_ledger)).kill_principal("u1")
    assert outcomes == ["ledger_conflict", "ok"]
    stored = ledger_of(probe)
    assert r == PrincipalKillResult(stored.version, True)
    ledger = json.loads(stored.text)
    assert ledger["tombstone"] is True
    assert [e["call"] for e in ledger["entries"]] == ["c1"]


def test_clear_principal_kill_ends_live_sessions(make: Make) -> None:
    store = make()
    gate = gate_for(PINGS, store)
    opened(gate, "A")
    gate.kill_principal("u1")
    p = gate.propose("A", call_id="c1", tool="ping", call_digest="d")
    assert denied_reason(p) == "killed"
    assert gate.clear_principal_kill("u1") == PrincipalKillResult(2, True)
    r = gate.propose("A", call_id="c2", tool="ping", call_digest="d")
    assert reason(r) == "ledger_conflict", r.verdict
    assert state(store, "A")["ended"] is True
    opened(gate, "B")
    assert gate.propose("B", call_id="c1", tool="ping", call_digest="d").kind == "allowed"
    assert gate.clear_principal_kill("u1") == PrincipalKillResult(2, False)


def test_after_clear_principal_kill_an_ended_session_still_settles_its_unknown_call(make: Make) -> None:
    store = make()
    gate = gate_for(LIFETIME, store)
    opened(gate, "A")
    assert gate.propose("A", call_id="c1", tool="ping", call_digest="d").kind == "allowed"
    assert gate.dispatch("A", call_id="c1", call_digest="d").claimed is True
    gate.kill_principal("u1")
    assert gate.outcome_unknown("A", "c1").verdict["verdict"] == "accepted"
    gate.clear_principal_kill("u1")
    r = gate.reconcile("A", call_id="c1", outcome="succeeded", no_effect=True)
    assert r.verdict["verdict"] == "accepted", r.verdict
    a = state(store, "A")
    assert a["ended"] is True
    assert a["calls"]["c1"]["reconciled"] == "succeeded"
    ledger = json.loads(ledger_of(store).text)
    assert "tombstone" not in ledger
    assert "entries" not in ledger
    opened(gate, "B")
    assert gate.propose("B", call_id="c1", tool="ping", call_digest="d").kind == "allowed"


def killed_and_cleared(make: Make, policy_text: str, cost: Cost | None = None) -> tuple[Store, Gate]:
    """Session A has `c1` claimed and sees the principal killed, then the kill is cleared."""
    store = make()
    gate = gate_for(policy_text, store)
    opened(gate, "A")
    tool = "ping" if cost is None else "buy"
    assert gate.propose("A", call_id="c1", tool=tool, call_digest="d", cost=cost).kind == "allowed"
    assert gate.dispatch("A", call_id="c1", call_digest="d", cost=cost).claimed is True
    gate.kill_principal("u1")
    p = gate.propose("A", call_id="c2", tool=tool, call_digest="d", cost=cost)
    assert p.kind == "denied" and p.reason == "killed", p.verdict
    gate.clear_principal_kill("u1")
    return store, gate


def test_after_clear_principal_kill_a_live_sessions_result_settles_in_one_call(make: Make) -> None:
    store, gate = killed_and_cleared(make, PINGS)
    r = gate.result("A", call_id="c1", outcome="succeeded")
    assert r.verdict["verdict"] == "accepted", r.verdict
    a = state(store, "A")
    assert a["ended"] is True
    assert a["calls"]["c1"]["reconciled"] == "succeeded"
    assert "tombstone" not in json.loads(ledger_of(store).text)
    assert entries(store, "call", "committed") == [("c1", True)]


def test_the_resent_reconcile_keeps_the_untrusted_clamp(make: Make) -> None:
    store, gate = killed_and_cleared(make, SPEND, {"amount": "1200", "currency": "USD"})
    r = gate.result("A", call_id="c1", outcome="succeeded", actual_cost="100", no_effect=True, untrusted=True)
    assert r.verdict["verdict"] == "accepted", r.verdict
    assert state(store, "A")["ended"] is True
    assert entries(store, "call", "amount", "committed") == [("c1", "1200", True)]


def test_a_repeated_reconcile_after_the_resend_is_already_reconciled(make: Make) -> None:
    store, gate = killed_and_cleared(make, PINGS)
    assert gate.result("A", call_id="c1", outcome="succeeded").verdict["verdict"] == "accepted"
    version = ledger_of(store).version
    r = gate.reconcile("A", call_id="c1", outcome="succeeded")
    assert reason(r) == "already_reconciled", r.verdict
    assert ledger_of(store).version == version


def test_outcome_unknown_after_clear_principal_kill_is_not_resent(make: Make) -> None:
    store, gate = killed_and_cleared(make, PINGS)
    u = gate.outcome_unknown("A", "c1")
    assert reason(u) == "ledger_conflict", u.verdict
    a = state(store, "A")
    assert a["ended"] is True
    assert a["calls"]["c1"]["status"] == "unknown"
    r = gate.reconcile("A", call_id="c1", outcome="succeeded")
    assert r.verdict["verdict"] == "accepted", r.verdict


def test_after_the_gate_ends_a_session_its_other_dispatched_calls_settle_through_result(make: Make) -> None:
    store = make()
    gate = gate_for(PINGS, store)
    opened(gate, "A")
    for call_id in ("c1", "c2"):
        assert gate.propose("A", call_id=call_id, tool="ping", call_digest="d").kind == "allowed"
        assert gate.dispatch("A", call_id=call_id, call_digest="d").claimed is True
    gate.kill_principal("u1")
    p = gate.propose("A", call_id="c3", tool="ping", call_digest="d")
    assert p.kind == "denied" and p.reason == "killed", p.verdict
    gate.clear_principal_kill("u1")
    for call_id in ("c1", "c2"):
        r = gate.result("A", call_id=call_id, outcome="succeeded")
        assert r.verdict["verdict"] == "accepted", f"{call_id}: {r.verdict}"
    a = state(store, "A")
    assert a["ended"] is True
    assert a["calls"]["c2"]["reconciled"] == "succeeded"
    assert entries(store, "call", "committed") == [("c1", True), ("c2", True)]


def test_result_on_a_host_ended_session_settles_as_reconcile(make: Make) -> None:
    store = make()
    gate = gate_for(PINGS, store)
    opened(gate, "A")
    assert gate.propose("A", call_id="c1", tool="ping", call_digest="d").kind == "allowed"
    assert gate.dispatch("A", call_id="c1", call_digest="d").claimed is True
    assert gate.end("A").verdict["verdict"] == "accepted"
    r = gate.result("A", call_id="c1", outcome="succeeded")
    assert r.verdict["verdict"] == "accepted", r.verdict
    a = state(store, "A")
    assert a["ended"] is True
    assert a["calls"]["c1"]["reconciled"] == "succeeded"
    assert entries(store, "call", "committed") == [("c1", True)]


def test_a_result_resent_after_a_forced_end_is_not_resent_again(make: Make) -> None:
    store, _ = killed_and_cleared(make, PINGS)
    steps: list[str] = []

    # A reconcile is never session_ended in the real kernel, so the stub makes it one to show the resend stops.
    def step(policy_text: str, state_text: str, event: Mapping[str, Any]) -> StepResult:
        steps.append(event["type"])
        r = kernel.step(policy_text, state_text, event)
        if event["type"] != "reconcile":
            return r
        verdict = {"verdict": "rejected", "state_version": r.state_version, "reason": "session_ended",
                   "retry": "never", "message": "stub"}
        return replace(r, verdict=verdict, changed=False)

    gate = gate_for(PINGS, store, kernel=stub(step))
    r = gate.result("A", call_id="c1", outcome="succeeded")
    assert reason(r) == "session_ended", r.verdict
    assert steps == ["result", "ledger_sync", "session_end", "reconcile"]


def test_a_full_session_can_still_be_killed_ended_and_settled(make: Make) -> None:
    probe = Probe(make())
    roomy = gate_for(OPEN, probe)
    opened(roomy, "s1")
    roomy.propose("s1", call_id="c1", tool="search", call_digest="d1")
    roomy.dispatch("s1", call_id="c1", attempt=1, call_digest="d1")
    n = utf8_bytes(loaded(probe, "s1").state)
    limit = n + 128
    headroom = limit * 7 // 8
    assert n > headroom, f"{n} > {headroom}"
    full = gate_for(OPEN, probe, max_state_bytes=limit)
    before = probe.load("s1")
    commits = probe.commits
    refused: list[Callable[[], object]] = [
        lambda: full.propose("s1", call_id="c2", tool="search", call_digest="d2"),
        lambda: full.permission_add("s1", permission="p.x", approver_id="owner"),
        lambda: full.dispatch("s1", call_id="c1", attempt=2, call_digest="d1"),
    ]
    for call in refused:
        with pytest.raises(WritStateFullError) as e:
            call()
        assert e.value.session_id == "s1" and e.value.bytes == n and e.value.limit == headroom
    assert probe.commits == commits
    assert probe.load("s1") == before
    assert full.result("s1", call_id="c1", outcome="succeeded").verdict["verdict"] == "accepted"
    assert full.kill("s1").verdict["verdict"] == "accepted"
    assert full.end("s1").verdict["verdict"] == "accepted"
    s = state(probe, "s1")
    assert s["calls"]["c1"]["status"] == "succeeded"
    assert s["killed"] is True
    assert s["ended"] is True
    assert utf8_bytes(loaded(probe, "s1").state) <= limit


def test_a_step_whose_new_state_is_over_the_budget_is_not_committed(make: Make) -> None:
    probe = Probe(make())
    roomy = gate_for(OPEN, probe)
    opened(roomy, "s1")
    roomy.propose("s1", call_id="c1", tool="search", call_digest="d1")
    roomy.dispatch("s1", call_id="c1", attempt=1, call_digest="d1")
    limit = utf8_bytes(loaded(probe, "s1").state) - 100
    before = probe.load("s1")
    commits = probe.commits
    tight = gate_for(OPEN, probe, max_state_bytes=limit)
    with pytest.raises(WritStateFullError) as e:
        tight.result("s1", call_id="c1", outcome="succeeded")
    assert e.value.session_id == "s1" and e.value.bytes > limit and e.value.limit == limit
    assert probe.commits == commits
    assert probe.load("s1") == before
    tiny = gate_for(OPEN, probe, max_state_bytes=64)
    with pytest.raises(WritStateFullError):
        tiny.start("s2", requester="u1", permissions=[], approvers={})
    assert probe.load("s2") is None
    # Python adaptation: a bool is refused like 1.5, and a float with an integral value is that int.
    for bad in (0, 1.5, True, 0.0):
        with input_error("max_state_bytes"):
            gate_for(OPEN, probe, max_state_bytes=bad)
    whole = gate_for(OPEN, probe, max_state_bytes=4096.0)
    assert whole._max_state_bytes == 4096 and type(whole._max_state_bytes) is int


def test_session_start_counts_the_incoming_ledger_against_the_budget(make: Make) -> None:
    store = make()
    gate = gate_for(CALLS, store)
    opened(gate, "s1")
    initial = utf8_bytes(kernel.initial(CALLS).state)
    gate.kill_principal("u1")
    ledger = utf8_bytes(ledger_of(store).text)
    # Above seven eighths only with the ledger counted.
    limit = -(-(initial + ledger) * 8 // 7) - 1
    assert initial <= limit * 7 // 8
    tight = gate_for(CALLS, store, max_state_bytes=limit)
    with pytest.raises(WritStateFullError) as e:
        tight.start("s2", requester="u1", permissions=[], approvers={})
    assert e.value.bytes == initial + ledger
    assert store.load("s2") is None


def test_a_retired_policy_settles_but_does_not_propose(make: Make) -> None:
    store = make()
    old = gate_for(CALLS, store)
    opened(old, "s1")
    old.propose("s1", call_id="c1", tool="ping", call_digest="d")
    old.dispatch("s1", call_id="c1", attempt=1, call_digest="d")
    assert entries(store, "call", "committed") == [("c1", False)]
    nxt = gate_for(OPEN, store, retired_policy_texts=[CALLS])
    r = nxt.result("s1", call_id="c1", outcome="succeeded")
    assert r.verdict["verdict"] == "accepted", r.verdict
    assert entries(store, "call", "committed") == [("c1", True)]
    assert state(store, "s1")["calls"]["c1"]["status"] == "succeeded"

    def changed(call: Callable[[], object]) -> None:
        with pytest.raises(WritPolicyChangedError) as e:
            call()
        assert e.value.session_id == "s1" and e.value.policy_digest == kernel.digest(CALLS)

    before = store.load("s1")
    changed(lambda: nxt.propose("s1", call_id="c2", tool="ping", call_digest="d"))
    changed(lambda: nxt.step_start("s1"))
    changed(lambda: nxt.dispatch("s1", call_id="c1", attempt=2, call_digest="d"))
    assert store.load("s1") == before
    changed(lambda: gate_for(OPEN, store).end("s1"))
    changed(lambda: gate_for(OPEN, store).inspect("s1"))
    view = nxt.inspect("s1")
    assert view is not None
    assert [(c.call_id, c.status) for c in view.calls] == [("c1", "succeeded")]
    assert nxt.end("s1").verdict["verdict"] == "accepted"
    assert state(store, "s1")["ended"] is True
    opened(nxt, "s2")
    assert nxt.propose("s2", call_id="c1", tool="search", call_digest="d").kind == "allowed"


def test_create_gate_refuses_a_failing_policy(make: Make) -> None:
    store = make()
    bad = compact({"writ": "0.1", "actions": {"ping": {"meters": ["nope"]}}})
    with pytest.raises(WritInputError, match="policy fails check: unknown_meter") as e:
        create_gate(kernel=kernel, policy_text=bad, store=store)
    assert e.value.path == "policy_text"
    refused(1, "unknown_meter")(lambda: create_gate(
        kernel=kernel, policy_text=OPEN, store=store, retired_policy_texts=[CALLS, bad]))


def refused(i: int, *parts: str) -> Callable[[Callable[[], object]], None]:
    def check(call: Callable[[], object]) -> None:
        with pytest.raises(WritInputError) as e:
            call()
        assert e.value.path == f"retired_policy_texts[{i}]", str(e.value)
        for part in parts:
            assert part in str(e.value), (part, str(e.value))
    return check


def test_create_gate_refuses_a_retired_policy_whose_shared_principal_meter_has_another_window(make: Make) -> None:
    store = make()

    def calls(scope: str, window_ms: int | None = None) -> str:
        meter: dict[str, Any] = {"unit": "calls", "cap": 3, "scope": scope}
        if window_ms is not None:
            meter["window_ms"] = window_ms
        return compact({"writ": "0.1", "meters": {"calls": meter}, "actions": {"ping": {"meters": ["calls"]}}})

    refused(1, "calls", "window_ms")(lambda: create_gate(
        kernel=kernel, policy_text=PINGS, store=store, retired_policy_texts=[OPEN, calls("principal")]))
    refused(0, "calls", "window_ms")(lambda: create_gate(
        kernel=kernel, policy_text=PINGS, store=store, retired_policy_texts=[calls("principal", 3600000)]))
    refused(0, "calls", "window_ms")(lambda: create_gate(
        kernel=kernel, policy_text=calls("principal"), store=store, retired_policy_texts=[PINGS]))
    create_gate(kernel=kernel, policy_text=PINGS, store=store,
                retired_policy_texts=[CALLS, calls("session", 1000), SPEND])
    create_gate(kernel=kernel, policy_text=calls("session"), store=store, retired_policy_texts=[PINGS])
    create_gate(kernel=kernel, policy_text=calls("principal"), store=store, retired_policy_texts=[calls("principal")])


def test_create_gate_refuses_two_retired_policies_that_disagree_on_a_window(make: Make) -> None:
    store = make()
    hourly = compact({
        "writ": "0.1",
        "meters": {"calls": {"unit": "calls", "cap": 3, "scope": "principal", "window_ms": 3600000}},
        "actions": {"ping": {"meters": ["calls"]}},
    })
    refused(1, '"calls"', "retired_policy_texts[0]")(lambda: create_gate(
        kernel=kernel, policy_text=OPEN, store=store, retired_policy_texts=[CALLS, hourly]))
    create_gate(kernel=kernel, policy_text=OPEN, store=store, retired_policy_texts=[CALLS, PINGS])


def spend_in(currency: str, scope: str = "principal", **extra: Any) -> str:
    return compact({
        "writ": "0.1",
        "meters": {"spend": {"currency": currency, "cap": 5000, "scope": scope, "window_ms": 86400000, **extra}},
        "actions": {"buy": {"meters": ["spend"]}},
    })


def test_create_gate_refuses_a_retired_policy_whose_shared_principal_meter_has_another_currency(make: Make) -> None:
    store = make()
    refused(0, '"spend"', 'money in "EUR"', 'money in "USD"', "policy_text", "rename the meter")(lambda: create_gate(
        kernel=kernel, policy_text=SPEND, store=store, retired_policy_texts=[spend_in("EUR")]))
    create_gate(kernel=kernel, policy_text=SPEND, store=store,
                retired_policy_texts=[spend_in("USD", "principal", cap=9000, max_per_call=100)])


def test_create_gate_refuses_a_retired_policy_whose_shared_principal_meter_is_calls_instead_of_money(
        make: Make) -> None:
    store = make()

    def calls_named_spend(window_ms: int) -> str:
        return compact({
            "writ": "0.1",
            "meters": {"spend": {"unit": "calls", "cap": 3, "scope": "principal", "window_ms": window_ms}},
            "actions": {"buy": {"meters": ["spend"]}},
        })

    refused(0, '"spend" is a calls meter here, but policy_text makes it money in "USD";')(lambda: create_gate(
        kernel=kernel, policy_text=SPEND, store=store, retired_policy_texts=[calls_named_spend(86400000)]))
    refused(0, '"spend" is a calls meter with window_ms 3600000 here, but policy_text makes it money in "USD" '
               "with window_ms 86400000;")(lambda: create_gate(
                   kernel=kernel, policy_text=SPEND, store=store, retired_policy_texts=[calls_named_spend(3600000)]))


def test_create_gate_refuses_two_retired_policies_that_disagree_on_a_meters_currency(make: Make) -> None:
    store = make()
    refused(1, '"spend"', "retired_policy_texts[0]", '"EUR"', '"USD"')(lambda: create_gate(
        kernel=kernel, policy_text=OPEN, store=store, retired_policy_texts=[spend_in("USD"), spend_in("EUR")]))


def test_create_gate_accepts_a_retired_policy_whose_same_named_meter_is_session_scope_with_another_currency(
        make: Make) -> None:
    store = make()
    create_gate(kernel=kernel, policy_text=SPEND, store=store, retired_policy_texts=[spend_in("EUR", "session")])


def test_a_retired_session_meter_never_prunes_a_live_principal_meter(make: Make) -> None:
    store = make()
    now = [1000]

    def clock() -> int:
        return now[0]

    retired_text = compact({
        "writ": "0.1",
        "meters": {
            "spend": {"currency": "USD", "cap": 5000, "window_ms": 10},
            "uses": {"unit": "calls", "cap": 10, "scope": "principal"},
        },
        "actions": {"buy": {"meters": ["spend"]}, "use": {"meters": ["uses"]}},
    })
    old = gate_for(retired_text, store, clock=clock)
    opened(old, "A")
    assert old.propose("A", call_id="c1", tool="use", call_digest="d").kind == "allowed"
    assert old.dispatch("A", call_id="c1", call_digest="d").claimed is True
    live = gate_for(SPEND, store, clock=clock, retired_policy_texts=[retired_text])
    opened(live, "B")
    cost: Cost = {"amount": "5", "currency": "USD"}
    assert live.propose("B", call_id="c1", tool="buy", call_digest="d", cost=cost).kind == "allowed"
    assert live.dispatch("B", call_id="c1", call_digest="d", cost=cost).claimed is True
    assert live.result("B", call_id="c1", outcome="succeeded").verdict["verdict"] == "accepted"
    now[0] += 10
    r = live.result("A", call_id="c1", outcome="succeeded")
    assert r.verdict["verdict"] == "accepted", r.verdict
    assert entries(store, "meter", "session", "committed") == [("uses", "A", True), ("spend", "B", True)]


def test_dispatch_reports_claimed(make: Make) -> None:
    store = make()
    gate = gate_for(CALLS, store)
    opened(gate, "s1")
    gate.propose("s1", call_id="c1", tool="ping", call_digest="d")
    gate.propose("s1", call_id="c2", tool="ping", call_digest="d")
    won = gate.dispatch("s1", call_id="c1", call_digest="d")
    assert won.claimed is True
    assert won.reason is None
    lost = gate.dispatch("s1", call_id="c2", call_digest="d")
    assert lost.claimed is False, lost.verdict
    assert lost.reason == "meter_exceeded"
    assert state(store, "s1")["calls"]["c2"]["status"] == "authorized"


def test_attempt_defaults_from_state(make: Make) -> None:
    store = make()
    gate = gate_for(RETRY, store)
    opened(gate, "s1")
    gate.propose("s1", call_id="c1", tool="ping", call_digest="d")
    assert gate.dispatch("s1", call_id="c1", call_digest="d").claimed is True
    gate.outcome_unknown("s1", "c1")
    again = gate.dispatch("s1", call_id="c1", call_digest="d")
    assert again.claimed is True, again.verdict
    assert state(store, "s1")["calls"]["c1"]["attempts"] == 2


def test_a_defaulted_attempt_is_fixed_at_the_first_read_so_a_retry_another_gate_allowed_meanwhile_is_not_claimed(
        make: Make) -> None:
    probe = Probe(make())
    a = gate_for(RETRY, probe)
    b = gate_for(RETRY, probe)
    opened(a, "s1")
    a.propose("s1", call_id="c1", tool="ping", call_digest="d")

    def other_writer() -> None:
        assert b.dispatch("s1", call_id="c1", call_digest="d").claimed is True
        b.outcome_unknown("s1", "c1")

    held = probe.hold_next(other_writer)
    ra = a.dispatch("s1", call_id="c1", call_digest="d")
    assert held.ran
    assert ra.claimed is False, ra.verdict
    s = state(probe, "s1")
    assert s["calls"]["c1"]["attempts"] == 1
    assert s["calls"]["c1"]["status"] == "unknown"


def test_result_reports_overrun_meters(make: Make) -> None:
    store = make()
    gate = gate_for(SPEND, store)
    opened(gate, "s1")
    cost: Cost = {"amount": "1200", "currency": "USD"}
    for cid in ("c1", "c2"):
        gate.propose("s1", call_id=cid, tool="buy", call_digest=cid, cost=cost)
        gate.dispatch("s1", call_id=cid, call_digest=cid, cost=cost)
    over = gate.result("s1", call_id="c1", outcome="succeeded", actual_cost="1500")
    assert over.verdict["verdict"] == "accepted", over.verdict
    assert over.overrun == ("spend",)
    normal = gate.result("s1", call_id="c2", outcome="succeeded", actual_cost="1000")
    assert normal.verdict["verdict"] == "accepted", normal.verdict
    assert normal.overrun == ()


def test_inspect_lists_calls_for_recovery(make: Make) -> None:
    store = make()
    crashed = gate_for(CALLS, store)
    opened(crashed, "s1")
    crashed.propose("s1", call_id="c1", tool="ping", call_digest="d")
    assert crashed.dispatch("s1", call_id="c1", call_digest="d").claimed is True
    before = loaded(store, "s1")
    view = gate_for(CALLS, store).inspect("s1")
    assert view is not None
    assert view.session_id == "s1"
    assert view.state_version == before.state_version
    assert [(c.call_id, c.status, c.attempts) for c in view.calls] == [("c1", "dispatched", 1)]
    assert store.load("s1") == before
    assert gate_for(CALLS, store).inspect("missing") is None


def test_a_stores_own_byte_limit_caps_a_larger_max_state_bytes(make: Make) -> None:
    inner = make()
    roomy = gate_for(OPEN, inner)
    opened(roomy, "s1")
    roomy.propose("s1", call_id="c1", tool="search", call_digest="d1")
    n = utf8_bytes(loaded(inner, "s1").state)
    limit = n + 64
    headroom = limit * 7 // 8
    assert n > headroom, f"{n} > {headroom}"
    gate = gate_for(OPEN, limited(inner, limit), max_state_bytes=limit * 100)
    with pytest.raises(WritStateFullError) as e:
        gate.propose("s1", call_id="c2", tool="search", call_digest="d2")
    assert e.value.bytes == n and e.value.limit == headroom
    smaller = gate_for(OPEN, limited(inner, limit * 100), max_state_bytes=limit)
    with pytest.raises(WritStateFullError) as e:
        smaller.propose("s1", call_id="c2", tool="search", call_digest="d2")
    assert e.value.limit == headroom


def test_kill_principal_and_clear_principal_kill_refuse_a_malformed_principal(make: Make) -> None:
    store = make()
    gate = gate_for(CALLS, store)
    # Python adaptation: a str holding a lone surrogate, which has no UTF-8 form, is refused too.
    bad: list[Any] = [None, 7, "", "x" * 513, chr(0xE9) * 257, "a" + chr(0xD800)]
    for p in bad:
        for f in (gate.kill_principal, gate.clear_principal_kill):
            with input_error("principal"):
                f(p)
    assert gate.kill_principal("x" * 512) == PrincipalKillResult(1, True)


def test_idempotency_keys_differ_across_principals(make: Make) -> None:
    assert default_idempotency_key("u1", "s", "c") != default_idempotency_key("u2", "s", "c")
    store = make()
    gate = gate_for(OPEN, store)
    opened(gate, "s1", "u7")
    gate.propose("s1", call_id="c1", tool="search", call_digest="d")
    gate.dispatch("s1", call_id="c1", attempt=1, call_digest="d")
    assert state(store, "s1")["calls"]["c1"]["idempotency_key"] == default_idempotency_key("u7", "s1", "c1")


def test_threads_sharing_one_gate_and_store_each_run_their_own_sessions(make: Make) -> None:
    # Python only: the TypeScript gate is never called from two threads.
    store = make()
    gate = gate_for(PINGS, store)
    failures: list[BaseException] = []

    def run(i: int) -> None:
        try:
            opened(gate, f"s{i}", f"u{i}")
            for n in range(5):
                assert gate.propose(f"s{i}", call_id=f"c{n}", tool="ping", call_digest="d").kind == "allowed"
                assert gate.dispatch(f"s{i}", call_id=f"c{n}", call_digest="d").claimed is True
                assert gate.result(f"s{i}", call_id=f"c{n}", outcome="succeeded").verdict["verdict"] == "accepted"
        except BaseException as e:
            failures.append(e)

    threads = [threading.Thread(target=run, args=(i,)) for i in range(4)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert failures == []
    for i in range(4):
        assert {c["status"] for c in state(store, f"s{i}")["calls"].values()} == {"succeeded"}
        assert len(json.loads(ledger_of(store, f"u{i}").text)["entries"]) == 5


# From packages/writ/test/gate.test.ts.


def test_clamp_untrusted_rewrites_only_result_and_reconcile() -> None:
    base = {"seq": 1, "time": 0, "state_version": 0, "call_id": "c"}
    assert _clamp_untrusted({**base, "type": "result", "outcome": "declined", "actual_cost": "5", "no_effect": True},
                            False, "10") == {**base, "type": "result", "outcome": "failed", "actual_cost": "10",
                                             "no_effect": False}
    assert _clamp_untrusted({**base, "type": "reconcile", "outcome": "declined", "actual_cost": "15"},
                            True, "10") == {**base, "type": "reconcile", "outcome": "declined", "actual_cost": "15",
                                            "no_effect": False}
    assert _clamp_untrusted({**base, "type": "result", "outcome": "succeeded", "actual_cost": "0"},
                            False, None) == {**base, "type": "result", "outcome": "succeeded", "actual_cost": "0",
                                             "no_effect": False}
    other = {**base, "type": "outcome_unknown"}
    assert _clamp_untrusted(other, False, None) is other


def test_propose_kind_table() -> None:
    def acc(**d: Any) -> dict[str, Any]:
        return {"verdict": "accepted", "state_version": 1, **d}

    rid = {"session": "s", "call": "c", "generation": 0}
    cases: list[tuple[dict[str, Any], str]] = [
        (acc(decision="allowed"), "allowed"),
        (acc(decision="allowed_by_grant", grant="g"), "allowed"),
        (acc(decision="authorized"), "allowed"),
        (acc(decision="existing", status="authorized"), "allowed"),
        (acc(decision="existing", status="dispatched"), "denied"),
        (acc(decision="needs_approval", request_id=rid), "needs_approval"),
        (acc(decision="denied", reason="unknown_tool"), "denied"),
        (acc(decision="existing", status={"status": "denied", "reason": "guard_false"}), "denied"),
        (acc(decision="existing", status={"status": "denied_at_dispatch", "reason": "permission_missing"}), "denied"),
        (acc(decision="existing", status="succeeded"), "denied"),
        (acc(decision="existing", status="unknown"), "denied"),
        (acc(decision="existing", status="cancelled"), "denied"),
        (acc(), "denied"),
        ({"verdict": "rejected", "state_version": 1, "reason": "turn_state", "retry": "fix_request", "message": "m"},
         "rejected"),
    ]
    for v, want in cases:
        assert propose_kind(v) == want, v


class Counting:
    def __init__(self, inner: Store) -> None:
        self.inner = inner
        self.commits: list[Commit] = []

    def load(self, session_id: str) -> Stored | None:
        return self.inner.load(session_id)

    def load_ledger(self, principal: str) -> LedgerRecord | None:
        return self.inner.load_ledger(principal)

    def commit_ledger(self, c: LedgerCommit) -> LedgerCommitOutcome:
        return self.inner.commit_ledger(c)

    def commit(self, c: Commit) -> CommitOutcome:
        self.commits.append(c)
        return self.inner.commit(c)


def test_dispatch_without_idempotency_key_sends_h_principal_session_id_call_id_the_same_on_every_attempt(
        make: Make) -> None:
    want = "sha256:" + hashlib.sha256(
        canonicalize({"principal": "u1", "session": "s1", "call": "c1"}).encode("utf-8")).hexdigest()
    assert default_idempotency_key("u1", "s1", "c1") == want
    assert default_idempotency_key("u1", "s1", "c2") != want
    assert default_idempotency_key("u1", "s2", "c1") != want
    assert default_idempotency_key("u2", "s1", "c1") != want

    store = Counting(make())
    gate = create_gate(kernel=kernel, policy_text=RETRY, store=store, clock=ticking(0))
    gate.start("s1", requester="u1", permissions=[], approvers={}, user_initiated=True)
    gate.step_start("s1")
    assert gate.propose("s1", call_id="c1", tool="ping", call_digest="d").kind == "allowed"
    keys = []
    for attempt in (1, 2):
        d = gate.dispatch("s1", call_id="c1", attempt=attempt, call_digest="d")
        assert decision(d) == "dispatch_claimed", d.verdict
        keys.append(state(store, "s1")["calls"]["c1"]["idempotency_key"])
        if attempt == 1:
            gate.outcome_unknown("s1", "c1")
    assert keys == [want, want]

    # An explicit key is still sent as given, and must then stay the same across attempts.
    gate.propose("s1", call_id="c2", tool="ping", call_digest="d")
    gate.dispatch("s1", call_id="c2", attempt=1, call_digest="d", idempotency_key="k-own")
    assert state(store, "s1")["calls"]["c2"]["idempotency_key"] == "k-own"
    gate.outcome_unknown("s1", "c2")
    other = gate.dispatch("s1", call_id="c2", attempt=2, call_digest="d")
    assert reason(other) == "idempotency_key_mismatch"


def test_the_gate_commits_nothing_for_a_rejected_verdict_even_when_the_kernel_says_changed(make: Make) -> None:
    store = Counting(make())
    lie = [False]

    def step(policy_text: str, state_text: str, event: Mapping[str, Any]) -> StepResult:
        r = kernel.step(policy_text, state_text, event)
        if not lie[0]:
            return r
        verdict = {"verdict": "rejected", "state_version": r.state_version, "reason": "call_awaiting",
                   "retry": "fix_request", "message": "stub"}
        return replace(r, verdict=verdict, changed=True)

    gate = create_gate(kernel=stub(step), policy_text=RETRY, store=store, clock=ticking(0))
    gate.start("s1", requester="u1", permissions=[], approvers={}, user_initiated=True)
    before = loaded(store, "s1")
    commits = len(store.commits)
    lie[0] = True
    r = gate.step_start("s1")
    assert r.verdict["verdict"] == "rejected"
    assert r.state_version == before.state_version
    assert len(store.commits) == commits
    assert store.load("s1") == before
