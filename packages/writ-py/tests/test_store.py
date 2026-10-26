"""The store contract, ported from packages/writ/test/store-suite.ts. Run it against your own store by adding
its factory to the `make` fixture in conftest.py."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import FrozenInstanceError, replace
from typing import Any

import pytest

from writ import Commit, LedgerCommit, LedgerRecord, Store, Stored

Make = Callable[[], Store]


def base(**over: Any) -> Commit:
    fields: dict[str, Any] = {"session_id": "s1", "state": "{}", "state_version": 1, "expected_state_version": None,
                              "principal": "u1", "expected_ledger_version": None}
    return Commit(**{**fields, **over})


def ledger_only(version: int, expected_ledger_version: int | None) -> LedgerCommit:
    return LedgerCommit(principal="u1", ledger=LedgerRecord(f"L{version}", version),
                        expected_ledger_version=expected_ledger_version)


def test_a_session_is_created_only_with_expected_version_null(make: Make) -> None:
    store = make()
    assert store.commit(base(expected_state_version=0)) == "state_conflict"
    assert store.load("s1") is None
    assert store.commit(base(state="a")) == "ok"
    assert store.load("s1") == Stored("a", 1, "u1")
    assert store.commit(base(state="b")) == "state_conflict"
    s = store.load("s1")
    assert s is not None and s.state == "a"


def test_a_stale_state_version_is_a_conflict_and_the_current_one_wins(make: Make) -> None:
    store = make()
    store.commit(base(state="a"))
    assert store.commit(base(state="b", state_version=2, expected_state_version=1)) == "ok"
    assert store.commit(base(state="c", state_version=2, expected_state_version=1)) == "state_conflict"
    assert store.load("s1") == Stored("b", 2, "u1")


def test_a_ledger_conflict_writes_neither_record(make: Make) -> None:
    store = make()
    assert store.commit(base(state="a", ledger=LedgerRecord("L2", 2))) == "ok"
    assert store.load_ledger("u1") == LedgerRecord("L2", 2)
    stale = base(state="b", state_version=2, expected_state_version=1, ledger=LedgerRecord("L3", 3),
                 expected_ledger_version=None)
    assert store.commit(stale) == "ledger_conflict"
    assert store.commit(replace(stale, expected_ledger_version=1)) == "ledger_conflict"
    assert store.load("s1") == Stored("a", 1, "u1")
    assert store.load_ledger("u1") == LedgerRecord("L2", 2)
    assert store.commit(replace(stale, expected_ledger_version=2)) == "ok"
    assert store.load_ledger("u1") == LedgerRecord("L3", 3)


def test_the_ledger_version_is_checked_even_when_the_commit_does_not_write_the_ledger(make: Make) -> None:
    store = make()
    store.commit(base(session_id="s0", ledger=LedgerRecord("L2", 2)))
    assert store.commit(base(state="a")) == "ledger_conflict"
    assert store.load("s1") is None
    assert store.commit(base(state="a", expected_ledger_version=2)) == "ok"
    assert store.load_ledger("u1") == LedgerRecord("L2", 2)


def test_a_state_conflict_is_reported_before_a_ledger_conflict_and_writes_nothing(make: Make) -> None:
    store = make()
    store.commit(base(state="a", ledger=LedgerRecord("L2", 2)))
    assert store.commit(base(state="b", state_version=2, expected_state_version=5,
                             expected_ledger_version=7)) == "state_conflict"
    s = store.load("s1")
    assert s is not None and s.state == "a"


def test_ledgers_are_kept_per_principal(make: Make) -> None:
    store = make()
    store.commit(base(ledger=LedgerRecord("L1", 1)))
    store.commit(base(session_id="s2", principal="u2"))
    assert store.load_ledger("u2") is None
    assert store.load_ledger("u1") == LedgerRecord("L1", 1)


def test_loaded_records_are_copies(make: Make) -> None:
    # The TypeScript test mutates the loaded objects; here they are frozen, so a write fails and the store keeps
    # its records.
    store = make()
    store.commit(base(state="a", ledger=LedgerRecord("L1", 1)))
    s = store.load("s1")
    ledger = store.load_ledger("u1")
    assert s is not None and ledger is not None
    with pytest.raises(FrozenInstanceError):
        s.state_version = 9  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        ledger.version = 9  # type: ignore[misc]
    s2 = store.load("s1")
    ledger2 = store.load_ledger("u1")
    assert s2 is not None and s2.state_version == 1
    assert ledger2 is not None and ledger2.version == 1


def test_commit_ledger_is_a_compare_and_swap_on_the_ledger_record_alone(make: Make) -> None:
    store = make()
    assert store.commit_ledger(ledger_only(1, 0)) == "ledger_conflict"
    assert store.load_ledger("u1") is None
    assert store.commit_ledger(ledger_only(1, None)) == "ok"
    assert store.load_ledger("u1") == LedgerRecord("L1", 1)
    assert store.commit_ledger(ledger_only(2, None)) == "ledger_conflict"
    assert store.commit_ledger(ledger_only(2, 0)) == "ledger_conflict"
    assert store.load_ledger("u1") == LedgerRecord("L1", 1)
    assert store.commit_ledger(ledger_only(2, 1)) == "ok"
    assert store.commit_ledger(ledger_only(3, 1)) == "ledger_conflict"
    assert store.load_ledger("u1") == LedgerRecord("L2", 2)
    assert store.load("s1") is None
    assert store.load_ledger("u2") is None


def test_a_session_commit_sees_the_version_commit_ledger_wrote_and_commit_ledger_leaves_sessions_alone(
        make: Make) -> None:
    store = make()
    assert store.commit(base(state="a", ledger=LedgerRecord("L1", 1))) == "ok"
    assert store.commit_ledger(ledger_only(2, 1)) == "ok"
    assert store.load("s1") == Stored("a", 1, "u1")
    nxt = base(state="b", state_version=2, expected_state_version=1)
    assert store.commit(replace(nxt, expected_ledger_version=1)) == "ledger_conflict"
    assert store.commit(replace(nxt, expected_ledger_version=2)) == "ok"
    assert store.load_ledger("u1") == LedgerRecord("L2", 2)
