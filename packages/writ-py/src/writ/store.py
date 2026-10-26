from __future__ import annotations

import threading
from dataclasses import dataclass
from typing import Literal, Protocol

CommitOutcome = Literal["ok", "state_conflict", "ledger_conflict"]
LedgerCommitOutcome = Literal["ok", "ledger_conflict"]


@dataclass(frozen=True)
class Stored:
    state: str
    state_version: int
    principal: str


@dataclass(frozen=True)
class LedgerRecord:
    """Version 0 is the empty ledger, which is never stored."""

    text: str
    version: int


@dataclass(frozen=True, kw_only=True)
class Commit:
    """One atomic compare-and-swap over the session record and the principal's ledger record.

    An expected version of None means the record must not exist yet. The ledger version is
    checked on every commit, including one that writes no ledger (`ledger` None).
    """

    session_id: str
    state: str
    state_version: int
    expected_state_version: int | None
    principal: str
    expected_ledger_version: int | None
    ledger: LedgerRecord | None = None


@dataclass(frozen=True, kw_only=True)
class LedgerCommit:
    """A compare-and-swap over the principal's ledger record alone, to set or clear its tombstone without a session."""

    principal: str
    ledger: LedgerRecord
    expected_ledger_version: int | None


class Store(Protocol):
    """Where a gate keeps sessions and principal ledgers.

    A store may also have a `max_state_bytes` attribute, an int: the most UTF-8 bytes of session state it
    can hold. The gate reads it with `getattr`, so a store without a limit leaves it out.
    """

    def load(self, session_id: str) -> Stored | None: ...

    def load_ledger(self, principal: str) -> LedgerRecord | None: ...

    def commit(self, c: Commit) -> CommitOutcome:
        """Writes nothing unless it returns "ok"."""
        ...

    def commit_ledger(self, c: LedgerCommit) -> LedgerCommitOutcome:
        """Writes nothing unless it returns "ok"; atomic with `commit`."""
        ...


class MemoryStore:
    """An in-process `Store`, for tests and single-process tools. Safe to share between threads."""

    def __init__(self) -> None:
        self._sessions: dict[str, Stored] = {}
        self._ledgers: dict[str, LedgerRecord] = {}
        self._lock = threading.Lock()

    def load(self, session_id: str) -> Stored | None:
        with self._lock:
            return self._sessions.get(session_id)

    def load_ledger(self, principal: str) -> LedgerRecord | None:
        with self._lock:
            return self._ledgers.get(principal)

    def _ledger_version(self, principal: str) -> int | None:
        rec = self._ledgers.get(principal)
        return None if rec is None else rec.version

    def commit(self, c: Commit) -> CommitOutcome:
        with self._lock:
            cur = self._sessions.get(c.session_id)
            if (None if cur is None else cur.state_version) != c.expected_state_version:
                return "state_conflict"
            if self._ledger_version(c.principal) != c.expected_ledger_version:
                return "ledger_conflict"
            self._sessions[c.session_id] = Stored(c.state, c.state_version, c.principal)
            if c.ledger is not None:
                self._ledgers[c.principal] = LedgerRecord(c.ledger.text, c.ledger.version)
            return "ok"

    def commit_ledger(self, c: LedgerCommit) -> LedgerCommitOutcome:
        with self._lock:
            if self._ledger_version(c.principal) != c.expected_ledger_version:
                return "ledger_conflict"
            self._ledgers[c.principal] = LedgerRecord(c.ledger.text, c.ledger.version)
            return "ok"
