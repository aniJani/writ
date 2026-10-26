"""Kernel results.

Records of a fixed shape are frozen dataclasses. Values that are also event or verdict JSON
(verdicts, request ids, costs, call statuses, profile envelopes) stay plain dicts and strs, as the
kernel wrote them, so they go back into events unchanged and print as the kernel printed them.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

JsonObject = dict[str, Any]

Verdict = JsonObject
"""`{"verdict": "accepted", "state_version", "decision"?, ...}`,
or `{"verdict": "rejected", "state_version", "reason", "retry", "message"}`."""

CallStatus = str | JsonObject
"""A status name such as `"awaiting"`, or `{"status": "denied" | "denied_at_dispatch", "reason": ...}`."""


@dataclass(frozen=True)
class StateEnvelope:
    state: str
    state_version: int
    ledger_version: int


@dataclass(frozen=True)
class StepResult(StateEnvelope):
    verdict: Verdict
    ledger: str
    changed: bool
    ledger_changed: bool


@dataclass(frozen=True)
class TombstoneResult:
    ledger: str
    ledger_version: int
    changed: bool


@dataclass(frozen=True)
class Finding:
    code: str
    message: str
    action: str | None = None


@dataclass(frozen=True)
class CheckResult:
    ok: bool
    errors: tuple[Finding, ...]
    warnings: tuple[Finding, ...]
    policy_digest: str


@dataclass(frozen=True)
class StepReplay:
    step: int
    message: str


@dataclass(frozen=True)
class TraceReplay:
    id: str
    ok: bool
    mismatches: tuple[StepReplay, ...]


@dataclass(frozen=True)
class ReplayResult:
    traces: tuple[TraceReplay, ...]


@dataclass(frozen=True)
class CallView:
    call_id: str
    tool: str
    status: CallStatus
    digest: str
    cost: JsonObject | None
    attempts: int
    generation: int
    epoch: int
    request_id: JsonObject | None = None
    """Present only while the call is awaiting approval."""


@dataclass(frozen=True)
class MeterView:
    """Amounts are decimal strings in the meter's unit; `cap` and `remaining` are None without a cap.

    `remaining` is never below "0", and `used` may exceed `cap` after an overrun.
    """

    meter: str
    scope: str
    used: str
    cap: str | None
    remaining: str | None


@dataclass(frozen=True)
class SessionView:
    session_id: str
    state_version: int
    ledger_version: int
    started: bool
    ended: bool
    killed: bool
    tombstone: bool
    escalated: bool
    escalations: int
    blocked_tools: tuple[str, ...]
    calls: tuple[CallView, ...]
    meters: tuple[MeterView, ...]


@dataclass(frozen=True)
class ProfileResult:
    """`disposition` is None while the call can still move; `envelope` is None for a verdict that has none."""

    disposition: str | None = None
    envelope: JsonObject | None = None


def _finding(d: JsonObject) -> Finding:
    return Finding(code=d["code"], message=d["message"], action=d.get("action"))


def check_result(d: JsonObject) -> CheckResult:
    return CheckResult(ok=d["ok"], errors=tuple(map(_finding, d["errors"])),
                       warnings=tuple(map(_finding, d["warnings"])), policy_digest=d["policy_digest"])


def replay_result(d: JsonObject) -> ReplayResult:
    return ReplayResult(traces=tuple(
        TraceReplay(id=t["id"], ok=t["ok"],
                    mismatches=tuple(StepReplay(step=m["step"], message=m["message"]) for m in t["mismatches"]))
        for t in d["traces"]))


def session_view(d: JsonObject) -> SessionView:
    return SessionView(
        session_id=d["session_id"], state_version=d["state_version"], ledger_version=d["ledger_version"],
        started=d["started"], ended=d["ended"], killed=d["killed"], tombstone=d["tombstone"],
        escalated=d["escalated"], escalations=d["escalations"], blocked_tools=tuple(d["blocked_tools"]),
        calls=tuple(CallView(
            call_id=c["call_id"], tool=c["tool"], status=c["status"], digest=c["digest"], cost=c["cost"],
            attempts=c["attempts"], generation=c["generation"], epoch=c["epoch"], request_id=c.get("request_id"),
        ) for c in d["calls"]),
        meters=tuple(MeterView(meter=m["meter"], scope=m["scope"], used=m["used"], cap=m["cap"],
                               remaining=m["remaining"]) for m in d["meters"]),
    )


def profile_result(d: JsonObject) -> ProfileResult:
    return ProfileResult(disposition=d.get("disposition"), envelope=d.get("envelope"))
