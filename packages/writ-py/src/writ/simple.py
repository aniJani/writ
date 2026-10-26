from __future__ import annotations

import json
import uuid
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from typing import Any, Final, Generic, Literal, TypeVar

from .canonical import MAX_SAFE_INTEGER
from .digest import call_digest
from .errors import WritInputError
from .gate import Clock, Gate, GateResult, KernelLike, _whole, create_gate
from .kernel import load_kernel
from .store import MemoryStore, Store

SimpleConsent = Literal["none", "per_call"]
SimpleStatus = Literal["allowed", "needs_approval", "denied"]
T = TypeVar("T")

APPROVER: Final = "user"


@dataclass(frozen=True)
class SimpleCall:
    """A proposed call. `request_id` is opaque to callers; `json.loads` gives the gate's request id."""

    call_id: str
    tool: str
    call_digest: str
    status: SimpleStatus
    reason: str | None = None
    request_id: str | None = None


@dataclass(frozen=True)
class RunResult(Generic[T]):
    """`ran` is True when the call was claimed and the function returned `value`; else `reason` says why not."""

    ran: bool
    value: T | None = None
    reason: str | None = None


def simple_policy(tools: Mapping[str, SimpleConsent], *, approval_ttl_ms: int | None = None) -> str:
    """The layer-1 policy for a map of tool names to consents, with the user as the only approver role."""
    if not isinstance(tools, Mapping):
        raise WritInputError("expected a dict of tool names to consents", "tools")
    if len(tools) == 0:
        raise WritInputError("expected at least one tool", "tools")
    actions: dict[str, dict[str, str]] = {}
    for name, consent in tools.items():
        if not isinstance(name, str):
            raise WritInputError("expected a str tool name", "tools")
        if consent not in ("none", "per_call"):
            raise WritInputError('expected "none" or "per_call"', f"tools.{name}")
        actions[name] = {"consent": consent}
    ttl = 600_000 if approval_ttl_ms is None else _whole(approval_ttl_ms)
    if not isinstance(ttl, int) or isinstance(ttl, bool) or not 0 <= ttl <= MAX_SAFE_INTEGER:
        raise WritInputError("expected a non-negative integer", "approval_ttl_ms")
    return json.dumps({
        "writ": "0.1",
        "approver_roles": [APPROVER],
        "limits": {"approval_ttl_ms": ttl},
        "actions": actions,
    }, separators=(",", ":"), ensure_ascii=False)


def _status_of(r: GateResult) -> SimpleStatus:
    v = r.verdict
    if v["verdict"] == "rejected":
        return "denied"
    d = v.get("decision")
    if d in ("allowed", "allowed_by_grant", "authorized"):
        return "allowed"
    if d in ("needs_approval", "pending"):
        return "needs_approval"
    if d == "existing":
        status = v.get("status")
        return "allowed" if status == "authorized" else "needs_approval" if status == "awaiting" else "denied"
    return "denied"


# The simple API hands the request id around as an opaque string so callers can store or show it.
def _encode_request(r: Mapping[str, Any]) -> str:
    return json.dumps(r, separators=(",", ":"), ensure_ascii=False)


def _decode_request(call: SimpleCall) -> dict[str, Any]:
    if call.request_id is None:
        raise WritInputError("the call is not awaiting approval", "request_id")
    try:
        r = json.loads(call.request_id)
    except (TypeError, ValueError):
        r = None
    if (isinstance(r, dict) and isinstance(r.get("session"), str) and isinstance(r.get("call"), str)
            and isinstance(r.get("generation"), int) and not isinstance(r.get("generation"), bool)):
        return r
    raise WritInputError("expected a request id from propose", "request_id")


class SimpleSession:
    """One gate session for the simple gate's user. Make one with `SimpleGate.session`."""

    def __init__(self, gate: Gate, session_id: str) -> None:
        self._gate = gate
        self.id = session_id

    def _settle(self, call: SimpleCall, r: GateResult) -> SimpleCall:
        status = _status_of(r)
        return SimpleCall(call.call_id, call.tool, call.call_digest, status, r.reason,
                          call.request_id if status == "needs_approval" else None)

    def _refused(self, call: SimpleCall, reason: str) -> SimpleCall:
        """A refused approve or reject, reported from where the call stands afterwards, which an expired
        approval changes."""
        # The kernel refuses an answer after the TTL, but the stored call stays awaiting until an
        # approval_expire event ends it.
        if reason == "approval_expired":
            self._gate.approval_expire(self.id, call_id=call.call_id, request_id=_decode_request(call))
        view = self._gate.inspect(self.id)
        found = None if view is None else next((c for c in view.calls if c.call_id == call.call_id), None)
        digest = call.call_digest if found is None else found.digest
        if found is not None and found.status == "authorized":
            return SimpleCall(call.call_id, call.tool, digest, "allowed", reason)
        if found is not None and found.status == "awaiting":
            rid = call.request_id if found.request_id is None else _encode_request(found.request_id)
            return SimpleCall(call.call_id, call.tool, digest, "needs_approval", reason, rid)
        return SimpleCall(call.call_id, call.tool, digest, "denied", reason)

    def propose(self, tool: str, args: object) -> SimpleCall:
        """Mints a call id and digests `{"server": "local", "tool", "tool_digest": "unversioned", "args"}`."""
        call_id = str(uuid.uuid4())
        digest = call_digest({"server": "local", "tool": tool, "tool_digest": "unversioned", "args": args})
        r = self._gate.propose(self.id, call_id=call_id, tool=tool, call_digest=digest)
        rid = _encode_request(r.request_id) if r.kind == "needs_approval" and r.request_id is not None else None
        return SimpleCall(call_id, tool, digest, _status_of(r), r.reason, rid)

    def approve(self, call: SimpleCall) -> SimpleCall:
        r = self._gate.approve(self.id, call_id=call.call_id, request_id=_decode_request(call), approver_id=APPROVER,
                               reviewed_digest=call.call_digest)
        if r.verdict["verdict"] == "rejected":
            return self._refused(call, str(r.verdict["reason"]))
        return self._settle(call, r)

    def reject(self, call: SimpleCall) -> SimpleCall:
        r = self._gate.reject(self.id, call_id=call.call_id, request_id=_decode_request(call), approver_id=APPROVER)
        if r.verdict["verdict"] == "rejected":
            return self._refused(call, str(r.verdict["reason"]))
        # An accepted reject ends the call rejected; its verdict carries no decision or reason.
        return SimpleCall(call.call_id, call.tool, call.call_digest, "denied")

    def run(self, call: SimpleCall, fn: Callable[[], T]) -> RunResult[T]:
        """Dispatches the call and runs `fn` only if the dispatch is claimed, then reports it succeeded.

        If `fn` raises, the call is reported unknown and the exception propagates.
        """
        d = self._gate.dispatch(self.id, call_id=call.call_id, call_digest=call.call_digest)
        if not d.claimed:
            return RunResult(ran=False, reason=d.reason or "not_claimed")
        try:
            value = fn()
        except BaseException:
            # The tool's error is the one the caller needs. If this report fails too, the call stays
            # dispatched, and `gate.inspect` lists it for `outcome_unknown` or `reconcile` later.
            try:
                self._gate.outcome_unknown(self.id, call.call_id)
            except Exception:
                pass
            raise
        self._gate.result(self.id, call_id=call.call_id, outcome="succeeded")
        return RunResult(ran=True, value=value)


class SimpleGate:
    """`policy_text` is the layer-1 policy the gate runs. Take it, and `gate`, when you outgrow the simple path."""

    def __init__(self, policy_text: str, gate: Gate, user: str) -> None:
        self.policy_text = policy_text
        self.gate = gate
        self._user = user

    def session(self, session_id: str | None = None) -> SimpleSession:
        """Starts a session (a new uuid4 id unless one is given) with a user-initiated first turn."""
        sid = str(uuid.uuid4()) if session_id is None else session_id
        started = self.gate.start(
            sid, requester=self._user, permissions=[],
            approvers={APPROVER: {"principal": self._user, "kind": "human", "roles": [APPROVER]}},
            user_initiated=True)
        if started.verdict["verdict"] == "rejected":
            raise WritInputError(f"the session could not start: {started.verdict['reason']}", "session_id")
        return SimpleSession(self.gate, sid)


def simple_gate(tools: Mapping[str, SimpleConsent], *, user: str, approval_ttl_ms: int | None = None,
                kernel: KernelLike | None = None, store: Store | None = None, clock: Clock | None = None) -> SimpleGate:
    """The minimal path: name the tools, say which need the user's approval (`"per_call"`), and run them.

    `approval_ttl_ms` defaults to 600000; `kernel` to a new `load_kernel()`, `store` to a new `MemoryStore`.
    """
    policy_text = simple_policy(tools, approval_ttl_ms=approval_ttl_ms)
    gate = create_gate(kernel=load_kernel() if kernel is None else kernel, policy_text=policy_text,
                       store=MemoryStore() if store is None else store, clock=clock)
    return SimpleGate(policy_text, gate, user)
