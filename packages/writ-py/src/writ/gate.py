from __future__ import annotations

import json
import re
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Final, Literal, Protocol, TypedDict, cast

from .canonical import MAX_SAFE_INTEGER, canonicalize, parse_strict
from .digest import Cost, sha256
from .errors import WritConflictError, WritInputError, WritPolicyChangedError, WritStateFullError
from .kernel import MAX_INPUT_BYTES
from .store import Commit, LedgerCommit, LedgerRecord, Store, Stored
from .types import CallStatus, CheckResult, JsonObject, SessionView, StateEnvelope, StepResult, TombstoneResult, Verdict

ProposeKind = Literal["allowed", "needs_approval", "denied", "rejected"]
Outcome = Literal["succeeded", "failed", "declined"]
Clock = Callable[[], int]


class KernelLike(Protocol):
    """The kernel methods a gate calls. `Kernel` from `load_kernel()` has them; a wrapper around one can too."""

    def check(self, policy_text: str) -> CheckResult: ...

    def digest(self, json_text: str) -> str: ...

    def initial(self, policy_text: str, digest: str | None = None) -> StateEnvelope: ...

    def step(self, policy_text: str, state_text: str, event: Mapping[str, Any]) -> StepResult: ...

    def tombstone(self, ledger_text: str, set: bool) -> TombstoneResult: ...

    def inspect(self, policy_text: str, state_text: str, time: int) -> SessionView: ...


class Approver(TypedDict):
    principal: str
    kind: Literal["human", "automated"]
    roles: Sequence[str]


class _EditFields(TypedDict):
    new_digest: str


class Edit(_EditFields, total=False):
    """An approval's edit of the call: its new digest, and optionally its new cost and escalators."""

    new_cost: Cost
    escalators: Mapping[str, bool]


@dataclass(frozen=True, kw_only=True)
class GateResult:
    """`state_version` is the version of the stored state after the call.

    `reason` is a rejected verdict's reason, else a `denied` or `dispatch_denied` decision's, else the
    one inside an `existing` denied status.
    """

    verdict: Verdict
    state_version: int
    reason: str | None = None


@dataclass(frozen=True, kw_only=True)
class ProposeResult(GateResult):
    """`request_id` is set for `needs_approval`; `status` is the call's status when the verdict is an
    `existing` decision and `kind` is `denied`."""

    kind: ProposeKind
    request_id: JsonObject | None = None
    status: CallStatus | None = None


@dataclass(frozen=True, kw_only=True)
class DispatchResult(GateResult):
    """`claimed` is True only for a `dispatch_claimed` decision: run the tool then, and only then."""

    claimed: bool


@dataclass(frozen=True, kw_only=True)
class ReportResult(GateResult):
    """`overrun` names the meters an accepted report committed above the reservation."""

    overrun: tuple[str, ...] = ()


@dataclass(frozen=True)
class PrincipalKillResult:
    """`ledger_version` is the version of the stored ledger after the call.

    `changed` is False when it already was so.
    """

    ledger_version: int
    changed: bool


def propose_kind(v: Verdict) -> ProposeKind:
    if v["verdict"] == "rejected":
        return "rejected"
    d = v.get("decision")
    # A repeated propose of an approved call answers `authorized`.
    if d in ("allowed", "allowed_by_grant", "authorized"):
        return "allowed"
    if d == "needs_approval":
        return "needs_approval"
    # A dispatched call cannot be dispatched again; it is recovered with outcome_unknown or reconcile.
    if d == "existing":
        return "allowed" if v.get("status") == "authorized" else "denied"
    # Anything else, a finished call included, must not run now.
    return "denied"


def _reason_of(v: Verdict) -> str | None:
    if v["verdict"] == "rejected":
        return str(v["reason"])
    d = v.get("decision")
    if d in ("denied", "dispatch_denied"):
        return str(v["reason"])
    status = v.get("status")
    if d == "existing" and isinstance(status, dict):
        return str(status["reason"])
    return None


def _gate_result(verdict: Verdict, state_version: int) -> GateResult:
    return GateResult(verdict=verdict, state_version=state_version, reason=_reason_of(verdict))


def _propose_result(r: GateResult) -> ProposeResult:
    v = r.verdict

    def kind(k: ProposeKind, request_id: JsonObject | None = None, status: CallStatus | None = None) -> ProposeResult:
        return ProposeResult(verdict=v, state_version=r.state_version, reason=r.reason, kind=k,
                             request_id=request_id, status=status)

    if v["verdict"] == "rejected":
        return kind("rejected")
    if v.get("decision") == "needs_approval":
        return kind("needs_approval", request_id=v["request_id"])
    if propose_kind(v) == "allowed":
        return kind("allowed")
    if v.get("decision") == "existing":
        return kind("denied", status=v["status"])
    return kind("denied")


def default_idempotency_key(principal: str, session_id: str, call_id: str) -> str:
    """The idempotency key spec section 6 derives from the principal, the session and the call:
    H(principal, session_id, call_id)."""
    return sha256(canonicalize({"principal": principal, "session": session_id, "call": call_id}))


_AMOUNT: Final = re.compile(r"(0|[1-9][0-9]*)")


def _clamp_untrusted(event: JsonObject, trusted_decline: bool, reservation: str | None) -> JsonObject:
    """Spec sections 6 and 10: a report from an untrusted executor never releases a reservation, never
    commits less than it, and cannot claim a decline that did not come through the trusted approval
    renderer. `reservation` is the call's current cost amount in state."""
    if event.get("type") not in ("result", "reconcile"):
        return event
    out = {**event, "no_effect": False}
    if out.get("outcome") == "declined" and trusted_decline is not True:
        out["outcome"] = "failed"
    actual = out.get("actual_cost")
    # A malformed amount is left for the kernel to reject. Well-formed amounts compare as digit strings,
    # since int() refuses more than 4300 digits.
    if (isinstance(reservation, str) and isinstance(actual, str) and _AMOUNT.fullmatch(reservation)
            and _AMOUNT.fullmatch(actual) and (len(actual), actual) < (len(reservation), reservation)):
        out["actual_cost"] = reservation
    return out


def _whole(v: object) -> object:
    """A float with an integral value as an int, as `Kernel.inspect` takes its time; anything else unchanged."""
    if isinstance(v, float) and v.is_integer():
        return int(v)
    return v


def _map(v: object) -> object:
    """A dict copy of any Mapping, which `canonicalize` would refuse unless it is a dict; anything else unchanged."""
    return dict(v) if isinstance(v, Mapping) else v


def _strs(v: object, path: str) -> object:
    """A list copy of a sequence of strings. A bare str is a sequence too, of characters, so it is refused."""
    if isinstance(v, str):
        raise WritInputError("expected a sequence of strings, got a str", path)
    return list(v) if isinstance(v, Sequence) else v


def _approvers(v: object) -> object:
    if not isinstance(v, Mapping):
        return v
    out: dict[object, object] = {}
    for k, a in v.items():
        if isinstance(a, Mapping):
            a = dict(a)
            if "roles" in a:
                a["roles"] = _strs(a["roles"], f"approvers.{k}.roles")
        out[k] = a
    return out


def _present(d: Mapping[str, Any]) -> JsonObject:
    """An event body without its absent optional fields: None would be sent as JSON null."""
    return {k: v for k, v in d.items() if v is not None}


@dataclass
class _Current:
    policy_text: str
    """The text of the policy the session runs under: the gate's, or a retired one."""
    state: str
    state_version: int
    expected: int | None
    """None while the session record does not exist."""
    principal: str
    last_seq: int
    last_time: int
    ledger_version: int
    policy_digest: str
    ended: bool
    calls: Mapping[str, Any]


@dataclass
class _Clamp:
    trusted_decline: bool
    reservation: str | None


@dataclass
class _Plan:
    body: JsonObject
    baseline: int
    """The ledger version the step read: the state's, or the one a session_start or ledger_sync brings in."""
    expected_ledger: int | None
    write_ledger: bool
    reload_on_ledger_conflict: bool = False
    incoming: str | None = None
    """The ledger text a session_start brings in, counted against the state budget."""
    clamp: _Clamp | None = None


@dataclass
class _Mode:
    kind: Literal["event", "sync", "end"]
    verdict: Verdict = field(default_factory=dict)
    expected_ledger: int | None = None


MAX_COMMITS: Final = 5

_GROWTH: Final = frozenset({
    "session_start", "propose", "approve", "grant_create", "approver_attest", "permission_add", "dispatch",
})

Access = Literal["live", "settle"]
"""`"settle"` marks the methods a session under a retired policy still accepts."""

MAX_PRINCIPAL_BYTES: Final = 512


def _bytes_of(s: str) -> int:
    return len(s.encode("utf-8"))


def _principal_of(p: object) -> str:
    if not isinstance(p, str) or p == "":
        raise WritInputError("expected a non-empty string", "principal")
    try:
        n = _bytes_of(p)
    except UnicodeEncodeError:
        raise WritInputError("string contains a lone surrogate", "principal") from None
    if n > MAX_PRINCIPAL_BYTES:
        raise WritInputError(f"{n} UTF-8 bytes, over the limit of {MAX_PRINCIPAL_BYTES}", "principal")
    return p


def _current(policy_text: str, state: str, state_version: int, expected: int | None, principal: str) -> _Current:
    # Read only. The gate never edits state.
    s = json.loads(state)
    ledger = s.get("ledger") or {}
    return _Current(
        policy_text=policy_text, state=state, state_version=state_version, expected=expected, principal=principal,
        last_seq=s["last_seq"], last_time=s["last_time"], ledger_version=ledger.get("version", 0),
        policy_digest=s["policy_digest"], ended=s.get("ended") is True, calls=s.get("calls") or {},
    )


def _parse_ledger(r: LedgerRecord | None) -> JsonObject:
    if r is None:
        return {}
    return cast(JsonObject, parse_strict(r.text))


def _checked(kernel: KernelLike, text: object, path: str) -> str:
    if not isinstance(text, str):
        raise WritInputError("expected policy text", path)
    try:
        r = kernel.check(text)
    except WritInputError as e:
        raise WritInputError(str(e).removeprefix("policy_text: "), path) from None
    if r.errors:
        first = r.errors[0]
        raise WritInputError(f"policy fails check: {first.code}: {first.message}", path)
    return kernel.digest(text)


@dataclass(frozen=True)
class _MeterIdentity:
    currency: str | None
    window: object


def _principal_meters(text: str) -> dict[str, _MeterIdentity]:
    """Kind, currency and `window_ms` of each principal-scope meter; read from a policy that passed `check`."""
    policy: Any = parse_strict(text)
    meters = policy.get("meters") or {}
    return {name: _MeterIdentity(m.get("currency"), m.get("window_ms"))
            for name, m in meters.items() if m.get("scope") == "principal"}


def _kind_text(c: str | None) -> str:
    return "a calls meter" if c is None else f"money in {canonicalize(c)}"


def _window_text(w: object) -> str:
    return "no window_ms" if w is None else f"window_ms {canonicalize(w)}"


def _identity_mismatch(name: str, here: _MeterIdentity, there: _MeterIdentity, there_path: str) -> str | None:
    kind = here.currency != there.currency
    window = here.window != there.window
    if not kind and not window:
        return None
    if kind and window:
        what = (f"is {_kind_text(here.currency)} with {_window_text(here.window)} here, "
                f"but {there_path} makes it {_kind_text(there.currency)} with {_window_text(there.window)}")
    elif kind:
        what = f"is {_kind_text(here.currency)} here, but {there_path} makes it {_kind_text(there.currency)}"
    else:
        what = f"has {_window_text(here.window)} here, but {there_path} gives it {_window_text(there.window)}"
    return (f'principal meter "{name}" {what}; policies that share a principal ledger need the same kind, currency '
            f"and window_ms for each shared principal meter, so rename the meter to change any of them")


def _system_clock() -> int:
    return time.time_ns() // 1_000_000


class Gate:
    """Steps sessions against a `Store`, committing every accepted step before it returns. Make one with
    `create_gate`.

    Every method that steps returns at least a `GateResult`. Refusals are returned, not raised: a rejected
    verdict writes nothing, and a denial is an accepted, committed step.
    """

    def __init__(self, *, kernel: KernelLike, policy_text: str, store: Store, clock: Clock | None = None,
                 ledger_scope: Literal["principal", "none"] = "principal", max_state_bytes: int | None = None,
                 retired_policy_texts: Sequence[str] = ()) -> None:
        self._kernel = kernel
        self._policy_text = policy_text
        self._store = store
        self._clock = _system_clock if clock is None else clock
        if ledger_scope not in ("principal", "none"):
            raise WritInputError('expected "principal" or "none"', "ledger_scope")
        self._shared = ledger_scope == "principal"
        store_max = getattr(store, "max_state_bytes", None)
        # A budget above the store's would let the store refuse a kill or end before the headroom check runs.
        budget: object
        if max_state_bytes is not None and store_max is not None:
            budget = min(max_state_bytes, store_max)
        elif max_state_bytes is not None:
            budget = max_state_bytes
        elif store_max is not None:
            budget = store_max
        else:
            budget = MAX_INPUT_BYTES // 2
        budget = _whole(budget)
        if not isinstance(budget, int) or isinstance(budget, bool) or not 0 < budget <= MAX_SAFE_INTEGER:
            raise WritInputError(f"expected a positive integer of bytes, got {budget!r}", "max_state_bytes")
        self._max_state_bytes = budget
        self._headroom = budget * 7 // 8
        self._policy_digest = _checked(kernel, policy_text, "policy_text")
        self._retired: dict[str, str] = {}
        if isinstance(retired_policy_texts, str):
            raise WritInputError("expected a sequence of policy texts", "retired_policy_texts")
        seen: list[tuple[str, dict[str, _MeterIdentity]]] = [("policy_text", _principal_meters(policy_text))]
        for i, text in enumerate(retired_policy_texts):
            path = f"retired_policy_texts[{i}]"
            d = _checked(kernel, text, path)
            meters = _principal_meters(text)
            # Ledger entries carry only a meter name and an amount, so a shared meter that changes kind or
            # currency sums unlike amounts; each session also prunes by its own policy's window, so a window
            # mismatch lets one policy drop entries the other still counts.
            for earlier_path, earlier in seen:
                for name, m in meters.items():
                    there = earlier.get(name)
                    msg = None if there is None else _identity_mismatch(name, m, there, earlier_path)
                    if msg is not None:
                        raise WritInputError(msg, path)
            seen.append((path, meters))
            if d != self._policy_digest and d not in self._retired:
                self._retired[d] = text

    def _now(self, last_time: int) -> int:
        t = _whole(self._clock())
        if not isinstance(t, int) or isinstance(t, bool) or not -MAX_SAFE_INTEGER <= t <= MAX_SAFE_INTEGER:
            raise TypeError(f"clock returned {t!r}, expected integer milliseconds")
        return max(last_time, t)

    def _load(self, session_id: str, requester: str, access: Access) -> _Current:
        stored = self._store.load(session_id)
        if stored is None:
            init = self._kernel.initial(self._policy_text, self._policy_digest)
            return _current(self._policy_text, init.state, init.state_version, None, requester)
        return self._resolve(session_id, stored, access)

    def _resolve(self, session_id: str, stored: Stored, access: Access) -> _Current:
        cur = _current(self._policy_text, stored.state, stored.state_version, stored.state_version, stored.principal)
        if cur.policy_digest == self._policy_digest:
            return cur
        text = self._retired.get(cur.policy_digest)
        if text is None:
            raise WritPolicyChangedError(
                f"session {session_id} runs under policy {cur.policy_digest}, which this gate neither runs nor "
                "lists as retired", session_id, cur.policy_digest)
        if access != "settle":
            raise WritPolicyChangedError(
                f"session {session_id} runs under the retired policy {cur.policy_digest}: only end, kill, result, "
                "outcome_unknown, reconcile and inspect", session_id, cur.policy_digest)
        cur.policy_text = text
        return cur

    def _full(self, session_id: str, n: int, limit: int, what: str) -> WritStateFullError:
        return WritStateFullError(
            f"session {session_id}: {what} is {n} UTF-8 bytes, over the limit of {limit} "
            f"(budget {self._max_state_bytes}); end the session and start a new one", session_id, n, limit)

    def _plan(self, cur: _Current, body: JsonObject) -> _Plan:
        # Version 0 is the empty ledger, which is never stored.
        return _Plan(body=body, baseline=cur.ledger_version,
                     expected_ledger=cur.ledger_version if self._shared and cur.ledger_version != 0 else None,
                     write_ledger=self._shared)

    def _brought(self, body: JsonObject, record: LedgerRecord | None) -> _Plan:
        return _Plan(body=body, baseline=0 if record is None else record.version,
                     expected_ledger=None if record is None else record.version, write_ledger=self._shared,
                     incoming=None if record is None else record.text)

    def _attempt(self, session_id: str, make: Callable[[_Current], _Plan], access: Access,
                 requester: str) -> tuple[GateResult, bool]:
        """Returns the result and whether a forced `session_end` was committed in place of the step."""
        kernel, store = self._kernel, self._store
        cur = self._load(session_id, requester, access)
        mode = _Mode("event")
        failed = 0
        while True:
            if mode.kind == "event":
                p = make(cur)
                if p.body["type"] in _GROWTH:
                    n = _bytes_of(cur.state) + (_bytes_of(p.incoming or "") if p.body["type"] == "session_start" else 0)
                    if n > self._headroom:
                        raise self._full(session_id, n, self._headroom, f"the stored state before {p.body['type']}")
            elif mode.kind == "sync":
                record = store.load_ledger(cur.principal)
                p = self._brought({"type": "ledger_sync", "ledger": _parse_ledger(record)}, record)
            else:
                # The stored ledger moved on without this session; its state can only be ended.
                p = _Plan(body={"type": "session_end"}, baseline=cur.ledger_version,
                          expected_ledger=mode.expected_ledger, write_ledger=False)
            event = {**p.body, "seq": cur.last_seq + 1, "time": self._now(cur.last_time),
                     "state_version": cur.state_version}
            if p.clamp is not None:
                event = _clamp_untrusted(event, p.clamp.trusted_decline, p.clamp.reservation)
            r = kernel.step(cur.policy_text, cur.state, event)
            if mode.kind == "sync" and r.verdict["verdict"] == "rejected" and r.verdict["reason"] == "ledger_conflict":
                mode = _Mode("end", r.verdict, p.expected_ledger)
                continue
            verdict = mode.verdict if mode.kind == "end" else r.verdict
            ended = mode.kind == "end"
            if not r.changed:
                return _gate_result(verdict, r.state_version), False
            # `changed` alone is not trusted: only an accepted step is stored, including the forced session_end.
            if r.verdict["verdict"] != "accepted":
                return _gate_result(verdict, cur.state_version), False
            n = _bytes_of(r.state)
            if n > self._max_state_bytes:
                raise self._full(session_id, n, self._max_state_bytes, f"the state after {event['type']}")
            outcome = store.commit(Commit(
                session_id=session_id, state=r.state, state_version=r.state_version,
                expected_state_version=cur.expected, principal=cur.principal,
                ledger=(LedgerRecord(r.ledger, r.ledger_version)
                        if p.write_ledger and r.ledger_version != p.baseline else None),
                expected_ledger_version=p.expected_ledger,
            ))
            if outcome == "ok":
                if mode.kind != "sync":
                    return _gate_result(verdict, r.state_version), ended
                cur = _current(cur.policy_text, r.state, r.state_version, r.state_version, cur.principal)
                mode = _Mode("event")
                continue
            if outcome not in ("state_conflict", "ledger_conflict"):
                raise RuntimeError(f"store.commit returned {outcome!r}")
            if outcome == "ledger_conflict" and not self._shared:
                raise WritConflictError(
                    f'principal {cur.principal} has a stored ledger, but this gate runs with ledger_scope "none"')
            failed += 1
            if failed >= MAX_COMMITS:
                raise WritConflictError(f"session {session_id}: {MAX_COMMITS} commits in a row conflicted")
            if outcome == "state_conflict" or p.reload_on_ledger_conflict:
                cur = self._load(session_id, requester, access)
                mode = _Mode("event")
            else:
                mode = _Mode("sync")

    def _run(self, session_id: str, make: Callable[[_Current], _Plan], access: Access = "live",
             requester: str = "") -> GateResult:
        return self._attempt(session_id, make, access, requester)[0]

    def _step(self, session_id: str, body: JsonObject | Callable[[_Current], JsonObject],
              access: Access = "live") -> GateResult:
        return self._run(session_id, lambda cur: self._plan(cur, body(cur) if callable(body) else body), access)

    def _report(self, kind: Literal["result", "reconcile"], session_id: str, call_id: str, outcome: Outcome,
                actual_cost: str | None, no_effect: bool | None, untrusted: bool,
                trusted_decline: bool) -> ReportResult:
        saw_ended = False

        def send(as_: Literal["result", "reconcile"]) -> tuple[GateResult, bool]:
            def make(cur: _Current) -> _Plan:
                nonlocal saw_ended
                saw_ended = cur.ended
                p = self._plan(cur, _present({"type": as_, "call_id": call_id, "outcome": outcome,
                                              "actual_cost": actual_cost, "no_effect": no_effect}))
                if untrusted:
                    call = cur.calls.get(call_id) or {}
                    cost = call.get("cost") or {}
                    p.clamp = _Clamp(trusted_decline is True, cost.get("amount"))
                return p
            return self._attempt(session_id, make, "settle", "")

        first, first_ended = send(kind)
        fv = first.verdict
        ended_before = (kind == "result" and saw_ended and fv["verdict"] == "rejected"
                        and fv["reason"] == "session_ended")
        # An ended session accepts only reconcile (spec section 6, Ended sessions), so the call still settles here.
        r = send("reconcile")[0] if first_ended or ended_before else first
        v = r.verdict
        overrun = tuple(v["meters"]) if v["verdict"] == "accepted" and v.get("decision") == "overrun" else ()
        return ReportResult(verdict=v, state_version=r.state_version, reason=r.reason, overrun=overrun)

    def _tombstone(self, principal: object, set: bool) -> PrincipalKillResult:
        p = _principal_of(principal)
        if not self._shared:
            raise WritInputError('a gate with ledger_scope "none" keeps no principal ledgers', "ledger_scope")
        failed = 0
        while True:
            record = self._store.load_ledger(p)
            t = self._kernel.tombstone("" if record is None else record.text, set)
            if not t.changed:
                return PrincipalKillResult(t.ledger_version, False)
            outcome = self._store.commit_ledger(LedgerCommit(
                principal=p, ledger=LedgerRecord(t.ledger, t.ledger_version),
                expected_ledger_version=None if record is None else record.version))
            if outcome == "ok":
                return PrincipalKillResult(t.ledger_version, True)
            if outcome != "ledger_conflict":
                raise RuntimeError(f"store.commit_ledger returned {outcome!r}")
            failed += 1
            if failed >= MAX_COMMITS:
                raise WritConflictError(f"principal {p}: {MAX_COMMITS} ledger commits in a row conflicted")

    def start(self, session_id: str, *, requester: str, permissions: Sequence[str], approvers: Mapping[str, Approver],
              user_initiated: bool | None = None) -> GateResult:
        """Starts a session; with `user_initiated` set, also its first turn, whose result is returned."""

        def make(_: _Current) -> _Plan:
            record = self._store.load_ledger(requester) if self._shared else None
            p = self._brought({
                "type": "session_start", "session_id": session_id, "policy_digest": self._policy_digest,
                "requester": requester, "permissions": _strs(permissions, "permissions"),
                "approvers": _approvers(approvers),
                "ledger": _parse_ledger(record),
            }, record)
            # There is no session state to sync yet, so a moved ledger is simply read again.
            p.reload_on_ledger_conflict = True
            return p

        r = self._run(session_id, make, "live", requester)
        if user_initiated is None or r.verdict["verdict"] != "accepted":
            return r
        return self.turn_start(session_id, user_initiated)

    def turn_start(self, session_id: str, user_initiated: bool) -> GateResult:
        return self._step(session_id, {"type": "turn_start", "user_initiated": user_initiated})

    def turn_end(self, session_id: str) -> GateResult:
        return self._step(session_id, {"type": "turn_end"})

    def step_start(self, session_id: str) -> GateResult:
        return self._step(session_id, {"type": "step_start"})

    def propose(self, session_id: str, *, call_id: str, tool: str, call_digest: str, cost: Cost | None = None,
                guards: Mapping[str, bool] | None = None,
                escalators: Mapping[str, bool] | None = None) -> ProposeResult:
        r = self._step(session_id, _present({
            "type": "propose", "call_id": call_id, "tool": tool, "call_digest": call_digest, "cost": _map(cost),
            "guards": {} if guards is None else _map(guards),
            "escalators": {} if escalators is None else _map(escalators),
        }))
        return _propose_result(r)

    def approve(self, session_id: str, *, call_id: str, request_id: Mapping[str, Any], approver_id: str,
                reviewed_digest: str, reviewed_cost: Cost | None = None, edit: Edit | None = None) -> GateResult:
        return self._step(session_id, _present({
            "type": "approve", "call_id": call_id, "request_id": _map(request_id), "approver": approver_id,
            "reviewed_digest": reviewed_digest, "reviewed_cost": _map(reviewed_cost),
            "edit": None if edit is None else _present({
                "new_digest": edit["new_digest"], "new_cost": _map(edit.get("new_cost")),
                "escalators": _map(edit.get("escalators") or {}),
            }),
        }))

    def reject(self, session_id: str, *, call_id: str, request_id: Mapping[str, Any], approver_id: str) -> GateResult:
        return self._step(session_id, {"type": "reject", "call_id": call_id, "request_id": _map(request_id),
                                       "approver": approver_id})

    def approval_expire(self, session_id: str, *, call_id: str, request_id: Mapping[str, Any]) -> GateResult:
        return self._step(session_id, {"type": "approval_expire", "call_id": call_id,
                                       "request_id": _map(request_id)})

    def grant_create(self, session_id: str, *, grant_id: str, approver_id: str, tool: str,
                     scope: Literal["turn", "session"], max_uses: int, reviewed_scope_digest: str,
                     call_digest: str | None = None, max_cost: Cost | None = None, not_before: int | None = None,
                     expires_at: int | None = None) -> GateResult:
        return self._step(session_id, _present({
            "type": "grant_create", "grant_id": grant_id, "approver": approver_id, "tool": tool,
            "call_digest": call_digest, "scope": scope, "max_uses": max_uses, "max_cost": _map(max_cost),
            "not_before": not_before, "expires_at": expires_at, "reviewed_scope_digest": reviewed_scope_digest,
        }))

    def grant_revoke(self, session_id: str, grant_id: str) -> GateResult:
        return self._step(session_id, {"type": "grant_revoke", "grant_id": grant_id})

    def dispatch(self, session_id: str, *, call_id: str, call_digest: str, attempt: int | None = None,
                 cost: Cost | None = None, guards: Mapping[str, bool] | None = None,
                 idempotency_key: str | None = None) -> DispatchResult:
        """Claims the call immediately before it runs.

        `attempt` defaults to the stored call's attempts plus one, read once when the call begins.
        `idempotency_key` defaults to `default_idempotency_key(principal, session_id, call_id)`, the same for
        every attempt.
        """
        # Read once: recomputed after a lost commit, it would claim a retry another writer just allowed.
        fixed = attempt

        def body(cur: _Current) -> JsonObject:
            nonlocal fixed
            if fixed is None:
                call = cur.calls.get(call_id) or {}
                fixed = (call.get("attempts") or 0) + 1
            return _present({
                "type": "dispatch", "call_id": call_id, "attempt": fixed, "call_digest": call_digest,
                "cost": _map(cost), "guards": {} if guards is None else _map(guards),
                "idempotency_key": (default_idempotency_key(cur.principal, session_id, call_id)
                                    if idempotency_key is None else idempotency_key),
            })

        r = self._step(session_id, body)
        v = r.verdict
        claimed = v["verdict"] == "accepted" and v.get("decision") == "dispatch_claimed"
        return DispatchResult(verdict=v, state_version=r.state_version, reason=r.reason, claimed=claimed)

    def result(self, session_id: str, *, call_id: str, outcome: Outcome, actual_cost: str | None = None,
               no_effect: bool | None = None, untrusted: bool = False, trusted_decline: bool = False) -> ReportResult:
        """Reports a claimed call's outcome. `untrusted` drops `no_effect`, commits at least the reservation, and
        turns `declined` into `failed` unless `trusted_decline` is set."""
        return self._report("result", session_id, call_id, outcome, actual_cost, no_effect, untrusted, trusted_decline)

    def outcome_unknown(self, session_id: str, call_id: str) -> GateResult:
        return self._step(session_id, {"type": "outcome_unknown", "call_id": call_id}, "settle")

    def reconcile(self, session_id: str, *, call_id: str, outcome: Outcome, actual_cost: str | None = None,
                  no_effect: bool | None = None, untrusted: bool = False,
                  trusted_decline: bool = False) -> ReportResult:
        return self._report("reconcile", session_id, call_id, outcome, actual_cost, no_effect, untrusted,
                            trusted_decline)

    def cancel(self, session_id: str, call_id: str) -> GateResult:
        return self._step(session_id, {"type": "cancel", "call_id": call_id})

    def escalation_ack(self, session_id: str, *, approver_id: str, escalation: int) -> GateResult:
        return self._step(session_id, {"type": "escalation_ack", "approver": approver_id, "escalation": escalation})

    def permission_add(self, session_id: str, *, permission: str, approver_id: str) -> GateResult:
        return self._step(session_id, {"type": "permission_add", "permission": permission, "approver": approver_id})

    def permission_revoke(self, session_id: str, permission: str) -> GateResult:
        return self._step(session_id, {"type": "permission_revoke", "permission": permission})

    def approver_attest(self, session_id: str, *, approver_id: str, principal: str,
                        kind: Literal["human", "automated"], roles: Sequence[str]) -> GateResult:
        return self._step(session_id, {"type": "approver_attest", "approver": approver_id, "principal": principal,
                                       "kind": kind, "roles": _strs(roles, "roles")})

    def reset(self, session_id: str) -> GateResult:
        return self._step(session_id, {"type": "reset"})

    def kill(self, session_id: str) -> GateResult:
        return self._step(session_id, {"type": "kill"}, "settle")

    def end(self, session_id: str) -> GateResult:
        return self._step(session_id, {"type": "session_end"}, "settle")

    def kill_principal(self, principal: str) -> PrincipalKillResult:
        """Sets the principal's tombstone in the stored ledger. Live sessions learn of it at their next commit."""
        return self._tombstone(principal, True)

    def clear_principal_kill(self, principal: str) -> PrincipalKillResult:
        """Clears the principal's tombstone. Live sessions that saw it set are ended at their next commit."""
        return self._tombstone(principal, False)

    def inspect(self, session_id: str) -> SessionView | None:
        """The stored session as the kernel sees it at the gate's clock, or None when none is stored.

        Reads only, and works under a retired policy too: after a crash, it lists the calls left to settle.
        """
        stored = self._store.load(session_id)
        if stored is None:
            return None
        cur = self._resolve(session_id, stored, "settle")
        return self._kernel.inspect(cur.policy_text, cur.state, self._now(cur.last_time))


def create_gate(*, kernel: KernelLike, policy_text: str, store: Store, clock: Clock | None = None,
                ledger_scope: Literal["principal", "none"] = "principal", max_state_bytes: int | None = None,
                retired_policy_texts: Sequence[str] = ()) -> Gate:
    """A gate over `store` for sessions under `policy_text`.

    `clock` returns integer milliseconds from a trusted clock (default: the system clock); a float with an
    integral value counts as that int. `ledger_scope`
    `"principal"` shares one ledger between the live sessions of a principal; `"none"` never reads or writes
    principal ledgers, so run one live session per principal. `max_state_bytes` is one session's budget of
    stored state in UTF-8 bytes (default: the store's `max_state_bytes`, else `MAX_INPUT_BYTES // 2`, and never
    above the store's). `retired_policy_texts` are earlier policies whose sessions may still be live: they can
    only be settled, ended and inspected.
    """
    return Gate(kernel=kernel, policy_text=policy_text, store=store, clock=clock, ledger_scope=ledger_scope,
                max_state_bytes=max_state_bytes, retired_policy_texts=retired_policy_texts)
