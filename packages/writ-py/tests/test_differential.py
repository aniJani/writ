"""The Python kernel against the native `writ oracle`, verdict by verdict and on the final state.

The random streams are packages/writ/test/differential.test.ts's, ported draw for draw, so a seed
gives the same events in both packages.
"""

from __future__ import annotations

import json
import os
import subprocess
from collections import Counter
from collections.abc import Callable
from pathlib import Path
from typing import Any, TypeVar

import pytest
from helpers import NATIVE_WRIT, REPO, compact, jsonl

from writ import Kernel

T = TypeVar("T")

STREAMS = 200
EVENTS = 30
M32 = 0xFFFFFFFF

MISSING = f"native binary {NATIVE_WRIT} is missing: run lake build writ"
native = pytest.mark.skipif(not NATIVE_WRIT.exists() and os.environ.get("WRIT_REQUIRE_NATIVE") != "1", reason=MISSING)


def oracle(policy_file: Path, events: list[dict[str, Any]], state_out: Path, digest: str | None = None) -> list[str]:
    assert NATIVE_WRIT.exists(), MISSING
    args = [str(NATIVE_WRIT), "oracle", str(policy_file), "--state-out", str(state_out)]
    if digest is not None:
        args += ["--digest", digest]
    r = subprocess.run(args, input="".join(compact(e) + "\n" for e in events), capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    return [line for line in r.stdout.split("\n") if line != ""]


def corpus_traces() -> list[dict[str, Any]]:
    files = sorted((REPO / "corpus/examples").glob("*.jsonl")) + sorted((REPO / "corpus/attacks").glob("*.jsonl"))
    return [t for f in files for t in jsonl(f)]


@native
@pytest.mark.parametrize("trace", corpus_traces(), ids=lambda t: t["id"])
def test_corpus_streams_agree_with_writ_oracle(trace: dict[str, Any], kernel: Kernel, tmp_path: Path) -> None:
    policy_text = compact(trace["policy"])
    digest = trace.get("policy_digest") or kernel.digest(policy_text)
    events = [dict(step["event"]) for step in trace["events"]]
    for e in events:
        if e["type"] == "session_start":
            e.setdefault("policy_digest", digest)
    state = kernel.initial(policy_text, digest).state
    got = []
    for e in events:
        r = kernel.step(policy_text, state, e)
        state = r.state
        got.append(compact(r.verdict))
    policy_file = tmp_path / "policy.json"
    policy_file.write_text(policy_text, encoding="utf-8")
    state_out = tmp_path / "state.json"
    assert got == oracle(policy_file, events, state_out, digest)
    assert state + "\n" == state_out.read_text(encoding="utf-8")


def mulberry32(seed: int) -> Callable[[], float]:
    a = seed & M32

    def rnd() -> float:
        nonlocal a
        a = (a + 0x6D2B79F5) & M32
        t = a
        t = ((t ^ (t >> 15)) * (t | 1)) & M32
        t ^= (t + (((t ^ (t >> 7)) * (t | 61)) & M32)) & M32
        return ((t ^ (t >> 14)) & M32) / 4294967296

    return rnd


TRACE = jsonl(REPO / "corpus/examples/payments.jsonl")[0]
# payments.jsonl plus one action that needs no approval, so the allowed decision is reachable.
POLICY_TEXT = compact({**TRACE["policy"], "actions": {**TRACE["policy"]["actions"],
                                                      "report.read": {"permission": "payments"}}})
APPROVERS = TRACE["events"][0]["event"]["approvers"]
APPROVER_NAMES = list(APPROVERS)
TOOLS = ["vendor.pay", "card.charge", "card.charge", "report.read", "report.read", "wire.unknown"]
SUB_DIGEST = "d-sub-1000"
SUB_COST = {"amount": "1000", "currency": "USD"}
BIG_AMOUNTS = ["2147483648", "18446744073709551616", "9" * 78]
KINDS = [
    "session_start", "turn_start", "turn_start", "turn_end", "step_start", "step_start", "step_start",
    "propose", "propose", "propose", "propose", "propose", "propose",
    "approve", "approve", "approve", "approve", "approve", "reject",
    "dispatch", "dispatch", "dispatch", "dispatch", "result", "result", "result", "result",
    "reconcile", "ledger_sync", "grant_create", "cancel", "outcome_unknown", "approval_expire",
    "permission_add",
]
NEEDS = {"approve": "awaiting", "reject": "awaiting", "approval_expire": "awaiting", "dispatch": "authorized",
         "result": "dispatched", "reconcile": "dispatched"}


class Generator:
    def __init__(self, seed: int, digest: str) -> None:
        self.rnd = mulberry32(seed)
        # Amounts from 2^31 up are heap Nats on wasm32 and go through the runtime's own mpn code,
        # where native uses GMP. The swap draws from its own stream, so the streams keep their shape.
        self.big_rnd = mulberry32(seed ^ 0x5BD1E995)
        self.digest = digest
        self.tracked: dict[str, dict[str, Any]] = {}
        self.last_seq = 0
        self.last_time = 0
        self.next_call = 1
        self.n = 0

    def pick(self, xs: list[T]) -> T:
        return xs[int(self.rnd() * len(xs))]

    def chance(self, p: float) -> bool:
        return self.rnd() < p

    def amount(self, big: float, small: list[int]) -> str:
        usual = str(self.pick(small))
        return BIG_AMOUNTS[int(self.big_rnd() * len(BIG_AMOUNTS))] if self.big_rnd() < big else usual

    def cost(self) -> dict[str, str]:
        amount = self.amount(0.1, [100, 500, 2000, 3000])
        return {"amount": amount, "currency": "EUR" if self.chance(0.04) else "USD"}

    def in_state(self, state: str) -> list[tuple[str, dict[str, Any]]]:
        return [(k, t) for k, t in self.tracked.items() if t["state"] == state]

    def random_call(self) -> str:
        return f"c{1 + int(self.rnd() * self.next_call)}"

    def target(self, state: str, noise: float) -> tuple[str, dict[str, Any] | None]:
        live = self.in_state(state)
        if live and not self.chance(noise):
            return self.pick(live)
        return self.random_call(), None

    def any_call(self) -> str:
        if self.tracked and self.chance(0.7):
            return self.pick(list(self.tracked))
        return self.random_call()

    @staticmethod
    def request_for(call: str, t: dict[str, Any] | None) -> dict[str, Any]:
        return t["request"] if t is not None else {"session": "s1", "call": call, "generation": 0}

    def next(self, ver: int) -> dict[str, Any]:
        i = self.n
        self.n += 1
        seq = max(1, self.last_seq - int(self.rnd() * 2)) if self.chance(0.04) else self.last_seq + 1
        tm = (max(0, self.last_time - 1 - int(self.rnd() * 20)) if self.chance(0.03)
              else self.last_time + int(self.rnd() * 50))
        sv = max(0, ver + self.pick([-1, 1, 2])) if self.chance(0.05) else ver
        head: dict[str, Any] = {"seq": seq, "time": tm, "state_version": sv}
        if i == 0 and self.chance(0.95):
            kind = "session_start"
        elif self.chance(0.008):
            kind = "kill"
        else:
            kind = self.pick(KINDS)
        # Without a live call these would only produce unknown_call, so mostly propose instead.
        need = NEEDS.get(kind)
        if need and not self.in_state(need) and not self.chance(0.08):
            kind = "propose"
        e: dict[str, Any] = {**head, "type": kind}
        if kind == "session_start":
            e["session_id"] = "s1"
            e["policy_digest"] = "sha256:" + "0" * 64 if self.chance(0.03) else self.digest
            e["requester"] = "u1"
            e["permissions"] = [] if self.chance(0.1) else ["payments"]
            e["approvers"] = APPROVERS
            e["ledger"] = {}
        elif kind == "turn_start":
            e["user_initiated"] = self.chance(0.85)
        elif kind in ("turn_end", "step_start", "kill"):
            pass
        elif kind == "propose":
            if self.chance(0.9):
                call_id = f"c{self.next_call}"
                self.next_call += 1
            else:
                call_id = self.random_call()
            tool = self.pick(TOOLS)
            sub = tool == "card.charge" and self.chance(0.5)
            e.update(call_id=call_id, tool=tool, call_digest=SUB_DIGEST if sub else f"d-{call_id}")
            if self.chance(0.95):
                e["cost"] = SUB_COST if sub else self.cost()
            e.update(guards={}, escalators={})
        elif kind == "approve":
            call_id, t = self.target("awaiting", 0.08)
            e.update(call_id=call_id, request_id=self.request_for(call_id, t),
                     approver=self.pick(APPROVER_NAMES) if self.chance(0.97) else "nobody")
            e["reviewed_digest"] = t["digest"] if t is not None and not self.chance(0.05) else "d-other"
            if t is not None and t.get("cost") and not self.chance(0.05):
                e["reviewed_cost"] = t["cost"]
            elif self.chance(0.5):
                e["reviewed_cost"] = self.cost()
        elif kind == "reject":
            call_id, t = self.target("awaiting", 0.2)
            e.update(call_id=call_id, request_id=self.request_for(call_id, t), approver=self.pick(APPROVER_NAMES))
        elif kind == "dispatch":
            call_id, t = self.target("authorized", 0.1)
            e.update(call_id=call_id, attempt=1 if self.chance(0.95) else 2)
            e["call_digest"] = t["digest"] if t is not None and not self.chance(0.05) else "d-other"
            if t is not None and t.get("cost") and not self.chance(0.05):
                e["cost"] = t["cost"]
            e.update(guards={}, idempotency_key=f"k-s1-{call_id}")
        elif kind in ("result", "reconcile"):
            call_id, _ = self.target("dispatched", 0.1)
            e.update(call_id=call_id,
                     outcome=self.pick(["succeeded", "succeeded", "succeeded", "succeeded", "declined", "failed"]))
            if self.chance(0.4):
                e["actual_cost"] = self.amount(0.5, [50, 400, 1500])
            if self.chance(0.1):
                e["no_effect"] = True
        elif kind in ("cancel", "outcome_unknown"):
            e["call_id"] = self.any_call()
        elif kind == "approval_expire":
            call_id, t = self.target("awaiting", 0.3)
            e.update(call_id=call_id, request_id=self.request_for(call_id, t))
        elif kind == "ledger_sync":
            ledger: dict[str, Any] = {"version": int(self.rnd() * 4)}
            if self.chance(0.05):
                ledger["tombstone"] = True
            e["ledger"] = ledger
        elif kind == "permission_add":
            e.update(permission="payments", approver=self.pick(APPROVER_NAMES))
        elif kind == "grant_create":
            e.update(grant_id=f"g{1 + int(self.rnd() * 3)}", approver=self.pick(["mgr", "fin", "own"]),
                     tool="card.charge")
            if self.chance(0.8):
                e["call_digest"] = SUB_DIGEST
            e.update(scope="session", max_uses=1 + int(self.rnd() * 3))
            if self.chance(0.7):
                e["max_cost"] = {"amount": "2500", "currency": "USD"}
            e.update(expires_at=3600000, reviewed_scope_digest="scope-sub")
        return e

    def observe(self, e: dict[str, Any], v: dict[str, Any]) -> None:
        if v["verdict"] != "accepted":
            return
        self.last_seq = e["seq"]
        self.last_time = e["time"]
        kind = e["type"]
        if kind in ("session_start", "kill", "reset"):
            self.tracked.clear()

        def move(call_id: str, state: str | None) -> None:
            if call_id not in self.tracked:
                return
            if state is None:
                del self.tracked[call_id]
            else:
                self.tracked[call_id]["state"] = state

        decision = v.get("decision")
        if kind == "propose":
            t: dict[str, Any] = {"tool": e["tool"], "digest": e["call_digest"]}
            if e.get("cost"):
                t["cost"] = e["cost"]
            if decision == "needs_approval":
                self.tracked[e["call_id"]] = {**t, "request": v["request_id"], "state": "awaiting"}
            elif decision in ("authorized", "allowed", "allowed_by_grant"):
                self.tracked[e["call_id"]] = {**t, "request": {"session": "s1", "call": e["call_id"], "generation": 0},
                                              "state": "authorized"}
        elif kind == "approve":
            if decision == "authorized":
                move(e["call_id"], "authorized")
            elif e.get("edit"):
                self.tracked.pop(e["call_id"], None)
        elif kind in ("reject", "cancel", "approval_expire", "result", "reconcile"):
            move(e["call_id"], None)
        elif kind == "dispatch":
            if decision == "dispatch_claimed":
                move(e["call_id"], "dispatched")
        elif kind == "outcome_unknown":
            move(e["call_id"], "dispatched")


def test_mulberry32_matches_the_typescript_generator() -> None:
    # The first draws of mulberry32(1) in JavaScript.
    rnd = mulberry32(1)
    assert [rnd() for _ in range(3)] == [0.6270739405881613, 0.002735721180215478, 0.5274470399599522]
    big = mulberry32(7 ^ 0x5BD1E995)
    assert [big(), big()] == [0.6936989342793822, 0.6232406974304467]


@native
def test_seeded_streams_agree_with_writ_oracle(kernel: Kernel, tmp_path: Path) -> None:
    policy_file = tmp_path / "policy.json"
    policy_file.write_text(POLICY_TEXT, encoding="utf-8")
    checked = kernel.check(POLICY_TEXT)
    assert checked.ok, checked.errors
    digest = checked.policy_digest
    counts: Counter[str] = Counter()
    state_out = tmp_path / "state.json"
    for seed in range(1, STREAMS + 1):
        gen = Generator(seed, digest)
        state = kernel.initial(POLICY_TEXT, digest).state
        version = 0
        events = []
        got = []
        for _ in range(EVENTS):
            e = gen.next(version)
            events.append(e)
            r = kernel.step(POLICY_TEXT, state, e)
            state = r.state
            version = r.state_version
            gen.observe(e, r.verdict)
            v = r.verdict
            counts[f"{v['verdict']}:{e['type']}"] += 1
            if v["verdict"] == "accepted" and v.get("decision"):
                counts[f"decision:{v['decision']}"] += 1
            if v["verdict"] == "rejected":
                counts[f"reason:{v['reason']}"] += 1
            if r.ledger_changed:
                counts["ledger_changed"] += 1
            if v["verdict"] == "accepted" and any(f'"{a}"' in compact(e) for a in BIG_AMOUNTS):
                counts["big_amount:accepted"] += 1
            if r.changed and any(f'"{a}"' in r.state for a in BIG_AMOUNTS):
                counts["big_amount:state"] += 1
            got.append(compact(v))
        assert got == oracle(policy_file, events, state_out), f"seed {seed}: verdicts differ"
        assert state + "\n" == state_out.read_text(encoding="utf-8"), f"seed {seed}: final state differs"
    print(f"differential counts: {json.dumps(dict(sorted(counts.items())))}")
    # The TypeScript test's floors for 300 streams, scaled to 200.
    minimums = {
        "decision:dispatch_claimed": 133, "accepted:approve": 133, "accepted:result": 100, "ledger_changed": 66,
        "decision:needs_approval": 200, "decision:denied": 33, "decision:allowed": 66,
        "decision:allowed_by_grant": 13, "accepted:grant_create": 33,
        "big_amount:accepted": 133, "big_amount:state": 666,
        "reason:call_awaiting": 20, "reason:call_authorized": 26, "reason:call_dispatched": 16,
        "reason:call_ended": 26, "reason:call_unknown": 3, "reason:killed": 66,
    }
    short = {k: counts[k] for k, floor in minimums.items() if counts[k] < floor}
    assert not short, short
    assert sum(n for k, n in counts.items() if k.startswith("rejected:")) >= 666
