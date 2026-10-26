"""The minimal path, ported from packages/writ/test/simple.test.ts under the same test names, plus the example."""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest
from helpers import input_error

from writ import Kernel, RunResult, WritInputError, simple_gate, simple_policy

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def boom() -> Any:
    raise RuntimeError("boom")


def test_simple_policy_passes_check(kernel: Kernel) -> None:
    r = kernel.check(simple_policy({"web_search": "none", "send_email": "per_call"}))
    assert r.ok is True
    assert r.warnings == ()


def test_simple_policy_emits_a_layer_1_policy_with_the_user_as_the_only_approver_role() -> None:
    assert json.loads(simple_policy({"web_search": "none", "send_email": "per_call"}, approval_ttl_ms=5000)) == {
        "writ": "0.1",
        "approver_roles": ["user"],
        "limits": {"approval_ttl_ms": 5000},
        "actions": {"web_search": {"consent": "none"}, "send_email": {"consent": "per_call"}},
    }
    assert json.loads(simple_policy({"t": "none"}))["limits"]["approval_ttl_ms"] == 600_000


def test_simple_policy_refuses_a_bad_consent_and_an_empty_map() -> None:
    with input_error("tools.a"):
        simple_policy({"a": "always"})  # type: ignore[dict-item]
    with input_error("tools"):
        simple_policy({})
    # Python adaptation: a bool and a key that is not a str are refused too, and a float with an integral value
    # is that int.
    assert json.loads(simple_policy({"t": "none"}, approval_ttl_ms=5000.0))["limits"] == {  # type: ignore[arg-type]
        "approval_ttl_ms": 5000}
    assert '"approval_ttl_ms":5000}' in simple_policy({"t": "none"}, approval_ttl_ms=5000.0)  # type: ignore[arg-type]
    for ttl in (1.5, True, -1, -1.0, float("inf")):
        with input_error("approval_ttl_ms"):
            simple_policy({"t": "none"}, approval_ttl_ms=ttl)  # type: ignore[arg-type]
    with input_error("tools"):
        simple_policy({1: "none"})  # type: ignore[dict-item]


def test_a_free_tool_runs_an_approved_tool_runs_once_an_unknown_tool_is_denied(kernel: Kernel) -> None:
    w = simple_gate({"web_search": "none", "send_email": "per_call"}, user="user:alice", kernel=kernel)
    s = w.session()
    a = s.propose("web_search", {"q": "tea"})
    assert a.status == "allowed"
    assert s.run(a, lambda: 1) == RunResult(ran=True, value=1)
    b = s.propose("send_email", {"to": "bob"})
    assert b.status == "needs_approval"
    assert b.request_id
    b = s.approve(b)
    assert b.status == "allowed"
    calls = [0]

    def once() -> int:
        calls[0] += 1
        return calls[0]

    assert s.run(b, once) == RunResult(ran=True, value=1)
    assert s.run(b, once) == RunResult(ran=False, reason="call_ended")
    assert calls[0] == 1
    c = s.propose("delete_all", {})
    assert c.status == "denied"
    assert c.reason == "unknown_tool"


def test_a_throwing_tool_is_reported_unknown_and_not_run_again(kernel: Kernel) -> None:
    w = simple_gate({"t": "none"}, user="u", kernel=kernel)
    s = w.session()
    a = s.propose("t", {})
    with pytest.raises(RuntimeError, match="boom"):
        s.run(a, boom)
    view = w.gate.inspect(s.id)
    assert view is not None
    assert next(c for c in view.calls if c.call_id == a.call_id).status == "unknown"
    ran = []
    assert s.run(a, lambda: ran.append(1)) == RunResult(ran=False, reason="retry_not_allowed")
    assert ran == []


def test_a_rejected_call_never_runs(kernel: Kernel) -> None:
    w = simple_gate({"send_email": "per_call"}, user="user:alice", kernel=kernel)
    s = w.session()
    b = s.propose("send_email", {"to": "bob"})
    assert b.status == "needs_approval"
    b = s.reject(b)
    assert b.status == "denied"
    ran = []
    assert s.run(b, lambda: ran.append(1)) == RunResult(ran=False, reason="call_ended")
    assert ran == []


def test_a_call_awaiting_approval_does_not_run(kernel: Kernel) -> None:
    w = simple_gate({"send_email": "per_call"}, user="user:alice", kernel=kernel)
    s = w.session()
    b = s.propose("send_email", {"to": "bob"})
    ran = []
    assert s.run(b, lambda: ran.append(1)) == RunResult(ran=False, reason="call_awaiting")
    assert ran == []


def test_sessions_are_separate_take_a_given_id_and_use_the_gates_clock_and_store(kernel: Kernel) -> None:
    now = [1000]
    w = simple_gate({"t": "per_call"}, user="u", approval_ttl_ms=10, clock=lambda: now[0], kernel=kernel)
    s1 = w.session("s-1")
    assert s1.id == "s-1"
    s2 = w.session()
    assert s2.id != s1.id
    a = s1.propose("t", {"n": 1})
    assert a.status == "needs_approval"
    now[0] += 11
    late = s1.approve(a)
    assert late.status == "denied"
    assert late.reason == "approval_expired"
    view = w.gate.inspect(s2.id)
    assert view is not None and len(view.calls) == 0
    with pytest.raises(WritInputError, match="already_started"):
        w.session("s-1")


def test_a_second_approve_reports_the_call_allowed_with_the_refusal_reason_and_the_call_runs_once(
        kernel: Kernel) -> None:
    w = simple_gate({"send_email": "per_call"}, user="user:alice", kernel=kernel)
    s = w.session()
    b = s.propose("send_email", {"to": "bob"})
    first = s.approve(b)
    assert first.status == "allowed"
    second = s.approve(b)
    assert second.status == "allowed"
    assert second.reason == "call_authorized"
    calls = [0]

    def once() -> int:
        calls[0] += 1
        return calls[0]

    assert s.run(second, once) == RunResult(ran=True, value=1)
    assert s.run(second, once).ran is False
    assert calls[0] == 1


def test_an_approve_with_a_wrong_digest_leaves_the_call_awaiting_with_its_request_id(kernel: Kernel) -> None:
    w = simple_gate({"send_email": "per_call"}, user="user:alice", kernel=kernel)
    s = w.session()
    b = s.propose("send_email", {"to": "bob"})
    tampered = s.approve(replace(b, call_digest="sha256:" + "0" * 64))
    assert tampered.status == "needs_approval"
    assert tampered.reason == "digest_mismatch"
    assert tampered.request_id == b.request_id
    assert tampered.call_digest == b.call_digest
    assert s.approve(tampered).status == "allowed"


def test_a_reject_after_approval_vetoes_the_call_and_a_refused_reject_keeps_the_reason(kernel: Kernel) -> None:
    w = simple_gate({"send_email": "per_call"}, user="user:alice", kernel=kernel)
    s = w.session()
    b = s.propose("send_email", {"to": "bob"})
    assert s.approve(b).status == "allowed"
    vetoed = s.reject(b)
    assert vetoed.status == "denied"
    ran = []
    assert s.run(b, lambda: ran.append(1)) == RunResult(ran=False, reason="call_ended")
    assert ran == []
    again = s.reject(b)
    assert again.status == "denied"
    assert again.reason == "call_ended"


def test_an_approve_after_the_ttl_ends_the_request(kernel: Kernel) -> None:
    now = [1000]
    w = simple_gate({"t": "per_call"}, user="u", approval_ttl_ms=10, clock=lambda: now[0], kernel=kernel)
    s = w.session()
    a = s.propose("t", {})
    now[0] += 11
    late = s.approve(a)
    assert late.status == "denied"
    assert late.reason == "approval_expired"
    assert late.request_id is None
    view = w.gate.inspect(s.id)
    assert view is not None
    assert next(c for c in view.calls if c.call_id == a.call_id).status == "expired"


def test_a_failing_outcome_unknown_does_not_hide_the_tools_error(kernel: Kernel) -> None:
    w = simple_gate({"t": "none"}, user="u", kernel=kernel)
    s = w.session()
    a = s.propose("t", {})

    def store_down(*_: object) -> Any:
        raise RuntimeError("store down")

    w.gate.outcome_unknown = store_down  # type: ignore[assignment]
    with pytest.raises(RuntimeError, match="boom"):
        s.run(a, boom)


def test_simple_policy_keeps_a_tool_named_proto(kernel: Kernel) -> None:
    text = simple_policy({"__proto__": "none"})
    assert "__proto__" in json.loads(text)["actions"]
    assert kernel.check(text).ok is True


# From packages/writ/test/example.test.ts, for the example this package has.


def test_the_minimal_example_runs_a_free_call_and_an_approved_call() -> None:
    out = subprocess.run([sys.executable, str(EXAMPLES / "minimal.py")], capture_output=True, text=True, check=True)
    assert out.stdout.rstrip("\n").split("\n") == [
        "search: RunResult(ran=True, value='3 results', reason=None)",
        "ask: Email bob@example.com?",
        "email: RunResult(ran=True, value='sent', reason=None)",
    ]


def test_the_gate_example_runs_the_readme_walk_through() -> None:
    out = subprocess.run([sys.executable, str(EXAMPLES / "gate.py")], capture_output=True, text=True, check=True)
    assert out.stdout.rstrip("\n").split("\n") == [
        "c1 shop.search: succeeded",
        "c2 shop.buy: succeeded",
        "meter spend: used 1999 of 5000",
    ]


def test_the_readme_walk_throughs_are_the_examples() -> None:
    readme = (EXAMPLES.parent / "README.md").read_text(encoding="utf-8")
    for heading, example in (("## Quick start", "minimal.py"), ("## Run a gate", "gate.py")):
        start = readme.index("```python\n", readme.index(heading)) + len("```python\n")
        block = readme[start:readme.index("```\n", start)]
        assert block in (EXAMPLES / example).read_text(encoding="utf-8"), example


def test_the_gate_and_store_names_are_exported() -> None:
    import writ

    for name in ("KernelLike", "Outcome", "SimpleStatus", "LedgerCommitOutcome", "create_gate", "simple_gate",
                 "MemoryStore", "Store", "WritStoreError", "default_idempotency_key"):
        assert name in writ.__all__ and hasattr(writ, name), name
