from __future__ import annotations

import json
from typing import Any

import pytest
from helpers import REPO, input_error, jsonl

from writ import REASONS, RETRY_CLASSES, Kernel, WritInputError, mcp_tool_approval
from writ.types import ProfileResult

VECTORS: list[dict[str, Any]] = jsonl(REPO / "corpus/profiles/mcp-tool-approval-v1.jsonl")


@pytest.mark.parametrize("v", VECTORS, ids=lambda v: v["id"])
def test_profile_vector(v: dict[str, Any], kernel: Kernel) -> None:
    inp = dict(v["input"])
    profile = inp.pop("profile")
    out = v["output"]
    assert kernel.profile(profile, inp) == ProfileResult(disposition=out.get("disposition"),
                                                         envelope=out.get("envelope"))


def test_the_vectors_cover_every_reason_code_and_every_call_status() -> None:
    assert len(VECTORS) == 179
    rejected = [v["input"]["verdict"]["reason"] for v in VECTORS
                if v["input"].get("verdict", {}).get("verdict") == "rejected"]
    assert rejected == list(REASONS)
    raw = [v["input"]["status"] for v in VECTORS if "status" in v["input"]]
    statuses = {s if isinstance(s, str) else s["status"] for s in raw}
    assert sorted(statuses) == ["authorized", "awaiting", "cancelled", "declined", "denied", "denied_at_dispatch",
                                "dispatched", "expired", "failed", "rejected", "succeeded", "unknown"]


def test_mcp_tool_approval_reads_dispositions_and_envelopes_from_the_kernel(kernel: Kernel) -> None:
    assert mcp_tool_approval.id == "mcp-tool-approval"
    assert mcp_tool_approval.disposition(kernel, "unknown") == "outcome-unknown"
    assert mcp_tool_approval.disposition(kernel, "cancelled") == "cancelled"
    assert mcp_tool_approval.disposition(kernel, {"status": "denied_at_dispatch", "reason": "grant_invalid"}) == \
        "denied-not-executed"
    assert mcp_tool_approval.disposition(kernel, "authorized") is None
    rid = {"session": "s1", "call": "c1", "generation": 1}
    assert mcp_tool_approval.envelope(kernel, {"verdict": "accepted", "state_version": 4, "decision": "needs_approval",
                                               "request_id": rid}) == {
        "reason": "insufficient_authorization", "remediation": "available", "remediationHints": [{"type": "task"}],
        "requestId": rid}
    env = mcp_tool_approval.envelope(kernel, {"verdict": "accepted", "state_version": 4, "decision": "denied",
                                              "reason": "killed", "retry": "never", "message": "ignored"})
    assert env is not None and env["remediation"] == "unavailable"
    assert list(env) == ["reason", "remediation", "code", "retry", "message"]
    assert env["code"] == "killed" and env["message"] != "ignored"
    allowed = {"verdict": "accepted", "state_version": 4, "decision": "allowed"}
    assert mcp_tool_approval.envelope(kernel, allowed) is None


def test_profile_input_errors_name_id_or_input_and_the_kernel_lives_on(kernel: Kernel) -> None:
    with input_error("id"):
        kernel.profile("writ/mcp-tool-approval", {"status": "unknown"})
    with input_error("id"):
        kernel.profile(None, {"status": "unknown"})  # type: ignore[arg-type]
    with pytest.raises(WritInputError) as e:
        kernel.profile("nope", {"status": "unknown"})
    assert str(e.value) == 'id: unknown profile "nope", expected mcp-tool-approval'
    with input_error("input"):
        kernel.profile("mcp-tool-approval", {"status": "denied"})
    with input_error("input"):
        kernel.profile("mcp-tool-approval", {})
    with input_error("input"):
        kernel.profile("mcp-tool-approval", "unknown")  # type: ignore[arg-type]
    with input_error("input.status"):
        kernel.profile("mcp-tool-approval", {"status": "\ud800"})
    assert kernel.profile("mcp-tool-approval", {"status": "succeeded"}).disposition == "approved-executed"


def test_reasons_match_schema_reasons_json_in_order() -> None:
    contract = json.loads((REPO / "schema/reasons.json").read_text(encoding="utf-8"))
    assert list(REASONS) == [r["code"] for r in contract]
    assert sorted(RETRY_CLASSES) == sorted({r["retry"] for r in contract})
    assert len(set(RETRY_CLASSES)) == len(RETRY_CLASSES)
