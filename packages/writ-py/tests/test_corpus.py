from __future__ import annotations

import subprocess
from pathlib import Path

import pytest
from helpers import NATIVE_WRIT, REPO, jsonl

from writ import Kernel

FILES = sorted((REPO / "corpus/examples").glob("*.jsonl")) + sorted((REPO / "corpus/attacks").glob("*.jsonl"))


def test_the_corpus_is_here() -> None:
    assert len([f for f in FILES if f.parent.name == "examples"]) >= 7
    assert len([f for f in FILES if f.parent.name == "attacks"]) >= 6


@pytest.mark.parametrize("path", FILES, ids=lambda p: f"{p.parent.name}/{p.name}")
def test_replay_reports_every_trace_ok(path: Path, kernel: Kernel) -> None:
    result = kernel.replay(path.read_text(encoding="utf-8"))
    want = [t["id"] for t in jsonl(path)]
    assert want
    assert [t.id for t in result.traces] == want
    for t in result.traces:
        assert (t.ok, t.mismatches) == (True, ()), t.id
    if NATIVE_WRIT.exists():
        r = subprocess.run([str(NATIVE_WRIT), "replay", str(path)], capture_output=True, text=True)
        assert r.returncode == 0, r.stderr
        assert [line[3:] for line in r.stdout.split("\n") if line.startswith("ok ")] == want


def test_replay_reports_a_mismatch(kernel: Kernel) -> None:
    path = REPO / "corpus/examples/payments.jsonl"
    text = path.read_text(encoding="utf-8").split("\n")[0].replace('"expect":{"verdict":"accepted"}',
                                                                    '"expect":{"verdict":"rejected"}', 1)
    result = kernel.replay(text)
    assert len(result.traces) == 1
    trace = result.traces[0]
    assert trace.ok is False
    assert trace.mismatches[0].step == 0
    assert "expected verdict rejected" in trace.mismatches[0].message
