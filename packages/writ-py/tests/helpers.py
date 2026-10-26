from __future__ import annotations

import json
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Any

import pytest

from writ import Kernel, WritInputError

REPO = Path(__file__).resolve().parents[3]
NATIVE_WRIT = REPO / ".lake/build/bin/writ"


def fixture(p: str) -> str:
    return (REPO / "tests/cli" / p).read_text(encoding="utf-8")


def compact(v: Any) -> str:
    """JSON.stringify's spelling: no spaces, non-ASCII raw."""
    return json.dumps(v, separators=(",", ":"), ensure_ascii=False)


def jsonl(path: Path) -> list[Any]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").split("\n") if line != ""]


def session_runner(kernel: Kernel) -> Callable[[], tuple[list[str], list[str], str]]:
    """Runs the oracle fixture session; returns the verdicts, the whole results and the final state."""
    policy = fixture("policies/simple.json")
    events = []
    # The fixture has one deliberately malformed line, which cannot be an event.
    for line in fixture("oracle-events.jsonl").split("\n"):
        if line == "":
            continue
        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            pass

    def run() -> tuple[list[str], list[str], str]:
        state = kernel.initial(policy).state
        verdicts, results = [], []
        for e in events:
            r = kernel.step(policy, state, e)
            state = r.state
            verdicts.append(compact(r.verdict))
            results.append(repr(r))
        return verdicts, results, state

    return run


@contextmanager
def input_error(path: str) -> Iterator[None]:
    with pytest.raises(WritInputError) as e:
        yield
    assert e.value.path == path, str(e.value)
