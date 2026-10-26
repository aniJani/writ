from __future__ import annotations

import json
import threading
from collections.abc import Mapping
from typing import Any, Final

from . import _wasm
from .canonical import MAX_SAFE_INTEGER, canonicalize
from .errors import WritInputError, WritKernelError
from .types import (
    CheckResult,
    JsonObject,
    ProfileResult,
    ReplayResult,
    SessionView,
    StateEnvelope,
    StepResult,
    TombstoneResult,
    check_result,
    profile_result,
    replay_result,
    session_view,
)

_FN: Final = {"check": 1, "digest": 2, "canonical": 3, "initial": 4, "step": 5, "replay": 6, "version": 7,
              "tombstone": 8, "inspect": 9, "profile": 10}

# The kernel's `input` name of each argument, mapped to the wrapper's parameter name.
_INPUT_PATHS: Final = {
    "policy": "policy_text", "state": "state_text", "event": "event", "ledger": "ledger_text",
    "traces": "traces_text", "json": "json_text", "digest": "digest", "time": "time",
}

# `profile` sends one JSON document built from its two parameters.
_PROFILE_PATHS: Final = {"profile": "id", "json": "input"}

MAX_INPUT_BYTES: Final = 8 * 1024 * 1024
"""The most UTF-8 bytes one kernel call takes, summed over its inputs.

The heap stops at 2 GiB. At 8 MiB the WebAssembly memory peaked at 500 MB (about 60 bytes per
input byte), under a quarter of the ceiling, which leaves room for the result, for fragmentation
and for a long-lived heap.
"""

_ABORTED: Final = "kernel aborted; load a new kernel"


def _text(s: object, name: str) -> bytes:
    if not isinstance(s, str):
        raise WritInputError("expected a string", name)
    try:
        return s.encode("utf-8")
    except UnicodeEncodeError:
        raise WritInputError("string contains a lone surrogate", name) from None


def _own(e: BaseException | None) -> bool:
    return isinstance(e, (WritKernelError, WritInputError))


class Kernel:
    """The Writ kernel in one WebAssembly instance. Make one with `load_kernel()`.

    Calls are synchronous and serialized by a lock. After a trap (the module aborted, ran out of
    memory or touched memory out of bounds) the instance is in an unknown state, so that call and
    every later one raise `WritKernelError("kernel aborted; load a new kernel")`.
    """

    def __init__(self, store: Any, exports: Any) -> None:
        self._store = store
        self._ex = exports
        self._memory = exports["memory"]
        self._lock = threading.Lock()
        self._dead: BaseException | None = None
        if exports["writ_init"](store) != 0:
            raise WritKernelError("writ_init failed")

    def _call_in(self, fn: int, a: bytes, b: bytes, c: bytes) -> str:
        store, ex, memory = self._store, self._ex, self._memory
        bufs = (a, b, c)
        ptrs: list[int] = []
        out_len = 0
        result = 0
        failure: BaseException | None = None

        def alloc(n: int) -> int:
            p: int = ex["malloc"](store, n)
            # Memory growth makes malloc return 0 instead of aborting.
            if p == 0:
                raise WritKernelError("out of WebAssembly memory")
            return p

        try:
            out_len = alloc(4)
            for buf in bufs:
                ptrs.append(alloc(max(len(buf), 1)))
            for buf, p in zip(bufs, ptrs, strict=True):
                if buf:
                    memory.write(store, buf, p)
            result = ex["writ_call"](store, fn, ptrs[0], len(a), ptrs[1], len(b), ptrs[2], len(c), out_len)
            if result == 0:
                raise WritKernelError(f"writ_call({fn}) returned NULL")
            n = int.from_bytes(memory.read(store, out_len, out_len + 4), "little")
            return bytes(memory.read(store, result, result + n)).decode("utf-8")
        except BaseException as e:
            failure = e
            raise
        finally:
            # Freeing into a heap the module abandoned could trap again and hide the first error.
            if failure is None or _own(failure):
                if result != 0:
                    ex["writ_free"](store, result)
                for p in ptrs:
                    ex["free"](store, p)
                if out_len != 0:
                    ex["free"](store, out_len)

    def _call(self, fn: int, a: bytes, b: bytes = b"", c: bytes = b"") -> str:
        with self._lock:
            if self._dead is not None:
                raise WritKernelError(_ABORTED) from self._dead
            total = len(a) + len(b) + len(c)
            if total > MAX_INPUT_BYTES:
                raise WritInputError(f"inputs total {total} UTF-8 bytes, over the limit of {MAX_INPUT_BYTES}")
            try:
                return self._call_in(fn, a, b, c)
            except BaseException as e:
                if _own(e):
                    raise
                self._dead = e
                if not isinstance(e, Exception):
                    raise
                raise WritKernelError(_ABORTED) from e

    @staticmethod
    def _envelope(out: str, paths: Mapping[str, str] = _INPUT_PATHS) -> JsonObject:
        env: JsonObject = json.loads(out)
        if "error" in env:
            where = env.get("input")
            if isinstance(where, str):
                raise WritInputError(str(env["error"]), paths.get(where, where))
            raise WritKernelError(str(env["error"]))
        return env

    def version(self) -> str:
        return self._call(_FN["version"], b"")

    def check(self, policy_text: str) -> CheckResult:
        return check_result(self._envelope(self._call(_FN["check"], _text(policy_text, "policy_text"))))

    def digest(self, json_text: str) -> str:
        """The `"sha256:"` digest of the canonical form of any JSON text the kernel accepts."""
        return str(self._envelope(self._call(_FN["digest"], _text(json_text, "json_text")))["digest"])

    def canonical(self, json_text: str) -> str:
        return str(self._envelope(self._call(_FN["canonical"], _text(json_text, "json_text")))["canonical"])

    def initial(self, policy_text: str, digest: str | None = None) -> StateEnvelope:
        env = self._envelope(self._call(
            _FN["initial"], _text(policy_text, "policy_text"), _text("" if digest is None else digest, "digest")))
        return StateEnvelope(state=env["state"], state_version=env["state_version"],
                             ledger_version=env["ledger_version"])

    def step(self, policy_text: str, state_text: str, event: Mapping[str, Any]) -> StepResult:
        """Steps the kernel by one event. Leave an optional event field out; None is JSON null."""
        env = self._envelope(self._call(
            _FN["step"], _text(policy_text, "policy_text"), _text(state_text, "state_text"),
            _text(canonicalize(event, "event"), "event")))
        return StepResult(state=env["state"], state_version=env["state_version"], ledger_version=env["ledger_version"],
                          verdict=env["verdict"], ledger=env["ledger"], changed=env["changed"],
                          ledger_changed=env["ledger_changed"])

    def replay(self, traces_text: str) -> ReplayResult:
        return replay_result(self._envelope(self._call(_FN["replay"], _text(traces_text, "traces_text"))))

    def tombstone(self, ledger_text: str, set: bool) -> TombstoneResult:
        """Sets or clears the ledger's tombstone; the version moves only when the flag changes.

        "" is the empty ledger.
        """
        env = self._envelope(self._call(_FN["tombstone"], _text(ledger_text, "ledger_text"), b"1" if set else b"0"))
        return TombstoneResult(ledger=env["ledger"], ledger_version=env["ledger_version"], changed=env["changed"])

    def inspect(self, policy_text: str, state_text: str, time: int) -> SessionView:
        """A read-only view of a session, with meter usage counted at `time` (milliseconds)."""
        t: object = time
        if isinstance(t, float) and t.is_integer():
            t = int(t)
        if not isinstance(t, int) or isinstance(t, bool) or not 0 <= t <= MAX_SAFE_INTEGER:
            raise WritInputError("expected a non-negative integer of milliseconds", "time")
        return session_view(self._envelope(self._call(
            _FN["inspect"], _text(policy_text, "policy_text"), _text(state_text, "state_text"),
            str(t).encode("ascii"))))

    def profile(self, id: str, input: Mapping[str, Any]) -> ProfileResult:
        """A standards profile's view of a verdict (`{"verdict": ...}`, its envelope) or of a call status
        (`{"status": ...}`, its disposition)."""
        if not isinstance(id, str):
            raise WritInputError("expected a string", "id")
        if not isinstance(input, Mapping):
            raise WritInputError("expected an object", "input")
        doc = canonicalize({**input, "profile": id}, "input")
        return profile_result(self._envelope(self._call(_FN["profile"], _text(doc, "input")), _PROFILE_PATHS))

    def _memory_bytes(self) -> int:
        return int(self._memory.data_len(self._store))

    def _heap_used(self) -> int:
        return int(self._ex["writ_heap_used"](self._store))


def _load(wasm: _wasm.WasmSource | None = None, memory_limit: int | None = None) -> Kernel:
    mod = _wasm.module(wasm)
    try:
        store, exports = _wasm.instantiate(mod, memory_limit)
        return Kernel(store, exports)
    except Exception as e:
        if _own(e):
            raise
        raise WritKernelError("kernel failed to start") from e


def load_kernel(wasm: _wasm.WasmSource | None = None) -> Kernel:
    """A new kernel on the bundled `writ.wasm`, or on `wasm` (the module's bytes or a path to it).

    A trap while the instance starts (its static constructors or `writ_init`) raises
    `WritKernelError("kernel failed to start")`, with the trap as `__cause__`.
    """
    return _load(wasm)
