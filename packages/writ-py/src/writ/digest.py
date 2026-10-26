from __future__ import annotations

import hashlib
from collections.abc import Mapping
from typing import TypedDict

from .canonical import canonicalize
from .errors import WritInputError


class Cost(TypedDict):
    amount: str
    currency: str


class _CallFields(TypedDict):
    server: str
    tool: str
    tool_digest: str


class CallInput(_CallFields, total=False):
    """A tool call to digest. Without `args` the arguments are `{}`; `args: None` is JSON null."""

    args: object
    cost: Cost | None


def _str(v: object, path: str) -> str:
    if not isinstance(v, str):
        raise WritInputError("expected a string", path)
    return v


def call_preimage(call: CallInput) -> str:
    """The canonical `writ-call-v1` preimage. Execute these bytes, not the original arguments."""
    if not isinstance(call, Mapping):
        raise WritInputError("expected a call object")
    cost: dict[str, str] | None = None
    raw_cost = call.get("cost")
    if raw_cost is not None:
        if not isinstance(raw_cost, Mapping):
            raise WritInputError("expected an object", "cost")
        for k in raw_cost:
            if k not in ("amount", "currency"):
                raise WritInputError("unknown field", f"cost.{k}")
        cost = {"amount": _str(raw_cost.get("amount"), "cost.amount"),
                "currency": _str(raw_cost.get("currency"), "cost.currency")}
    args = canonicalize(call["args"] if "args" in call else {}, "args")
    rest = canonicalize({
        "t": "writ.call.v1",
        "server": _str(call.get("server"), "server"),
        "tool": _str(call.get("tool"), "tool"),
        "tool_digest": _str(call.get("tool_digest"), "tool_digest"),
        "cost": cost,
    })
    # "args" sorts before every other key, and the depth limit counts from args itself.
    return '{"args":' + args + "," + rest[1:]


def sha256(text: str) -> str:
    """`"sha256:"` plus the lowercase hex SHA-256 of the UTF-8 bytes of `text`."""
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def call_digest(call: CallInput) -> str:
    """`writ-call-v1`: `"sha256:"` plus the lowercase hex SHA-256 of `call_preimage(call)`."""
    return sha256(call_preimage(call))
