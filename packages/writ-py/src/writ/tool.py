from __future__ import annotations

from typing import Final

from .canonical import canonicalize_with, ecma_number
from .digest import sha256
from .errors import WritInputError

MAX_SIGNIFICANT_DIGITS: Final = 15


def _significant_digits(printed: str) -> int:
    mantissa = printed.lstrip("-").split("e")[0].replace(".", "")
    return len(mantissa.lstrip("0").rstrip("0"))


def _out_of_range(path: str) -> WritInputError:
    return WritInputError("number is outside 1e-300 to 1e300 in magnitude", path)


def _too_many_digits(path: str) -> WritInputError:
    return WritInputError(f"number has more than {MAX_SIGNIFICANT_DIGITS} significant digits", path)


# A double that came from a literal of at most 15 significant digits prints as that literal, normalized,
# so these checks refuse exactly what the Lean parser refuses for such literals.
def _tool_float(n: float, path: str) -> str:
    if n != n:
        raise WritInputError("NaN is not a JSON value", path)
    if n == 0:
        return "0"
    printed = ecma_number(n)
    # Digits before range, in Lean's order, so a number breaking both rules gets the same error.
    if abs(n) != float("inf") and _significant_digits(printed) > MAX_SIGNIFICANT_DIGITS:
        raise _too_many_digits(path)
    if abs(n) > 1e300 or abs(n) < 1e-300:
        raise _out_of_range(path)
    return printed


def _tool_int(n: int, path: str) -> str:
    """An int is its exact value: at most 15 significant digits, then printed as the double it equals."""
    if n == 0:
        return "0"
    m = abs(n)
    # Strip trailing zeros by arithmetic, since str() of a huge int is refused past 4300 digits.
    while m % 10**16 == 0:
        m //= 10**16
    while m % 10 == 0:
        m //= 10
    if m >= 10**MAX_SIGNIFICANT_DIGITS:
        raise _too_many_digits(path)
    if abs(n) > 10**300:
        raise _out_of_range(path)
    return ecma_number(float(n))


def tool_preimage(tool: object) -> str:
    """The canonical `writ.tool.v1` preimage of an MCP tool definition, every member included."""
    if not isinstance(tool, dict):
        raise WritInputError("expected a tool object")
    if "name" not in tool:
        raise WritInputError("missing field", "name")
    if not isinstance(tool["name"], str):
        raise WritInputError("expected a string", "name")
    body = canonicalize_with(tool, _tool_float, _tool_int)
    # "t" sorts before "tool", and the tool's own error paths stay rooted at the tool.
    return '{"t":"writ.tool.v1","tool":' + body + "}"


def tool_digest(tool: object) -> str:
    """`writ-tool-v1`: `"sha256:"` plus the lowercase hex SHA-256 of `tool_preimage(tool)`."""
    return sha256(tool_preimage(tool))
