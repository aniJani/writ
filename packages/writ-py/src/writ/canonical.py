"""RFC 8785 canonical JSON with I-JSON checks, and a strict parser under the same limits.

Values are Python's JSON values: dict with str keys, list or tuple, str, int, float, bool and None.
"""

from __future__ import annotations

import math
import re
from collections.abc import Callable
from typing import Final

from .errors import WritInputError

MAX_DEPTH: Final = 128
MAX_SAFE_INTEGER: Final = 2**53 - 1

NumberRule = Callable[[float, str], str]
"""Prints a float, or raises `WritInputError` at the path."""

IntRule = Callable[[int, str], str]
"""Prints an int (never a bool), or raises `WritInputError` at the path."""


def _child(path: str, key: str) -> str:
    return key if path == "" else f"{path}.{key}"


def ecma_number(x: float) -> str:
    """`Number.prototype.toString` of a double (ECMA-262 Number::toString), which RFC 8785 uses."""
    if x != x:
        return "NaN"
    if math.isinf(x):
        return "Infinity" if x > 0 else "-Infinity"
    if x == 0:
        return "0"
    sign = "-" if x < 0 else ""
    # repr gives the shortest digits that round-trip, as ECMAScript requires; only the layout differs.
    mantissa, _, exp_text = repr(abs(x)).partition("e")
    whole, _, frac = mantissa.partition(".")
    raw = whole + frac
    stripped = raw.lstrip("0")
    digits = stripped.rstrip("0")
    k = len(digits)
    # The value is 0.<digits> * 10^n.
    n = len(whole) + int(exp_text or "0") - (len(raw) - len(stripped))
    if k <= n <= 21:
        body = digits + "0" * (n - k)
    elif 0 < n <= 21:
        body = digits[:n] + "." + digits[n:]
    elif -6 < n <= 0:
        body = "0." + "0" * -n + digits
    else:
        e = n - 1
        exp = ("+" if e >= 0 else "-") + str(abs(e))
        body = (digits if k == 1 else digits[0] + "." + digits[1:]) + "e" + exp
    return sign + body


def _well_formed(s: str) -> bool:
    try:
        s.encode("utf-8")
    except UnicodeEncodeError:
        return False
    return True


_ESCAPES: Final = {'"': '\\"', "\\": "\\\\", "\b": "\\b", "\f": "\\f", "\n": "\\n", "\r": "\\r", "\t": "\\t"}
_NEEDS_ESCAPE: Final = re.compile(r'["\\\x00-\x1f]')


def _quote(s: str, path: str, what: str) -> str:
    if not _well_formed(s):
        raise WritInputError(f"{what} contains a lone surrogate", path)
    return '"' + _NEEDS_ESCAPE.sub(lambda m: _ESCAPES.get(m[0]) or f"\\u{ord(m[0]):04x}", s) + '"'


def _utf16_order(key: str) -> bytes:
    return key.encode("utf-16-be", "surrogatepass")


def _check_float(n: float, path: str) -> None:
    if not math.isfinite(n):
        raise WritInputError("number is not finite", path)
    if n == 0 and math.copysign(1.0, n) < 0:
        raise WritInputError("negative zero is not allowed", path)
    if n.is_integer() and abs(n) > MAX_SAFE_INTEGER:
        raise WritInputError("integer outside plus or minus 2^53 - 1 (carry it as a string)", path)


def _call_float(n: float, path: str) -> str:
    _check_float(n, path)
    return ecma_number(n)


def _call_int(n: int, path: str) -> str:
    if abs(n) > MAX_SAFE_INTEGER:
        raise WritInputError("integer outside plus or minus 2^53 - 1 (carry it as a string)", path)
    return str(n)


def _type_error(value: object, path: str) -> WritInputError:
    name = type(value).__name__
    if name == "Decimal":
        return WritInputError("Decimal is not a JSON value (carry it as a string or a float)", path)
    return WritInputError(f"{name} is not a JSON value (use dict, list, tuple, str, int, float, bool or None)", path)


def _write(value: object, path: str, depth: int, num: NumberRule, integer: IntRule) -> str:
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, str):
        return _quote(value, path, "string")
    if isinstance(value, int):
        return integer(int(value), path)
    if isinstance(value, float):
        return num(float(value), path)
    if isinstance(value, (list, tuple)):
        if depth >= MAX_DEPTH:
            raise WritInputError(f"nesting deeper than {MAX_DEPTH} levels", path)
        items = [_write(v, f"{path}[{i}]", depth + 1, num, integer) for i, v in enumerate(value)]
        return "[" + ",".join(items) + "]"
    if isinstance(value, dict):
        for k in value:
            if not isinstance(k, str):
                # json.dumps would print 1 as "1" and True as "true", so two dicts could share a digest.
                raise WritInputError(f"object key {k!r} is not a str", path)
        if depth >= MAX_DEPTH:
            raise WritInputError(f"nesting deeper than {MAX_DEPTH} levels", path)
        parts = []
        for k in sorted(value, key=_utf16_order):
            p = _child(path, k)
            parts.append(_quote(k, p, "object key") + ":" + _write(value[k], p, depth + 1, num, integer))
        return "{" + ",".join(parts) + "}"
    raise _type_error(value, path)


def canonicalize(value: object, root: str = "") -> str:
    """RFC 8785 canonical JSON with I-JSON checks. Error paths look like `items[3].name`; `root` prefixes them.

    Keys sort by UTF-16 code unit. Numbers print as ECMAScript prints them: `1e-7`, and a float that
    is a whole number prints without a fraction, so `1.0` and `1` are the same value. `True` is
    `true`, never `1`. Refused: a non-finite float, `-0.0`, an integer beyond plus or minus
    (2^53 - 1), a key that is not a str, a str holding a surrogate code point, nesting deeper than
    128 levels, and any other type.
    """
    return _write(value, root, 0, _call_float, _call_int)


def canonicalize_with(value: object, num: NumberRule, integer: IntRule, root: str = "") -> str:
    """`canonicalize` with other number rules, for digests other than `writ-call-v1`."""
    return _write(value, root, 0, num, integer)


_LITERAL: Final = re.compile(r"(-?)([0-9]+)(?:\.([0-9]+))?(?:[eE]([+-]?[0-9]+))?")
_NUMBER: Final = re.compile(r"-?(?:0|[1-9][0-9]*)(\.[0-9]+)?(?:[eE][+-]?[0-9]+)?")
_PLAIN: Final = re.compile(r'[^"\\\x00-\x1f]+')
_HEX4: Final = re.compile(r"[0-9a-fA-F]{4}")
_SURROGATE: Final = re.compile("[\ud800-\udfff]")
_SIMPLE_ESCAPES: Final = {'"': '"', "\\": "\\", "/": "/", "b": "\b", "f": "\f", "n": "\n", "r": "\r", "t": "\t"}


def _decimal(text: str) -> str:
    """The value as `digits e exp` with no leading or trailing zeros in digits, or "0"."""
    m = _LITERAL.fullmatch(text)
    assert m is not None
    frac = m[3] or ""
    digits = m[2] + frac
    trimmed = digits.lstrip("0")
    end = len(trimmed.rstrip("0"))
    if end == 0:
        return "0"
    exp_text = (m[4] or "0").lstrip("+")
    neg = exp_text.startswith("-")
    exp_digits = exp_text.lstrip("-").lstrip("0") or "0"
    if len(exp_digits) > 30:
        # No double prints with an exponent this long, so the literal cannot round-trip; int() would also refuse it.
        return "out of range"
    exp = (-1 if neg else 1) * int(exp_digits) - len(frac) + (len(trimmed) - end)
    return f"{m[1]}{trimmed[:end]}e{exp}"


def _utf16_offset(s: str, i: int) -> int:
    return i + sum(1 for c in s[:i] if ord(c) > 0xFFFF)


class _Parser:
    def __init__(self, s: str, root: str) -> None:
        self.s = s
        self.root = root
        self.i = 0

    def fail(self, msg: str, path: str | None = None) -> WritInputError:
        return WritInputError(f"{msg} at offset {_utf16_offset(self.s, self.i)}", self.root if path is None else path)

    def ws(self) -> None:
        s, i, n = self.s, self.i, len(self.s)
        while i < n and s[i] in " \t\n\r":
            i += 1
        self.i = i

    def peek(self) -> str | None:
        return self.s[self.i] if self.i < len(self.s) else None

    def literal(self, word: str, v: object) -> object:
        if not self.s.startswith(word, self.i):
            raise self.fail("invalid JSON")
        self.i += len(word)
        return v

    def value(self, path: str, depth: int) -> object:
        self.ws()
        c = self.peek()
        if c == "{":
            return self.object(path, depth)
        if c == "[":
            return self.array(path, depth)
        if c == '"':
            return self.string(path, "string")
        if c == "t":
            return self.literal("true", True)
        if c == "f":
            return self.literal("false", False)
        if c == "n":
            return self.literal("null", None)
        if c is not None and (c == "-" or "0" <= c <= "9"):
            return self.number(path)
        raise self.fail("unexpected end of input" if c is None else "invalid JSON")

    def number(self, path: str) -> int | float:
        m = _NUMBER.match(self.s, self.i)
        if m is None:
            raise self.fail("invalid number", path)
        text = m[0]
        self.i += len(text)
        n = float(text)
        _check_float(n, path)
        if _decimal(text) != _decimal(ecma_number(n)):
            raise WritInputError(
                "number has more precision than a double holds or does not round-trip; carry it as a string", path)
        if m[1] is None and "e" not in text and "E" not in text:
            return int(n)
        return n

    def string(self, path: str, what: str | None) -> str:
        s = self.s
        self.i += 1
        parts: list[str] = []
        while True:
            plain = _PLAIN.match(s, self.i)
            if plain is not None:
                parts.append(plain[0])
                self.i = plain.end()
            c = self.peek()
            if c is None:
                raise self.fail("unterminated string", path)
            if c == '"':
                self.i += 1
                break
            if c != "\\":
                raise self.fail("unescaped control character in string", path)
            e = s[self.i + 1] if self.i + 1 < len(s) else None
            if e is not None and e in _SIMPLE_ESCAPES:
                parts.append(_SIMPLE_ESCAPES[e])
                self.i += 2
                continue
            if e != "u":
                raise self.fail("invalid escape", path)
            hex4 = s[self.i + 2:self.i + 6]
            if _HEX4.fullmatch(hex4) is None:
                raise self.fail("invalid \\u escape", path)
            parts.append(chr(int(hex4, 16)))
            self.i += 6
        out = "".join(parts)
        if _SURROGATE.search(out) is not None:
            # Pairs written as two escapes (or as raw code points) become one character, as in UTF-16.
            out = out.encode("utf-16-be", "surrogatepass").decode("utf-16-be", "surrogatepass")
        if what is not None and not _well_formed(out):
            raise self.fail(f"{what} contains a lone surrogate", path)
        return out

    def array(self, path: str, depth: int) -> list[object]:
        if depth >= MAX_DEPTH:
            raise self.fail(f"nesting deeper than {MAX_DEPTH} levels", path)
        self.i += 1
        out: list[object] = []
        self.ws()
        if self.peek() == "]":
            self.i += 1
            return out
        while True:
            out.append(self.value(f"{path}[{len(out)}]", depth + 1))
            self.ws()
            c = self.peek()
            self.i += 1
            if c == "]":
                return out
            if c != ",":
                self.i -= 1
                raise self.fail("expected , or ]")

    def object(self, path: str, depth: int) -> dict[str, object]:
        if depth >= MAX_DEPTH:
            raise self.fail(f"nesting deeper than {MAX_DEPTH} levels", path)
        self.i += 1
        out: dict[str, object] = {}
        self.ws()
        if self.peek() == "}":
            self.i += 1
            return out
        while True:
            self.ws()
            if self.peek() != '"':
                raise self.fail("expected an object key")
            key_start = self.i
            key = self.string(path, None)
            p = _child(path, key)
            if not _well_formed(key):
                self.i = key_start
                raise self.fail("object key contains a lone surrogate", p)
            if key in out:
                self.i = key_start
                raise self.fail("duplicate key", p)
            self.ws()
            c = self.peek()
            self.i += 1
            if c != ":":
                self.i -= 1
                raise self.fail("expected :")
            out[key] = self.value(p, depth + 1)
            self.ws()
            c = self.peek()
            self.i += 1
            if c == "}":
                return out
            if c != ",":
                self.i -= 1
                raise self.fail("expected , or }")


def parse_strict(text: str, root: str = "") -> object:
    """Parses JSON text under the same limits as `canonicalize`, and refuses duplicate keys and trailing data.

    A number literal must round-trip through a double exactly (`4.50` and `1E2` do,
    `0.10000000000000001` does not). An integer literal gives an int, any other a float.
    Error offsets count UTF-16 code units, as in the TypeScript package.
    """
    if not isinstance(text, str):
        raise WritInputError("expected JSON text", root)
    p = _Parser(text, root)
    v = p.value(root, 0)
    p.ws()
    if p.i < len(text):
        raise p.fail("trailing data")
    return v
