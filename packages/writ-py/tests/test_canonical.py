from __future__ import annotations

import json
import random
import shutil
import struct
import subprocess
import time
from collections import OrderedDict
from decimal import Decimal
from enum import IntEnum

import pytest
from helpers import REPO, input_error

from writ import CallInput, Kernel, WritInputError, call_digest, canonicalize, parse_strict
from writ.canonical import ecma_number

# Review focus 2: Python's own JSON habits must not reach a digest.


def test_true_and_false_are_never_numbers() -> None:
    assert canonicalize([1, True, 0, False]) == "[1,true,0,false]"
    assert canonicalize({"a": True}) != canonicalize({"a": 1})
    base: CallInput = {"server": "s", "tool": "t", "tool_digest": "d"}
    assert call_digest({**base, "args": {"n": True}}) != call_digest({**base, "args": {"n": 1}})


def test_floats_print_as_ecmascript_prints_them() -> None:
    assert canonicalize(1e-7) == "1e-7"
    assert canonicalize(1.5e-10) == "1.5e-10"
    assert canonicalize(0.000001) == "0.000001"
    assert canonicalize(123456789.125) == "123456789.125"
    assert canonicalize(0.1 + 0.2) == "0.30000000000000004"
    assert canonicalize(5e-324) == "5e-324"
    assert ecma_number(1e20 / 3) == "33333333333333330000"
    assert canonicalize(-2.5) == "-2.5"


def test_a_whole_float_is_the_integer() -> None:
    assert canonicalize(1.0) == "1"
    assert canonicalize({"a": 1.0, "b": -3.0}) == canonicalize({"a": 1, "b": -3}) == '{"a":1,"b":-3}'
    assert canonicalize(9007199254740991.0) == "9007199254740991"


def test_negative_zero_is_refused_and_zero_is_not() -> None:
    with input_error("items[3]"):
        canonicalize({"items": [0, 1, 2, -0.0]})
    assert canonicalize([0, 0.0, -0]) == "[0,0,0]"


def test_integers_past_2_53_are_refused_as_int_or_float() -> None:
    assert canonicalize([2**53 - 1, -(2**53 - 1)]) == "[9007199254740991,-9007199254740991]"
    for bad in (2**53, -(2**53), 10**400, float(2**53), 1e21):
        with input_error("n"):
            canonicalize({"n": bad})


def test_non_finite_floats_are_refused() -> None:
    for path, value in (("n", {"n": float("nan")}), ("[1]", [1, float("inf")]), ("a.b", {"a": {"b": float("-inf")}})):
        with input_error(path):
            canonicalize(value)


def test_astral_keys_sort_by_utf16_code_unit() -> None:
    # Python's own order (code points) would put U+FFFF before the emoji.
    value = {"\uffff": 4, "\U0001f600": 3, "\u00e9": 2, "a": 1}
    assert sorted(value) == ["a", "\u00e9", "\uffff", "\U0001f600"]
    assert canonicalize(value) == '{"a":1,"\u00e9":2,"\U0001f600":3,"\uffff":4}'
    assert canonicalize({"\U0001d11e": 1, "\ue000": 2}) == '{"\U0001d11e":1,"\ue000":2}'


def test_integer_like_keys_sort_as_strings_and_int_keys_are_refused() -> None:
    value = {"10": 1, "9": 2, "01": 3, "a": 4, "1": 5, "-1": 6, "1.5": 7}
    assert canonicalize(value) == '{"-1":6,"01":3,"1":5,"1.5":7,"10":1,"9":2,"a":4}'
    # json.dumps turns 1 into "1" and True into "true"; each would collide with a str key.
    for bad in ({1: "x"}, {True: "x"}, {None: 1}, {1.5: 2}, {("a",): 1}):
        with input_error("o"):
            canonicalize({"o": bad})


def test_escapes_follow_rfc_8785() -> None:
    assert canonicalize('"\\/\b\f\n\r\t\x00\x1f\x7f\u2028\U0001f600') == \
        '"\\"\\\\/\\b\\f\\n\\r\\t\\u0000\\u001f\x7f\u2028\U0001f600"'


def test_values_json_cannot_carry_are_refused_with_a_path() -> None:
    cyclic: dict[str, object] = {}
    cyclic["self"] = cyclic

    class Point:
        x = 1

    class Small(IntEnum):
        ONE = 1

    cases: list[tuple[str, object, str]] = [
        ("bytes", {"b": b"x"}, "b"),
        ("set", {"s": {1}}, "s"),
        ("Decimal", {"d": Decimal("1.5")}, "d"),
        ("object", {"items": [{"a": 1}, {"p": Point()}]}, "items[1].p"),
        ("lone surrogate", {"s": "\ud800"}, "s"),
        ("lone surrogate key", {"\udc00": 1}, "\udc00"),
        ("surrogate pair as code points", [chr(0xD83D) + chr(0xDE00)], "[0]"),
        ("cycle", cyclic, ".".join(["self"] * 128)),
    ]
    for name, value, path in cases:
        with pytest.raises(WritInputError) as e:
            canonicalize(value)
        assert e.value.path == path, name
    assert canonicalize({"n": Small.ONE}) == '{"n":1}'
    assert canonicalize(OrderedDict([("b", 1), ("a", (2, 3))])) == '{"a":[2,3],"b":1}'


def test_depth_128_is_accepted_and_129_refused() -> None:
    def nest(n: int, wrap: object) -> object:
        v: object = 1
        for _ in range(n):
            v = [v] if wrap == "list" else {"a": v}
        return v

    canonicalize(nest(128, "list"))
    canonicalize(nest(128, "dict"))
    with input_error("[0]" * 128):
        canonicalize(nest(129, "list"))
    with input_error(".".join(["a"] * 128)):
        canonicalize(nest(129, "dict"))


def test_canonicalize_prefixes_error_paths_with_the_root() -> None:
    with input_error("event.a[0]"):
        canonicalize({"a": [float("nan")]}, "event")


def test_canonicalize_output_for_plain_values() -> None:
    assert canonicalize({"b": [1, "x", None, True], "a": {"d": 0.5, "c": ""}}) == \
        '{"a":{"c":"","d":0.5},"b":[1,"x",null,true]}'


def test_parse_strict_keeps_numbers_as_written_kinds() -> None:
    assert parse_strict("[1.0, 1E2, 100e-2, 4.50, 7, -0.5]") == [1, 100, 1, 4.5, 7, -0.5]
    ints = parse_strict("[7, 9007199254740991, -1]")
    assert isinstance(ints, list) and all(type(x) is int for x in ints)
    floats = parse_strict("[1.0, 1e2]")
    assert isinstance(floats, list) and all(type(x) is float for x in floats)
    assert canonicalize(parse_strict('{"b":1.0,"a":1e-7}')) == '{"a":1e-7,"b":1}'


def test_parse_strict_refuses_duplicates_after_unescaping() -> None:
    with input_error("args.a"):
        parse_strict('{"a":1,"\\u0061":2}', "args")
    with input_error("args.x[0].k"):
        parse_strict('{"x":[{"k":1,"k":2}]}', "args")


def test_parse_strict_joins_surrogate_escapes_and_refuses_lone_ones() -> None:
    assert parse_strict('"\\ud83d\\ude00"') == "\U0001f600"
    assert parse_strict('{"\\ud834\\udd1e":"\U0001d11e"}') == {"\U0001d11e": "\U0001d11e"}
    with input_error("args"):
        parse_strict('"\\ud800"', "args")
    with input_error("args"):
        parse_strict('"\\ude00\\ud83d"', "args")
    with input_error("args.a.s"):
        parse_strict('{"a":{"s":"\ud800"}}', "args")
    with input_error("args.\ud800"):
        parse_strict('{"\\ud800":1}', "args")


def test_an_error_message_never_holds_a_lone_surrogate_but_its_path_does() -> None:
    with pytest.raises(WritInputError) as e:
        parse_strict('{"\\ud800":1}', "args")
    assert e.value.path == "args.\ud800"
    assert str(e.value).startswith("args.\\ud800: object key contains a lone surrogate")
    str(e.value).encode("utf-8")


def test_parse_strict_refuses_non_string_input() -> None:
    for bad in (5, b"{}", None):
        with input_error("args"):
            parse_strict(bad, "args")  # type: ignore[arg-type]


def test_parse_strict_error_offsets_count_utf16_code_units() -> None:
    with pytest.raises(WritInputError) as e:
        parse_strict('["\U0001f600", x]')
    assert str(e.value) == "invalid JSON at offset 7"


def test_parse_strict_handles_a_1_mb_number_literal_in_linear_time() -> None:
    for text in ("0.1" + "0" * 1_000_000 + "1", "1" + "0" * 1_000_000, "0." + "0" * 1_000_000,
                 "1e-" + "1" * 5000, "0e" + "9" * 5000, "1e0" + "0" * 5000 + "1"):
        t0 = time.perf_counter()
        try:
            parse_strict(text, "args")
        except WritInputError:
            pass
        assert time.perf_counter() - t0 < 2, text[:20]
    assert parse_strict("1e0" + "0" * 5000 + "1") == 10


def test_a_number_that_does_not_round_trip_is_refused_with_advice() -> None:
    for text in ("0.10000000000000001", "0.1000000000000000055511151231257827021181583404541015625",
                 "9007199254740991.2", "1e-" + "1" * 5000):
        with pytest.raises(WritInputError) as e:
            parse_strict(f"[{text}]", "args")
        assert str(e.value) == \
            "args[0]: number has more precision than a double holds or does not round-trip; carry it as a string"


def test_canonicalize_equals_kernel_canonical_on_every_integer_only_cli_policy(kernel: Kernel) -> None:
    compared = 0
    for f in sorted((REPO / "tests/cli/policies").glob("*.json")):
        text = f.read_text(encoding="utf-8")
        try:
            want = kernel.canonical(text)
        except WritInputError:
            continue
        assert canonicalize(parse_strict(text)) == want, f.name
        compared += 1
    assert compared >= 10


@pytest.mark.skipif(shutil.which("node") is None, reason="node is not installed")
def test_ecma_number_agrees_with_node_on_random_doubles() -> None:
    rng = random.Random(8785)
    xs = [1e21, 1e-7, 1e-6, 123e-20, 5e-324, 1.7976931348623157e308, 2**53, 0.1, 100, 1e20 / 3]
    xs += [struct.unpack("<d", rng.getrandbits(64).to_bytes(8, "little"))[0] for _ in range(3000)]
    xs += [rng.uniform(-1e6, 1e6) for _ in range(1000)]
    xs += [float(rng.randint(-10**22, 10**22)) * 10.0 ** rng.randint(-30, 0) for _ in range(1000)]
    xs = [x for x in xs if x == x and abs(x) != float("inf")]
    script = "const xs = JSON.parse(require('fs').readFileSync(0, 'utf8')); " \
             "process.stdout.write(JSON.stringify(xs.map((x) => String(Number(x)))))"
    out = subprocess.run(["node", "-e", script], input=json.dumps([repr(x) for x in xs]),
                         capture_output=True, text=True, check=True).stdout
    want = json.loads(out)
    misses = [(repr(x), w, ecma_number(x)) for x, w in zip(xs, want, strict=False) if w != ecma_number(x)]
    assert not misses, misses[:5]
