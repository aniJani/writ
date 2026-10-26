from __future__ import annotations

import hashlib
import json
from typing import Any

import pytest
from helpers import REPO, compact, input_error, jsonl

from writ import CallInput, Kernel, WritInputError, call_digest, call_preimage, parse_strict, tool_digest, tool_preimage

CALL_VECTORS: list[dict[str, Any]] = jsonl(REPO / "corpus/digests/call-v1.jsonl")
TOOL_VECTORS: list[dict[str, Any]] = jsonl(REPO / "corpus/digests/tool-v1.jsonl")


def call_of(v: dict[str, Any]) -> CallInput:
    inp = v["input"]
    call: CallInput = {"server": inp["server"], "tool": inp["tool"], "tool_digest": inp["tool_digest"]}
    if "args_text" in inp:
        call["args"] = parse_strict(inp["args_text"], "args")
    elif "args" in inp:
        call["args"] = inp["args"]
    if "cost" in inp:
        call["cost"] = inp["cost"]
    return call


# Raw argument text is spliced in as is, so Lean sees duplicate keys, escapes and spellings the parser saw.
def lean_text(v: dict[str, Any]) -> str:
    inp = v["input"]
    args = inp.get("args_text", compact(inp.get("args", {})))
    return (f'{{"t":"writ.call.v1","server":{compact(inp["server"])},"tool":{compact(inp["tool"])},'
            f'"tool_digest":{compact(inp["tool_digest"])},"args":{args},"cost":{compact(inp.get("cost"))}}}')


# Lean reads -0 as the integer 0; the call digest refuses it on purpose. Lean counts depth over the
# whole preimage, so args nested 128 deep is 129 there; 1.0 and 1E2 are not integer spellings.
LEAN_SKIPS = {"depth-128", "num-1.0", "num-1E2"}
LEAN_ACCEPTS = {"err-neg-zero"}


def integer_only(x: object) -> bool:
    if isinstance(x, float):
        return x.is_integer()
    if isinstance(x, list):
        return all(map(integer_only, x))
    if isinstance(x, dict):
        return all(map(integer_only, x.values()))
    return True


def test_the_call_vectors_are_all_here() -> None:
    assert len(CALL_VECTORS) == 63
    assert len(TOOL_VECTORS) == 42


@pytest.mark.parametrize("v", [v for v in CALL_VECTORS if "error" not in v], ids=lambda v: v["id"])
def test_call_vector(v: dict[str, Any], kernel: Kernel) -> None:
    call = call_of(v)
    assert call_preimage(call) == v["canonical"]
    assert call_digest(call) == v["digest"]
    assert v["digest"] == "sha256:" + hashlib.sha256(v["canonical"].encode("utf-8")).hexdigest()
    if integer_only(call.get("args", {})) and v["id"] not in LEAN_SKIPS:
        assert kernel.canonical(lean_text(v)) == v["canonical"]


@pytest.mark.parametrize("v", [v for v in CALL_VECTORS if "error" in v], ids=lambda v: v["id"])
def test_call_vector_is_refused(v: dict[str, Any], kernel: Kernel) -> None:
    with input_error(v["error"]["path"]):
        call_digest(call_of(v))
    if "args_text" in v["input"] and v["id"] not in LEAN_ACCEPTS:
        with pytest.raises(WritInputError):
            kernel.canonical(lean_text(v))


def test_call_digest_normalizes_missing_args_to_an_empty_object_and_checks_its_fields() -> None:
    base: CallInput = {"server": "s", "tool": "t", "tool_digest": "d"}
    assert call_digest(base) == call_digest({**base, "args": {}}) == call_digest({**base, "args": {}, "cost": None})
    assert call_preimage({**base, "args": None}).startswith('{"args":null,')
    for path, call in (
        ("args.n", {**base, "args": {"n": float("nan")}}),
        ("server", {**base, "server": "\ud800"}),
        ("server", {"tool": "t", "tool_digest": "d"}),
        ("tool_digest", {**base, "tool_digest": 5}),
        ("cost", {**base, "cost": "12"}),
        ("cost.currency", {**base, "cost": {"amount": "1"}}),
        ("cost.extra", {**base, "cost": {"amount": "1", "currency": "USD", "extra": 1}}),
    ):
        with input_error(path):
            call_digest(call)  # type: ignore[arg-type]


def test_call_digest_refuses_a_call_that_is_not_a_mapping() -> None:
    for bad in (None, 5, "x", ["server"]):
        with input_error(""):
            call_digest(bad)  # type: ignore[arg-type]
        with input_error(""):
            call_preimage(bad)  # type: ignore[arg-type]


def first_tool(text: str) -> object:
    def no_constants(name: str) -> object:
        raise ValueError(f"{name} is not JSON")

    doc = json.loads(text, parse_constant=no_constants)
    tools = doc if isinstance(doc, list) else doc.get("tools")
    return tools[0] if isinstance(tools, list) else doc


# tool_digest takes one parsed tool, so it cannot see duplicate keys (json.loads keeps the last)
# or problems of the list around the tool.
LIST_OR_TEXT_ONLY = {"err-duplicate-key", "err-duplicate-tool-name", "err-not-a-list"}


@pytest.mark.parametrize("v", [v for v in TOOL_VECTORS if "error_contains" not in v], ids=lambda v: v["id"])
def test_tool_vector(v: dict[str, Any]) -> None:
    tool = first_tool(v["tool_text"])
    assert tool_preimage(tool) == v["canonical"]
    assert tool_digest(tool) == v["digest"]


@pytest.mark.parametrize("v", [v for v in TOOL_VECTORS if "error_contains" in v and v["id"] not in LIST_OR_TEXT_ONLY],
                         ids=lambda v: v["id"])
def test_tool_vector_is_refused(v: dict[str, Any]) -> None:
    with pytest.raises(WritInputError) as e:
        tool_digest(first_tool(v["tool_text"]))
    assert v["error_contains"] in str(e.value)


def test_reordered_keys_and_whitespace_give_one_digest_and_a_dropped_annotation_does_not() -> None:
    by = {v["id"]: v.get("digest") for v in TOOL_VECTORS}
    assert by["annotations-present"] == by["annotations-reordered"]
    assert by["annotations-present"] != by["annotations-absent"]
    assert by["tools-list-next-cursor"] == by["tools-list-meta"] == by["tools-list-unknown-key"]


def test_tool_digest_takes_python_numbers_as_their_exact_values() -> None:
    assert tool_preimage({"name": "t", "n": 10**20, "f": 1e20, "z": -0.0, "w": 2.0, "b": True}) == \
        '{"t":"writ.tool.v1","tool":{"b":true,"f":100000000000000000000,"n":100000000000000000000,"name":"t",' \
        '"w":2,"z":0}}'
    assert tool_preimage({"name": "t", "n": 10**21, "m": 123e-20}) == \
        '{"t":"writ.tool.v1","tool":{"m":1.23e-18,"n":1e+21,"name":"t"}}'
    assert tool_preimage({"name": "t", "n": 10**300}) == '{"t":"writ.tool.v1","tool":{"n":1e+300,"name":"t"}}'


def test_tool_digest_refuses_values_json_cannot_carry_and_numbers_it_cannot_print_exactly() -> None:
    for tool, path in (
        ({"name": "t", "n": float("nan")}, "n"),
        ({"name": "t", "n": [float("inf")]}, "n[0]"),
        ({"name": "t", "n": 0.1 + 0.2}, "n"),
        ({"name": "t", "n": 2**60}, "n"),
        ({"name": "t", "n": 10**300 + 1}, "n"),
        ({"name": "t", "n": 10**5000 + 1}, "n"),
        ({"name": "t", "n": 10**5000}, "n"),
        ({"name": "t", "s": "\ud800"}, "s"),
        ({"name": "t", 1: "x"}, ""),
    ):
        with input_error(path):
            tool_digest(tool)
    bad: object
    for bad in (None, [], "x", 5):
        with input_error(""):
            tool_digest(bad)
    with pytest.raises(WritInputError, match="more than 15 significant digits"):
        tool_digest({"name": "t", "n": 1.234567890123456e301})
    with pytest.raises(WritInputError, match="more than 15 significant digits"):
        tool_digest({"name": "t", "n": 10**5000 + 1})
    with pytest.raises(WritInputError, match="outside 1e-300 to 1e300"):
        tool_digest({"name": "t", "n": 10**5000})
