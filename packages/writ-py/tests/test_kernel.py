from __future__ import annotations

import json
from dataclasses import FrozenInstanceError
from typing import Any

import pytest
import wasmtime
from helpers import REPO, compact, fixture, input_error, session_runner

from writ import MAX_INPUT_BYTES, Kernel, WritInputError, WritKernelError, _wasm, load_kernel
from writ._wasm import WASM_PATH
from writ.kernel import _load

SHOP = fixture("policies/formats-shop.json")
SHOP_DIGEST = fixture("formats-digest.out").strip()
SHOP_START = {
    "type": "session_start", "seq": 1, "time": 0, "state_version": 0, "session_id": "s1",
    "policy_digest": SHOP_DIGEST, "requester": "u1", "permissions": ["shop.read", "shop.buy"],
    "approvers": {"laptop": {"principal": "u1", "kind": "human", "roles": ["owner"]}}, "ledger": {},
}


def test_version_matches_the_native_binary(kernel: Kernel) -> None:
    assert kernel.version() == fixture("version.out").strip()


def test_check_accepts_a_valid_policy(kernel: Kernel) -> None:
    r = kernel.check(SHOP)
    assert r.ok is True
    assert r.policy_digest == SHOP_DIGEST
    assert r.errors == () and r.warnings == ()


def test_check_reports_an_invalid_policy(kernel: Kernel) -> None:
    r = kernel.check(fixture("policies/errors.json"))
    assert r.ok is False
    assert any(e.code == "unknown_meter" and e.action == "a" for e in r.errors)
    assert any(w.action is None for w in r.warnings)


def test_check_json_fixtures_match_the_native_check(kernel: Kernel) -> None:
    for name in ("ok", "errors", "warnings"):
        want = json.loads(fixture(f"check-json-{name}.out"))
        case = fixture(f"check-json-{name}.case")
        policy = next(line for line in case.split("\n") if line.startswith("args: ")).split()[2]
        r = kernel.check((REPO / policy).read_text(encoding="utf-8"))
        assert r.ok == want["ok"] and r.policy_digest == want["policy_digest"]
        assert [(f.code, f.action, f.message) for f in r.errors] == [
            (f["code"], f.get("action"), f["message"]) for f in want["errors"]]
        assert [(f.code, f.action, f.message) for f in r.warnings] == [
            (f["code"], f.get("action"), f["message"]) for f in want["warnings"]]


def test_results_are_frozen(kernel: Kernel) -> None:
    r = kernel.initial(SHOP)
    with pytest.raises(FrozenInstanceError):
        r.state = "x"  # type: ignore[misc]


def test_a_lone_surrogate_raises_input_error_naming_the_parameter(kernel: Kernel) -> None:
    with input_error("policy_text"):
        kernel.check('{"writ":"0.1","x":"\ud800"}')
    with input_error("digest"):
        kernel.initial(SHOP, "\udc00")
    with input_error("event.origin"):
        kernel.step(SHOP, "", {"type": "turn_end", "seq": 1, "time": 0, "state_version": 0, "origin": "\ud800"})
    with input_error("json_text"):
        kernel.digest('"\ud83d"')


def test_a_bad_policy_gives_input_error_at_policy_text(kernel: Kernel) -> None:
    with input_error("policy_text"):
        kernel.initial(fixture("policies/errors.json"))
    with input_error("policy_text"):
        kernel.initial("{")
    with input_error("policy_text"):
        kernel.check("{")


def test_each_kernel_input_error_names_its_argument(kernel: Kernel) -> None:
    with input_error("json_text"):
        kernel.digest("{")
    with input_error("json_text"):
        kernel.canonical("{")
    with input_error("traces_text"):
        kernel.replay("{")
    with input_error("digest"):
        kernel.initial(SHOP, "sha256:0")
    with input_error("state_text"):
        kernel.step(SHOP, "{", {"type": "turn_end", "seq": 1, "time": 0, "state_version": 0})
    with input_error("ledger_text"):
        kernel.tombstone("{", True)
    with input_error("policy_text"):
        kernel.check('{"writ":"0.1"}\u0000')
    state = kernel.initial(SHOP).state
    for bad in (-1, 1.5, True, "5", 2**53):
        with input_error("time"):
            kernel.inspect(SHOP, state, bad)  # type: ignore[arg-type]
    with input_error("state_text"):
        kernel.inspect(SHOP, "{", 0)


def test_a_non_string_argument_is_an_input_error(kernel: Kernel) -> None:
    with input_error("policy_text"):
        kernel.check(b"{}")  # type: ignore[arg-type]
    with input_error("json_text"):
        kernel.digest(None)  # type: ignore[arg-type]


def test_malformed_host_input_is_an_input_error_and_the_kernel_lives_on(kernel: Kernel) -> None:
    started = kernel.step(SHOP, kernel.initial(SHOP).state, SHOP_START)
    head = {"seq": 2, "time": 10, "state_version": 1}
    with input_error("event"):
        kernel.step(SHOP, started.state,
                    {**head, "type": "result", "call_id": "c1", "outcome": "succeeded", "actual_cost": "6.00"})
    with input_error("event"):
        kernel.step(SHOP, started.state, {**head, "type": "propose", "call_id": "x" * 513, "tool": "search",
                                          "call_digest": "d", "guards": {}, "escalators": {}})
    with input_error("state_text"):
        kernel.step(fixture("policies/simple.json"), started.state, {**head, "type": "turn_end"})
    nxt = kernel.step(SHOP, started.state, {**head, "type": "turn_start", "user_initiated": True})
    assert nxt.verdict["verdict"] == "accepted"
    assert nxt.state_version == 2


def test_step_serializes_events_with_canonicalize(kernel: Kernel) -> None:
    policy = '{"writ":"0.1"}'
    state = kernel.initial(policy).state
    with input_error("event.n"):
        kernel.step(policy, state, {"type": "session_start", "n": float("nan")})
    with input_error("event.audit[0]"):
        kernel.step(policy, state, {"type": "turn_end", "audit": [object()]})
    cyclic: dict[str, object] = {}
    cyclic["c"] = cyclic
    with pytest.raises(WritInputError):
        kernel.step(policy, state, cyclic)


def test_tombstone_sets_once(kernel: Kernel) -> None:
    first = kernel.tombstone("", True)
    assert first.ledger_version == 1 and first.changed is True
    assert json.loads(first.ledger) == {"tombstone": True, "version": 1}
    again = kernel.tombstone(first.ledger, True)
    assert again.changed is False and again.ledger_version == 1 and again.ledger == first.ledger
    cleared = kernel.tombstone(first.ledger, False)
    assert cleared.changed is True and cleared.ledger_version == 2


def test_inspect_shows_calls_and_meters(kernel: Kernel) -> None:
    policy = compact({"writ": "0.1", "meters": {"spend": {"currency": "USD", "cap": 5000}},
                      "actions": {"buy": {"meters": ["spend"]}}})
    digest = kernel.digest(policy)
    cost = {"amount": "1200", "currency": "USD"}
    events = [
        {"type": "session_start", "seq": 1, "time": 0, "state_version": 0, "session_id": "s1", "policy_digest": digest,
         "requester": "u1", "permissions": [], "approvers": {}, "ledger": {}},
        {"type": "turn_start", "seq": 2, "time": 10, "state_version": 1, "user_initiated": True},
        {"type": "step_start", "seq": 3, "time": 20, "state_version": 2},
        {"type": "propose", "seq": 4, "time": 30, "state_version": 3, "call_id": "c1", "tool": "buy",
         "call_digest": "d1", "cost": cost, "guards": {}, "escalators": {}},
        {"type": "dispatch", "seq": 5, "time": 40, "state_version": 4, "call_id": "c1", "attempt": 1,
         "call_digest": "d1", "cost": cost, "guards": {}, "idempotency_key": "k1"},
    ]
    state = kernel.initial(policy).state
    for e in events:
        r = kernel.step(policy, state, e)
        assert r.verdict["verdict"] == "accepted", r.verdict
        state = r.state
    view = kernel.inspect(policy, state, 50)
    assert view.session_id == "s1" and view.state_version == 5
    assert view.started is True and view.killed is False
    assert len(view.calls) == 1
    call = view.calls[0]
    assert (call.call_id, call.status, call.attempts, call.cost, call.request_id) == ("c1", "dispatched", 1, cost, None)
    assert [(m.meter, m.scope, m.used, m.cap, m.remaining) for m in view.meters] == [
        ("spend", "session", "1200", "5000", "3800")]
    assert kernel.inspect(policy, state, 50.0) == view  # type: ignore[arg-type]


def test_session_start_then_propose_needs_approval_at_state_version_3(kernel: Kernel) -> None:
    init = kernel.initial(SHOP, SHOP_DIGEST)
    assert init.state_version == 0
    a = kernel.step(SHOP, init.state, SHOP_START)
    assert a.verdict["verdict"] == "accepted" and a.state_version == 1
    turn = kernel.step(SHOP, a.state, {"type": "turn_start", "seq": 2, "time": 10, "state_version": 1,
                                       "user_initiated": True})
    b = kernel.step(SHOP, turn.state, {
        "type": "propose", "seq": 3, "time": 20, "state_version": 2, "call_id": "c1", "tool": "buy",
        "call_digest": "d1", "cost": {"amount": "1200", "currency": "USD"}, "guards": {"card_on_file": True},
        "escalators": {}})
    assert b.verdict["decision"] == "needs_approval" and b.state_version == 3


def test_the_oracle_fixture_session_gives_the_oracle_verdicts_and_final_state(kernel: Kernel) -> None:
    verdicts, _, state = session_runner(kernel)()
    want = [line for line in fixture("oracle-1.out").rstrip().split("\n") if not line.startswith('{"error"')]
    assert verdicts == want
    assert state + "\n" == fixture("states/after-1.json")


def test_amounts_of_2_31_and_up_give_the_native_oracle_verdicts_and_state(kernel: Kernel) -> None:
    policy = fixture("policies/big-amounts.json")
    state = kernel.initial(policy).state
    verdicts = []
    for line in fixture("oracle-big-events.jsonl").rstrip().split("\n"):
        r = kernel.step(policy, state, json.loads(line))
        state = r.state
        verdicts.append(compact(r.verdict))
    assert verdicts == fixture("oracle-big.out").rstrip().split("\n")
    assert state + "\n" == fixture("states/after-big.json")


def test_10000_steps_keep_the_heap_flat_and_results_unchanged() -> None:
    long = load_kernel()
    run = session_runner(long)
    per_loop = len(run()[0])
    warmup = -(-100 // per_loop)
    loops = -(-10000 // per_loop)
    tail: list[str] = []
    used_after_warmup = memory_after_warmup = 0
    for i in range(loops):
        _, results, _ = run()
        if i == warmup - 1:
            used_after_warmup = long._heap_used()
            memory_after_warmup = long._memory_bytes()
        if i >= loops - 2:
            tail.extend(results)
    fresh = session_runner(load_kernel())
    want = fresh()[1] + fresh()[1]
    assert tail[-10:] == want[-10:]
    assert long._memory_bytes() <= 2 * memory_after_warmup
    # Allocation accounting is exact and the steps are deterministic, so any difference is a leak.
    assert long._heap_used() == used_after_warmup


def test_load_kernel_accepts_bytes_and_paths(kernel: Kernel) -> None:
    data = WASM_PATH.read_bytes()
    expected = kernel.version()
    assert load_kernel(data).version() == expected
    assert load_kernel(bytearray(data)).version() == expected
    assert load_kernel(memoryview(data)).version() == expected
    assert load_kernel(WASM_PATH).version() == expected
    assert load_kernel(str(WASM_PATH)).version() == expected


def test_inputs_over_max_input_bytes_raise_input_error_before_calling_in(kernel: Kernel) -> None:
    with pytest.raises(WritInputError, match="over the limit"):
        kernel.canonical(compact({"a": "x" * MAX_INPUT_BYTES}))
    half = "x" * (MAX_INPUT_BYTES // 2)
    with pytest.raises(WritInputError, match="over the limit"):
        kernel.step(half, half, {"type": "turn_end", "seq": 1, "time": 0, "state_version": 0})
    # Multi-byte characters count as their UTF-8 bytes.
    with pytest.raises(WritInputError, match="over the limit"):
        kernel.canonical(compact({"a": "\u00e9" * (MAX_INPUT_BYTES // 2)}))
    assert kernel.version() == fixture("version.out").strip()


def assert_aborted(e: pytest.ExceptionInfo[WritKernelError],
                   cause: type[BaseException] | tuple[type[BaseException], ...] | None = None) -> None:
    assert str(e.value) == "kernel aborted; load a new kernel"
    assert e.value.__cause__ is not None
    if cause is not None:
        assert isinstance(e.value.__cause__, cause), repr(e.value.__cause__)


# Memory capped well below 2 GiB runs out cheaply; build/wasm/README.md ("Traps") lists which
# allocation fails first. Either trap kills the kernel the same way.
@pytest.mark.parametrize(("limit", "size"), [(64 << 20, 4 << 20), (32 << 20, 1 << 20)])
def test_a_trap_kills_that_kernel_and_every_later_call_says_aborted(kernel: Kernel, limit: int, size: int) -> None:
    small = _load(memory_limit=limit)
    assert small.version() == kernel.version()
    with pytest.raises(WritKernelError) as e:
        small.canonical(compact({"a": "x" * size}))
    assert_aborted(e, (wasmtime.Trap, wasmtime.ExitTrap))
    first = e.value.__cause__
    with pytest.raises(WritKernelError) as again:
        small.version()
    assert_aborted(again)
    assert again.value.__cause__ is first
    with pytest.raises(WritKernelError) as again:
        small.check(SHOP)
    assert_aborted(again)
    assert kernel.canonical('{"b":1,"a":2}') == '{"a":2,"b":1}'


def test_a_trap_from_a_bad_pointer_kills_the_kernel() -> None:
    k = load_kernel()
    real = k._ex
    # The result length is written through a pointer far outside memory, the smoke test's trap.
    k._ex = {**{name: real[name] for name in ("memory", "writ_call", "writ_free", "free")},
             "malloc": lambda store, n: real["malloc"](store, n) if n != 4 else 0x7FFFFFF0}
    with pytest.raises(WritKernelError) as e:
        k.version()
    assert_aborted(e, wasmtime.Trap)
    k._ex = real
    with pytest.raises(WritKernelError) as e:
        k.version()
    assert_aborted(e)


def test_the_package_license_is_the_repository_license() -> None:
    assert (REPO / "packages/writ-py/LICENSE").read_bytes() == (REPO / "LICENSE").read_bytes()


def test_a_trap_while_the_kernel_starts_raises_failed_to_start(monkeypatch: pytest.MonkeyPatch) -> None:
    with pytest.raises(WritKernelError, match="^kernel failed to start$") as e:
        _load(memory_limit=1 << 20)
    assert isinstance(e.value.__cause__, wasmtime.WasmtimeError)

    real = _wasm.instantiate

    def trapping_init(mod: wasmtime.Module, memory_limit: int | None = None) -> tuple[wasmtime.Store, Any]:
        store, ex = real(mod, memory_limit)

        def writ_init(_store: wasmtime.Store) -> int:
            raise wasmtime.Trap("unreachable")

        return store, {**{n: ex[n] for n in ("memory", "malloc", "free", "writ_call", "writ_free")},
                       "writ_init": writ_init}

    monkeypatch.setattr(_wasm, "instantiate", trapping_init)
    with pytest.raises(WritKernelError, match="^kernel failed to start$") as e:
        load_kernel()
    assert isinstance(e.value.__cause__, wasmtime.Trap)

    def trapping_constructors(mod: wasmtime.Module, memory_limit: int | None = None) -> tuple[wasmtime.Store, Any]:
        raise wasmtime.Trap("unreachable")

    monkeypatch.setattr(_wasm, "instantiate", trapping_constructors)
    with pytest.raises(WritKernelError, match="^kernel failed to start$"):
        load_kernel()
