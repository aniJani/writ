"""Smoke test for packages/writ-py/src/writ/wasm/writ.wasm, loaded through the package's own loader
(src/writ/_wasm.py) but called through the raw ABI, without the package's Kernel.

Run from the repository root (scripts/build-wasm.sh does this after build/wasm/smoke.mjs):
    uv sync --project packages/writ-py --frozen --no-install-project
    uv run --project packages/writ-py --no-sync python packages/writ-py/scripts/smoke.py

It mirrors build/wasm/smoke.mjs, and also checks the module's import set against the one
build/wasm/README.md documents. Exits nonzero if any check fails.
"""

import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

import wasmtime

REPO = Path(__file__).resolve().parents[3]
MODULE_PATH = REPO / "packages/writ-py/src/writ/wasm/writ.wasm"

# build-wasm.sh syncs only the dependencies (--no-install-project), so the package comes from the tree.
sys.path.insert(0, str(REPO / "packages/writ-py/src"))
from writ import _wasm  # noqa: E402

# The table "Imports" in build/wasm/README.md. A new import means a new host function for the binding.
EXPECTED_IMPORTS = {
    ("env", "emscripten_notify_memory_growth"),
    ("wasi_snapshot_preview1", "random_get"),
    ("wasi_snapshot_preview1", "proc_exit"),
    ("wasi_snapshot_preview1", "fd_close"),
    ("wasi_snapshot_preview1", "fd_read"),
    ("wasi_snapshot_preview1", "fd_write"),
    ("wasi_snapshot_preview1", "fd_seek"),
    ("wasi_snapshot_preview1", "fd_fdstat_get"),
    ("wasi_snapshot_preview1", "environ_sizes_get"),
    ("wasi_snapshot_preview1", "environ_get"),
    ("wasi_snapshot_preview1", "clock_time_get"),
}
EXPECTED_EXPORTS = {"memory", "_initialize", "writ_init", "writ_call", "writ_free", "writ_heap_used", "malloc", "free"}

failures = 0


def expect(ok, what, detail=""):
    global failures
    if ok:
        print(f"ok   {what}")
    else:
        failures += 1
        print(f"FAIL {what}" + (f"\n     {detail}" if detail else ""))


def fixture(p):
    return (REPO / "tests/cli" / p).read_text(encoding="utf-8")


def lines(text):
    return text.rstrip("\n").split("\n")


try:
    module = _wasm.module(MODULE_PATH)
except (OSError, wasmtime.WasmtimeError) as e:
    print(f"FAIL load {MODULE_PATH}: {e}")
    sys.exit(1)

imports = {(i.module, i.name) for i in module.imports}
expect(imports == EXPECTED_IMPORTS, "imports are the documented set",
       f"extra {sorted(imports - EXPECTED_IMPORTS)}, missing {sorted(EXPECTED_IMPORTS - imports)}")
exports = {e.name for e in module.exports}
expect(EXPECTED_EXPORTS <= exports, "exports include the ABI", f"missing {sorted(EXPECTED_EXPORTS - exports)}")

store, ex = _wasm.instantiate(module)
memory = ex["memory"]


# wasmtime returns an i32 as a signed int. The memory's maximum is 2 GiB, so no pointer is negative.
def malloc(n):
    return ex["malloc"](store, n)


def free(p):
    ex["free"](store, p)


def heap_used():
    return ex["writ_heap_used"](store)


def call(fn, *args, out_ptr=None):
    bufs = [a.encode("utf-8") if isinstance(a, str) else a for a in (list(args) + ["", "", ""])[:3]]
    ptrs = []
    for b in bufs:
        p = malloc(max(len(b), 1))
        memory.write(store, b, p)
        ptrs.append(p)
    out = malloc(4) if out_ptr is None else out_ptr
    r = ex["writ_call"](store, fn, ptrs[0], len(bufs[0]), ptrs[1], len(bufs[1]), ptrs[2], len(bufs[2]), out)
    for p in ptrs:
        free(p)
    if r == 0:
        free(out)
        raise RuntimeError(f"writ_call({fn}) returned NULL")
    n = int.from_bytes(memory.read(store, out, out + 4), "little")
    free(out)
    text = bytes(memory.read(store, r, r + n)).decode("utf-8")
    ex["writ_free"](store, r)
    return text


def compact(v):
    return json.dumps(v, separators=(",", ":"), ensure_ascii=False)


expect(ex["writ_init"](store) == 0, "writ_init() == 0")
expect(ex["writ_init"](store) == 0, "writ_init() is idempotent")

version = call(7)
expect(version == fixture("version.out").rstrip("\n"), "version matches writ --version", version)

shop = fixture("policies/formats-shop.json")
digest = json.loads(call(2, shop))["digest"]
expect(digest == fixture("formats-digest.out").rstrip("\n"), "digest of formats-shop.json matches writ digest", digest)

check = json.loads(call(1, shop))
expect(check["ok"] is True and check["policy_digest"] == digest, "check of formats-shop.json is ok", compact(check))

for name in ("ok", "errors", "warnings"):
    case = fixture(f"check-json-{name}.case")
    policy = next(line for line in case.split("\n") if line.startswith("args: ")).split()[2]
    got = call(1, (REPO / policy).read_text(encoding="utf-8"))
    expect(got == fixture(f"check-json-{name}.out").rstrip("\n"),
           f"check of {policy} matches check-json-{name}.out", got)

assistant = REPO / "schema/examples/assistant.json"
native = REPO / ".lake/build/bin/writ"
if native.exists():
    want = subprocess.run([str(native), "check", "--json", str(assistant)], capture_output=True, text=True).stdout
    got = call(1, assistant.read_text(encoding="utf-8"))
    expect(got == want.rstrip("\n"), "check of assistant.json matches writ check --json", got)
elif os.environ.get("WRIT_REQUIRE_NATIVE") == "1":
    expect(False, "check of assistant.json matches writ check --json", f"no {native} (run lake build writ)")
else:
    print(f"skip check of assistant.json against writ check --json: no {native}")

simple = fixture("policies/simple.json")
init = json.loads(call(4, simple, ""))
expect(isinstance(init.get("state"), str) and init.get("state_version") == 0, "initial gives a state", compact(init))

events = lines(fixture("oracle-events.jsonl"))
want = lines(fixture("oracle-1.out"))
state = init["state"]
states = [state]
got = []
for line in events:
    r = json.loads(call(5, simple, state, line))
    if "error" in r:
        got.append(compact({"error": r["error"]}))
        continue
    state = r["state"]
    states.append(state)
    got.append(compact(r["verdict"]))
expect(got == want, "oracle sequence matches oracle-1.out",
       "; ".join(f"line {i + 1}: got {g}, want {w}" for i, (g, w) in enumerate(zip(got, want)) if g != w))
expect(state + "\n" == fixture("states/after-1.json"), "final state matches states/after-1.json")

big_policy = fixture("policies/big-amounts.json")
big_state = json.loads(call(4, big_policy, ""))["state"]
big_want = lines(fixture("oracle-big.out"))
big_got = []
for line in lines(fixture("oracle-big-events.jsonl")):
    r = json.loads(call(5, big_policy, big_state, line))
    if "error" in r:
        big_got.append(compact({"error": r["error"]}))
        continue
    big_state = r["state"]
    big_got.append(compact(r["verdict"]))
expect(big_got == big_want, "big-amount sequence matches oracle-big.out",
       "; ".join(f"line {i + 1}: got {g}, want {w}" for i, (g, w) in enumerate(zip(big_got, big_want)) if g != w))
expect(big_state + "\n" == fixture("states/after-big.json"), "big-amount final state matches states/after-big.json")

big = '{"s":"\\u00e9\\ud83d\\ude00","n":9007199254740991,"m":-9007199254740991,"k":4294967296}'
big_canon = '{"k":4294967296,"m":-9007199254740991,"n":9007199254740991,"s":"é\U0001f600"}'
canon = json.loads(call(3, big))["canonical"]
expect(canon == big_canon, "canonical of large integers and non-ASCII text", canon)
sha = "sha256:" + hashlib.sha256(big_canon.encode("utf-8")).hexdigest()
expect(json.loads(call(2, big))["digest"] == sha, "digest is SHA-256 of the canonical text")

for f in sorted((REPO / "corpus/examples").glob("*.jsonl")):
    r = json.loads(call(6, f.read_text(encoding="utf-8")))
    traces = r.get("traces")
    expect(isinstance(traces, list) and len(traces) > 0 and all(t["ok"] for t in traces),
           f"replay of corpus/examples/{f.name}", compact(r)[:300])

tomb = json.loads(call(8, "", "1"))
expect(tomb.get("ledger") == '{"tombstone":true,"version":1}' and tomb.get("ledger_version") == 1
       and tomb.get("changed") is True, "tombstone sets the flag on an empty ledger", compact(tomb))
again = json.loads(call(8, tomb["ledger"], "1"))
expect(again.get("ledger") == tomb["ledger"] and again.get("ledger_version") == 1 and again.get("changed") is False,
       "tombstone on a tombstoned ledger changes nothing", compact(again))
expect(isinstance(json.loads(call(8, "", "yes")).get("error"), str), "a tombstone flag other than 1 or 0 gives {error}")

shop_state = json.loads(call(4, shop, ""))["state"]
for line in lines(fixture("formats-events-a.jsonl")):
    shop_state = json.loads(call(5, shop, shop_state, line))["state"]
view = json.loads(call(9, shop, shop_state, "1100"))
calls = view.get("calls", [])
meters = view.get("meters", [])
expect(view.get("session_id") == "s1" and len(calls) == 1 and calls[0].get("status") == "awaiting"
       and (calls[0].get("request_id") or {}).get("call") == "c1" and meters and meters[0].get("used") == "0"
       and meters[0].get("cap") == "5000", "inspect shows the awaiting call and the meter", compact(view))
bad_time = json.loads(call(9, shop, shop_state, "1.5"))
expect(bad_time.get("input") == "time", "inspect with a time that is not digits gives {error, input: time}",
       compact(bad_time))
foreign = json.loads(call(5, simple, shop_state, events[0]))
expect(foreign.get("input") == "state", "a state from another policy gives {error, input: state}", compact(foreign))

profile_text = (REPO / "corpus/profiles/mcp-tool-approval-v1.jsonl").read_text(encoding="utf-8")
vectors = [json.loads(line) for line in lines(profile_text)]
misses = [v["id"] for v in vectors if json.loads(call(10, compact(v["input"]))) != v["output"]]
expect(not misses, f"profile gives all {len(vectors)} vectors of corpus/profiles/mcp-tool-approval-v1.jsonl",
       ", ".join(misses))
bad_profile = json.loads(call(10, '{"profile":"other","status":"unknown"}'))
expect(bad_profile.get("input") == "profile", "an unknown profile gives {error, input: profile}", compact(bad_profile))

nul = json.loads(call(2, bytes([0x7B, 0x7D, 0x00])))
expect(isinstance(nul.get("error"), str), "input with a NUL byte gives {error}", compact(nul))
bad = json.loads(call(2, bytes([0x22, 0xFF, 0x22])))
expect(isinstance(bad.get("error"), str), "input with invalid UTF-8 gives {error}", compact(bad))
nul_b = json.loads(call(5, simple, bytes([0x7B, 0x00, 0x7D]), events[0]))
expect(nul_b.get("error") == "input b contains a NUL byte" and nul_b.get("input") == "state",
       "a NUL byte in the second input gives {error, input}", compact(nul_b))
expect(isinstance(json.loads(call(99)).get("error"), str), "unknown fn code gives {error}")

# A block larger than any free chunk is placed at the top of the malloc heap, so its address
# tracks the heap's high-water mark.
def heap_top():
    p = malloc(1 << 20)
    free(p)
    return p


pairs = [(states[3], events[4]), (states[4], events[5])]
first = [call(5, simple, s, e) for s, e in pairs]
steps = 10000
drift = 0
elapsed = 0.0
for i in range(steps):
    s, e = pairs[i % 2]
    t = time.perf_counter()
    r = call(5, simple, s, e)
    elapsed += time.perf_counter() - t
    if r != first[i % 2]:
        drift += 1
    if i == 99:
        mem_after_100 = memory.data_len(store)
        top_after_100 = heap_top()
        used_after_100 = heap_used()
mem_end = memory.data_len(store)
top_end = heap_top()
used_end = heap_used()
expect(drift == 0, f"{steps} alternating steps give unchanged results", f"{drift} differ")
expect(mem_end <= 2 * mem_after_100, f"memory bounded: {mem_after_100} bytes after 100 steps, {mem_end} after {steps}")
expect(top_end - top_after_100 <= 65536,
       f"malloc heap top moved {top_end - top_after_100} bytes from step 100 to step {steps}")
expect(used_end == used_after_100,
       f"bytes in use unchanged: {used_after_100} after 100 steps, {used_end} after {steps}")
print(f"time per step: {elapsed / steps * 1e6:.1f} us ({steps} steps in {elapsed * 1000:.0f} ms)")

# The heap needs about 60 bytes per input byte, so 1 MiB outgrows the initial memory.
before = memory.data_len(store)
wide = '{"a":"' + "x" * (1 << 20) + '"}'
wide_sha = "sha256:" + hashlib.sha256(wide.encode("utf-8")).hexdigest()
expect(json.loads(call(2, wide)).get("digest") == wide_sha and memory.data_len(store) > before,
       f"a 1 MiB input grows the memory from {before} bytes to {memory.data_len(store)}")

# Last, since it leaves the instance unusable: a store through an out-of-bounds pointer traps.
try:
    call(7, out_ptr=-16)
    expect(False, "an out-of-bounds result pointer traps", "no trap")
except wasmtime.Trap as e:
    expect(True, f"an out-of-bounds result pointer raises wasmtime.Trap ({e.trap_code})")

if failures:
    print(f"{failures} failed")
    sys.exit(1)
print("all passed")
