# The WebAssembly build

`scripts/build-wasm.sh` compiles the kernel, through `Writ.Api`, to
`packages/writ/wasm/writ.mjs` and `packages/writ/wasm/writ.wasm` with Emscripten, for the
TypeScript package. A second link of the same objects gives
`packages/writ-py/src/writ/wasm/writ.wasm`, a standalone module for wasmtime and the Python
package (see "The standalone module" below). The build then runs `node build/wasm/smoke.mjs` and,
when `uv` is on the path, `packages/writ-py/scripts/smoke.py`. Only after a module's smoke test
passes does it write `writ.source` next to that module, the hash of the sources it built from (see
"The source stamp" below), so without `uv` the standalone module gets no stamp. All of these are
build products and are not committed.

```sh
scripts/build-wasm.sh
```

The module is single-threaded and uses no pthreads, GMP, mmap, mimalloc or libuv code.

## Prerequisites

- `emcc` 6.0.12 (Emscripten).
- The Lean toolchain named in `lean-toolchain`, with `lake` on the path.
- node, which runs `build/wasm/closure.mjs` and the smoke test.
- `uv`, optional, which runs the standalone module's smoke test with the `wasmtime` pinned in
  `packages/writ-py/uv.lock`. Without it that test is skipped and the standalone module is left
  unstamped. With it, the first run needs network access to PyPI, or a cached wasmtime wheel:
  offline with an empty cache, the build fails at `uv sync` rather than skipping the test, since a
  `uv` that is present but cannot sync is a broken setup, not a missing tool.
- git with sparse-checkout, to fetch the runtime sources.
- Network access to github.com, for the first build (the runtime and the libuv header are fetched once into `.wasm-build/`).
- A repository path without spaces.

## Pinned versions

| What | Version | Checked by |
|---|---|---|
| Emscripten | `emcc` 6.0.12 | first line of `emcc --version` |
| Lean | v4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | `lean-toolchain` and `lean --version` |
| Lean runtime sources | tag `v4.35.0` of `leanprover/lean4`, same commit | `git rev-parse HEAD` after the fetch |
| libuv header | tag `v1.48.0` of `libuv/libuv`, commit `e9f29cb984231524e3931aa0ae2c5dae1a32884e` | `git rev-parse HEAD` after the fetch |
| wasmtime (standalone smoke test only) | 49.0.0 from PyPI | `packages/writ-py/uv.lock`, used with `uv sync --frozen` |

The script stops when a version differs. `WRIT_WASM_ALLOW_VERSIONS=1` builds anyway, for a
deliberate upgrade; update the pins in the script once the smoke test passes. libuv v1.48.0 is
the version Lean's own CMake build pins.

Other settings: `WRIT_WASM_OPT` (default `-Os`) and `WRIT_WASM_JOBS` (default: the number of CPUs).

## Where the runtime sources come from

The toolchain ships the runtime only as the native `libleanrt.a`: its `src/lean/runtime`
holds an empty `uv/` directory and nothing else. So the script fetches the tag shallowly and
sparsely (`src/runtime`, `src/include`, `src/util`, the `src/*.h.in` templates and `LICENSE`,
about 4 MB) into `.wasm-build/lean4`, checks the commit, and checks that its `lean.h` is
byte-identical to the toolchain's `include/lean/lean.h`. For libuv only `include/` is fetched.

## How the build works

1. **Versions.** As above.
2. **Fetch** the runtime and the libuv header into `.wasm-build/`, then apply
   `build/wasm/lean-runtime.patch` (see below).
3. **Headers.** `config.h`, `version.h` and `githash.h` are written from the tag's templates:
   no `LEAN_MIMALLOC`, platform target `wasm32-unknown-emscripten`.
4. **Lean side.** `lake build WritWasm` builds `WritWasm/Exports.lean`, which puts one
   `@[export writ_lean_<name>]` on each `Writ.Api` function and on `version`.
   `build/wasm/closure.mjs` then computes the import closure of `WritWasm.Exports` by asking
   `lean --deps` for the imports of every module, starting from the root: 827 modules, of
   which 653 are `Init`, 140 `Std` and 34 from this repository. Lake's C facet
   (`lake build +<module>:c`) produces the C for our modules.
5. **Init and Std to C.** Every other module of the closure is compiled with
   `lean -R <toolchain>/src/lean -c <out>.c <toolchain>/src/lean/<module>.lean`, with
   `LEAN_PATH` at the toolchain's `lib/lean`, in parallel. The C is cached in
   `.wasm-build/c-<lean commit>/`, so this runs once per toolchain. As a cross-check during
   development, every one of the 28,518 functions these files export is also exported by the
   toolchain's own `libInit.a` and `libStd.a`.
6. **Literal checks.** The script fails if the generated C packs a scalar into a pointer that
   does not fit a wasm32 small Nat (31 bits), or has a `USize` literal above 32 bits.
7. **Compile** with `-Os -DNDEBUG -DLEAN_EMSCRIPTEN -ffp-contract=off`:
   - the runtime files listed in `RUNTIME_OBJS` of `src/runtime/CMakeLists.txt`, except
     `uv/*`, with `em++ -std=c++20 -DLEAN_EXPORTING`;
   - the Lean C with `emcc -include build/wasm/lean_wasm32.h`;
   - `build/wasm/shim.c` and `build/wasm/uv_stub.c`;
   - `build/wasm/standalone.c`, which only the standalone link uses.

   Objects are cached in `.wasm-build/obj/` and rebuilt when their source is newer or the
   flags, `build/wasm/lean_wasm32.h` or the patch change.
8. **Link** with `em++ -Os --no-entry -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node
   -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=4MB --post-js build/wasm/post.js`, exporting `_writ_init`,
   `_writ_call`, `_writ_free`, `_writ_heap_used`, `_malloc` and `_free`, plus the `HEAPU8`
   and `HEAPU32` views. `build/wasm/post.js` only touches the JavaScript glue (see "Traps and
   aborts" below); `writ.wasm` is the same with or without it.
9. **Standalone link** of the same objects plus `standalone.o` with `em++ -Os --no-entry
   -sSTANDALONE_WASM -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=4MB
   -Wl,--wrap=lean_io_get_random_bytes`, with the same exported functions, to
   `packages/writ-py/src/writ/wasm/writ.wasm`. It has no JavaScript glue.
10. **Sizes.** Prints the raw and gzipped size of both modules and fails when either is above
    3 MB raw.
11. **Smoke tests.** `build/wasm/smoke.mjs`, then, with `uv`, `lake build writ` and
    `packages/writ-py/scripts/smoke.py` with `WRIT_REQUIRE_NATIVE=1`, which compares a `check`
    result with the current native `writ check --json` and fails without the binary (run by
    hand without the variable, it skips that check when the binary is missing).
12. **Stamp.** Writes `writ.source` next to each module whose smoke test ran and passed, the hash
    `scripts/wasm-source-hash.sh` printed when the build started. Both are removed before linking,
    so a build that fails, or whose smoke tests fail, leaves none.

The flags follow Lean's own Emscripten build (`-DUSE_GMP=OFF -DMMAP=OFF`, `LEAN_EMSCRIPTEN`),
minus its `-pthread`, `-fwasm-exceptions` and `-flto`, and with `MULTI_THREAD` off.

## The source stamp

CI cannot build the WebAssembly, so a stale `writ.wasm` could be tested without anyone
noticing. `scripts/wasm-source-hash.sh` prints `sha256:<hex>` over the files the build reads
from this repository: the import closure of `WritWasm.lean` (its own Lean modules, not `Init`
or `Std`), `lean-toolchain`, `lakefile.toml` (its Lean options shape the generated C),
`scripts/build-wasm.sh` and the tracked files under `build/wasm/` other than this README and
`smoke.mjs`. Docs, proofs and tests are outside it, and so is `packages/writ-py/scripts/smoke.py`.
Each file adds its path and the SHA-256 of its contents, in path order. Both modules come from one
run of the script over the same sources, so `packages/writ-py/src/writ/wasm/writ.source` holds
the same hash as `packages/writ/wasm/writ.source`.

`npm test` in `packages/writ` and in `examples/langgraph` runs
`packages/writ/scripts/check-wasm.mjs` first, which compares that hash with `writ.source` and
refuses to run when the stamp is missing or differs. The hash does not cover the emcc and Lean
binaries themselves; the script's version checks pin those. Nor does it cover the environment:
`WRIT_WASM_OPT` and `WRIT_WASM_ALLOW_VERSIONS=1` change `writ.wasm` without changing the stamp.

## Diagnostic export

`writ_heap_used()` returns the bytes currently allocated from the malloc heap (`mallinfo().uordblks`). It is not part of the ABI. `HEAPU8.length` cannot show a leak, since the initial memory has megabytes of slack, so the smoke test and the package tests compare this value after 100 steps with its value after 10,000. Allocation accounting is exact and the steps are deterministic, so the two must be equal.

## Runtime configuration

| Feature | Setting | Effect |
|---|---|---|
| Threads | `LEAN_MULTI_THREAD` undefined, no `-pthread` | tasks run synchronously; no worker threads |
| Big numbers | `LEAN_USE_GMP` undefined | the runtime's own `mpz.cpp` and `mpn.cpp` |
| mmap | `LEAN_MMAP` undefined | no `.olean` mapping (not needed) |
| Allocator | `LEAN_MIMALLOC` undefined | Emscripten's `malloc` (dlmalloc) |
| libuv | `uv/*.cpp` not compiled, only `uv.h` | no libuv code is linked |
| C++ exceptions | disabled (Emscripten default) | a `throw` becomes a JS exception out of `writ_call`; in the standalone module, a trap |

## Exclusions and stubs

Excluded runtime files:

| File | Why |
|---|---|
| `uv/{net_addr,event_loop,timer,tcp,udp,dns,system,signal}.cpp` | libuv bindings for `Std.Internal.UV`, which is not in the closure |
| `mimalloc.cpp` | not in `RUNTIME_OBJS`; only used with `LEAN_MIMALLOC` |

Compiled in their `LEAN_EMSCRIPTEN` form, which is Lean's own code for this target:
`libuv.cpp` (no event loop, libuv version 0), `openssl.cpp` (OpenSSL version 0),
`stackinfo.cpp`, `platform.cpp`, `process.cpp`, `io.cpp`.

`io.cpp` and `process.cpp` also contain calls into libuv and process APIs. None of them is
reachable from `Writ.Api`: `wasm-ld` drops unreachable code before it reports undefined
symbols, and the link fails on any libuv symbol that is still reachable. So any new path
from the kernel into libuv breaks the build instead of shipping a stub. As a check,
`io.o` references nine libuv functions (`uv_fs_*`, `uv_os_tmpdir`, `uv_strerror`); linking
without `build/wasm/uv_stub.c` fails on `uv_strerror` alone.

The one stub is `build/wasm/uv_stub.c`, which defines `uv_strerror`. It is reachable only through
`io.cpp` turning an errno into an IO error message. `Writ.Api` does no IO; the only IO its
closure can reach is the runtime printing a panic message to stderr, and that formats an
error only if the write itself fails. The stub returns libc's `strerror` text for the same
errno (libuv error codes are negated errno values on Unix, and Emscripten follows that),
where libuv would return its own wording.

The link warns about a signature mismatch for `lean_io_create_tempfile` and
`lean_io_create_tempdir`: `Init.System.IO` declares them with a different signature from
the runtime's definition, and a call would trap. They implement `IO.FS.createTempFile` and
`IO.FS.createTempDir`, which `Writ.Api` never calls.

## Fixes for a 32-bit target

The C comes from the 64-bit toolchain. Lean's code generator aims to emit word-size
independent C, and the generated code checks out against that (static objects use
`sizeof(void*)`, `USize` constant folding only happens when 32-bit and 64-bit agree, static
tagged Nats are limited to 31 bits), with these exceptions, each found by the smoke test's
heap check or by an AddressSanitizer and LeakSanitizer build of the whole module:

1. **`LEAN_EMSCRIPTEN` for the Lean C.** `lean.h` splits the 8-byte scalar groups of static
   objects (`LEAN_SCALAR_PTR_LITERAL`) into two 32-bit words only when `LEAN_EMSCRIPTEN` is
   defined. Without it static objects lose 4 bytes and the high half of their scalars.
2. **Nat literals above 2^31 - 1** (`build/wasm/lean_wasm32.h`). The compiler types a Nat literal
   up to its host's `Lean.maxSmallNat` (2^63 - 1) as a tagged scalar and emits no reference
   counting for it. On wasm32 such a value is a heap object, so it leaked on every evaluation
   (one per parsed JSON number, from `maxInt` in `Writ.Json.Parse`), and an unbalanced
   decrement could free it while in use. The header redefines `lean_unsigned_to_nat` and
   `lean_cstr_to_nat`, which generated code calls only for literals, so that each call site
   builds its value once as a persistent object, on which reference counting is a no-op.
   Fourteen literal call sites in the closure fall in that range; the header treats every
   literal above 2^31 - 1 the same way, which is harmless for those the compiler did count.
3. **`String.toList` nil** (`build/wasm/lean-runtime.patch`). `string_to_list_core` in
   `src/runtime/object.cpp` ends the list with `lean_box_uint32(0)`. That is `lean_box(0)`,
   the empty list, on 64-bit, but a heap-allocated boxed `UInt32` on 32-bit, which leaked
   once per call (`Writ.Json.parse` calls `String.toList`). The patch uses `lean_box(0)`.

Known limit: the compiler also treats the results of `Array.size`, `ByteArray.size`,
`String.utf8ByteSize` and `String.length` as tagged scalars. On wasm32 that holds below
2^31 elements or bytes, far above any input the kernel accepts.

## The export layer and the shim

`WritWasm/Exports.lean` takes its `String` arguments owned: Lean 4.35 rejects borrow
annotations (`@&`) on an `@[export]` declaration. `build/wasm/shim.c` implements the ABI:

- `writ_init()` runs `lean_initialize_runtime_module`, the module initializer of
  `WritWasm.Exports` (which initializes the whole closure) and
  `lean_io_mark_end_initialization`, once; later calls return the first result.
  `writ_call` initializes on first use too.
- `writ_call(fn, a, an, b, bn, c, cn, out_len)` turns each byte range the function uses into a
  Lean string with the same check as `String.fromUTF8?`, rejects a NUL byte, calls the export
  and returns a `malloc`ed copy of the UTF-8 result, its length in `*out_len`. Invalid UTF-8,
  a NUL or an unknown `fn` gives an `{"error": ...}` envelope. `fn` 4 with an empty `b` passes
  no digest; a digest that is not the policy's is an error.
- `writ_free(p)` frees a result.

### What each `fn` returns

Every result is one compact JSON object, except `version`. Any failure (invalid UTF-8, a NUL
byte, an unknown `fn`, a parse or decode error, a policy that fails `check` where a checked
policy is needed) is instead `{"error": "<message>", "input": "<name>"}`, and that is the only
shape with an `error` key. `input` names the argument at fault: `policy`, `state`, `event`,
`ledger`, `traces`, `json`, `digest`, `time` or `profile`. It is absent only for an unknown `fn`, a failed
initialization and a malformed tombstone flag, which are faults of the binding, not of the
host's input.

| `fn` | Inputs | Result fields |
|---|---|---|
| 1 `check` | `a` policy text | `ok` (boolean), `errors` and `warnings` (arrays of `{code, action?, message}`), `policy_digest` (string). A policy that parses but fails its checks is `ok: false`, not `{error}`. |
| 2 `digest` | `a` JSON text | `digest`: `"sha256:"` plus hex of the canonical text |
| 3 `canonical` | `a` JSON text | `canonical`: the canonical text |
| 4 `initial` | `a` policy text, `b` policy digest or empty for the policy's own | `state` (the canonical `writ.state/1` text, as a string), `state_version` (number, 0), `ledger_version` (number) |
| 5 `step` | `a` policy text, `b` state text, `c` one event as JSON text | `verdict` (the verdict object of `docs/formats.md`), `state` (new state text), `ledger` (the principal ledger in the new state, canonical text), `changed` (boolean: the state text differs), `state_version`, `ledger_version` (numbers, after the step), `ledger_changed` (boolean: the ledger version moved). Every call hashes the policy document and compares the digest with the state's `policy_digest`; a state made under another policy is an error. |
| 6 `replay` | `a` traces, one `writ.trace/1` per line | `traces`: an array of `{id, ok, mismatches}`, each mismatch `{step, message}` |
| 7 `version` | none | plain text, not JSON: `writ <cli> (kernel <v>, trace <schema>, state <schema>)` |
| 8 `tombstone` | `a` ledger text or empty for the empty ledger, `b` `"1"` to set or `"0"` to clear | `ledger` (canonical text), `ledger_version` (number), `changed` (boolean). The version moves only when the flag changes. |
| 9 `inspect` | `a` policy text, `b` state text, `c` time in milliseconds as decimal digits | `session_id`, `state_version`, `ledger_version`, `started`, `ended`, `killed`, `tombstone`, `escalated`, `escalations`, `blocked_tools`, `calls` (in call id order, each `{call_id, tool, status, digest, cost, attempts, generation, epoch}` plus `request_id` while awaiting), `meters` (each meter of the policy as `{meter, scope, used, cap, remaining}`, amounts as decimal strings, `cap` and `remaining` null without a cap, usage in the window at `c`; `remaining` is never below `"0"`, and `used` may exceed `cap` after an overrun) |
| 10 `profile` | `a` JSON text: `{"profile": "mcp-tool-approval", "verdict": v}` or `{"profile": "mcp-tool-approval", "status": s}`, with a verdict or a call status as `docs/formats.md` writes them | `envelope` for a verdict and `disposition` for a status (MCP SEP-2848 profile, `docs/formats.md`), each absent when the profile gives none, so `{}` is a valid result. An unknown profile id is `{error, input: "profile"}`; any other bad input is `{error, input: "json"}`. |

`state` and `ledger` are strings holding JSON text, so a binding passes them back byte for
byte. A rejected event is still a `step` result with `"verdict": "rejected"`, not `{error}`.

### Traps and aborts

A trap (for example a stack overflow) or a C++ exception surfaces in JavaScript as an
exception from `_writ_call`; the instance is then in an unknown state and must be discarded.

When `malloc` fails, the Lean runtime prints `INTERNAL PANIC: out of memory` and calls
`exit(1)`, which Emscripten turns into a thrown `ExitStatus`: not an `Error`, and in Node its
default `quit` handler also sets `process.exitCode` to 1, which outlives a caught exception.
Emscripten 6 no longer reads a `quit` module option, so `build/wasm/post.js` restores it. Pass
`quit: (status, toThrow) => { throw toThrow }` to the factory to keep `process.exitCode`
alone. The memory a failed call grew stays allocated until the instance is dropped.
`@anijani/writ` does both: it throws `WritKernelError("kernel aborted; load a new kernel")`
for any exception out of the module and refuses every later call on that instance.

## The standalone module

`packages/writ-py/src/writ/wasm/writ.wasm` is the same objects linked a second time with
`-sSTANDALONE_WASM --no-entry`, for the Python package, which runs it in wasmtime. It has no
JavaScript glue and unminified import names: Emscripten's standalone mode implements in C what
the TypeScript module imports from its glue (`__syscall_openat`, `_tzset_js`, `_abort_js`,
`emscripten_get_now`, `emscripten_resize_heap` and the rest) and leaves only WASI calls and one
`env` function to the host.

### The decision: the standalone link, not the fallback

The plan ruled a standalone link first, and as a fallback, if wasmtime could not run it, keeping
the Emscripten module and having Python implement its sixteen minified imports from a map read out
of `writ.mjs`. The standalone link is used. wasmtime 49 loaded it at once; the only failure was
`writ_init` returning 1, because Lean's initializer for `IO.stdGenRef` calls `IO.getRandomBytes`,
which in the runtime opens `/dev/urandom`, and Emscripten's standalone `open()` admits only the
standard streams (in the TypeScript module the glue's in-memory file system serves the device).
`build/wasm/standalone.c` closes that gap: the standalone link passes
`-Wl,--wrap=lean_io_get_random_bytes`, so the generated C's calls reach
`__wrap_lean_io_get_random_bytes`, which asks the host through WASI `random_get`. The kernel never
reads those bytes. After that one change the module passes the whole smoke test, the same checks
as `smoke.mjs`, under Python 3.11, 3.13 and 3.15.

The fallback would have had Python reimplement Emscripten's JavaScript system layer, including a
file system that serves `/dev/urandom` through `__syscall_openat` and `fd_read`, against names that
the minifier may reassign on any link. The standalone link needs neither, and the TypeScript link
is untouched: same objects, same flags, byte-identical `writ.mjs` and `writ.wasm`.

### Loading it

Instantiate with wasmtime's WASI for `wasi_snapshot_preview1` (a default `WasiConfig`, plus
`inherit_stderr()` to see panic messages, and never `inherit_env()`) and the one `env` function
below. Then call the export `_initialize` once, before anything else: it runs the C and C++
static constructors. After that the ABI is the one above: `writ_init`, `writ_call`, `writ_free`,
`malloc` and `free`, with `writ_heap_used` as the diagnostic. The other exports
(`__indirect_function_table`, `setThrew`, `_emscripten_stack_restore`,
`emscripten_stack_get_current`) are Emscripten internals.

wasmtime passes and returns an `i32` as a signed Python int. The memory's maximum is 2 GiB (32,768
pages), so every pointer and length is non-negative and below 2^31. `*out_len` is 4 bytes,
little-endian.

### Imports

`packages/writ-py/scripts/smoke.py` fails when the module's imports differ from this table.
"When" is from a run with every import logged, over `writ_init`, `initial`, the oracle sequence,
every corpus replay, `inspect`, `version` and `check`: only `environ_*`, `random_get` and
`clock_time_get` were called. The rest are linked through libc's stdio and run only on a fatal
error or not at all.

| Module | Name | Signature | Behaviour | Traps |
|---|---|---|---|---|
| `wasi_snapshot_preview1` | `random_get` | `(buf: i32, buf_len: i32) -> i32` | Fills `buf_len` bytes at `buf` with random bytes. Called once, in `writ_init`, for the 8 bytes Lean seeds `IO.stdGenRef` with (through `standalone.c`); no kernel result depends on them. A nonzero errno makes `writ_init` return 1. | no |
| `wasi_snapshot_preview1` | `environ_sizes_get` | `(count: i32, buf_size: i32) -> i32` | The environment's size, read once by `_initialize`. Give it an empty environment: the Lean runtime reads variables such as `LEAN_ABORT_ON_PANIC`, which would turn a panic into an abort. | no |
| `wasi_snapshot_preview1` | `environ_get` | `(environ: i32, buf: i32) -> i32` | The environment itself, read once by `_initialize`, as above. | no |
| `wasi_snapshot_preview1` | `clock_time_get` | `(clock_id: i32, precision: i64, time: i32) -> i32` | `clock_gettime`, for the runtime's own timing: about 2,900 calls in `writ_init` and a few in later calls (38 over that whole run). No kernel result depends on the time. | no |
| `wasi_snapshot_preview1` | `fd_write` | `(fd: i32, iovs: i32, iovs_len: i32, nwritten: i32) -> i32` | Writes to stdout (1) or stderr (2). The kernel writes only to stderr: a Lean panic message (`PANIC at ...`, after which the call goes on with the default value, as in the TypeScript module) or an internal panic such as `INTERNAL PANIC: out of memory` just before `proc_exit`. | no |
| `wasi_snapshot_preview1` | `proc_exit` | `(code: i32) -> ()`, never returns | `exit()`. Only after an internal panic, such as running out of memory: the runtime prints it to stderr and calls `exit(1)`. wasmtime's WASI raises `wasmtime.ExitTrap`. | yes, always |
| `wasi_snapshot_preview1` | `fd_read` | `(fd: i32, iovs: i32, iovs_len: i32, nread: i32) -> i32` | Reads stdin. No kernel path reads it; WASI's default empty stdin is right. | no |
| `wasi_snapshot_preview1` | `fd_close` | `(fd: i32) -> i32` | libc `close`. Not called. | no |
| `wasi_snapshot_preview1` | `fd_seek` | `(fd: i32, offset: i64, whence: i32, newoffset: i32) -> i32` | libc stdio seeking on a standard stream. Not called. | no |
| `wasi_snapshot_preview1` | `fd_fdstat_get` | `(fd: i32, stat: i32) -> i32` | libc's terminal check when stdout or stderr first buffers output. Only before a panic message. | no |
| `env` | `emscripten_notify_memory_growth` | `(memory_index: i32) -> ()` | Called with 0 after each `memory.grow`. Do nothing; a host that caches a view of the memory refreshes it here (wasmtime's `Memory.read` and `write` need no refresh). The standalone heap grows by exactly what it needs, so the calls are many: 5,126 for one input of 8 MiB. | no |

### Traps

A trap leaves the instance in an unknown state, as in the TypeScript module, and the binding must
then refuse every later call with "kernel aborted; load a new kernel". wasmtime raises:

- `wasmtime.ExitTrap`, a `wasmtime.WasmtimeError`, from `proc_exit`: an internal panic, such as
  the Lean allocator running out of memory;
- `wasmtime.Trap`, which is not a `WasmtimeError`, from a trap in the module: `unreachable` from
  `abort()`, which is also where every C++ `throw` goes (standalone `__cxa_throw` calls `abort`,
  since C++ exceptions are disabled), an out-of-bounds memory access, or exhausting the stack.

Running out of memory can end either way. When a Lean allocation fails, the runtime prints
`INTERNAL PANIC: out of memory` and exits: `ExitTrap` with status 1. When a C++ allocation in the
runtime fails, it ends in `abort()`, since exceptions are disabled: `Trap` with
`TrapCode.UNREACHABLE`. Which allocation fails first depends on the input and
the limit, so a binding catches both and treats them alike.

The smoke test checks `Trap` with an out-of-bounds result pointer (`TrapCode.MEMORY_OUT_OF_BOUNDS`).
Both out-of-memory paths are cheap to provoke by capping the store's memory with
`store.set_limits(memory_size=...)` before instantiating, instead of letting the memory reach
2 GiB. With wasmtime 49, a `digest` of a JSON string of 4 MiB under a 64 MiB cap gave `Trap`
(`UNREACHABLE`); 8 MiB under 256 MiB, and 1 MiB under 32 MiB, gave `ExitTrap`, as did a `check`
of 1 MiB under 48 MiB. Without a cap, a 64 MiB input gave `ExitTrap` once the memory reached 2 GiB.

## Measured

Measured on 2026-10-19 on an arm64 Mac with 10 cores, Node 26, emcc 6.0.12; the clean build
and the peak memory at the input cap below are from 2026-10-18. The `-Os` output is
byte-for-byte the same from one build to the next: rebuilding it after an `-O2` build gave the
same SHA-256 for `writ.wasm` and `writ.mjs`. Sizes are as `scripts/build-wasm.sh` prints them
(gzip at level 9).

| Build | `writ.wasm` raw | gzipped | `writ.mjs` | Time per `step` |
|---|---|---|---|---|
| `-Os` (default) | 2,196,523 bytes (2.09 MiB) | 389,488 bytes | 60,343 bytes | 202 to 207 microseconds |
| `-O2` | 2,268,048 bytes (2.16 MiB) | 394,601 bytes | 60,959 bytes | 199 to 208 microseconds |

The kernel as of 2026-10-21 builds to 2,196,751 bytes (389,512 gzipped) with `-Os`; the comparison above is of the 2026-10-19 kernel.

The kernel as of 2026-10-25 builds to 2,215,471 bytes (392,943 gzipped) with `-Os`, and its
standalone module to 2,250,380 bytes (381,709 gzipped). Through wasmtime 49 from Python 3.13, the
standalone module takes 320 to 335 microseconds per `step` in `packages/writ-py/scripts/smoke.py`,
against 205 in `smoke.mjs`; the difference is the cost of calling in and copying bytes from
Python. A `digest` of an 8 MiB input peaks its memory at 491,126,784 bytes, close to the
TypeScript module's 500,170,752 for a `step` at the input cap.

`-O2` is 72 KB larger and no faster within run-to-run noise, so `-Os` is the default. Times per
`step` are the smoke test's, over eight runs of each build, interleaved.

- Clean build (empty `.wasm-build/`, Lake outputs present): 127 s wall clock. Of that, the
  fetches take 9 s, `lake build` and the closure 17 s, `lean -c` for the Init and Std
  modules 66 s, compiling 28 s and linking 5 s. Peak resident memory 783 MB.
- Rebuild with everything cached: 22 s, mostly `lean --deps` for the closure.
- Rebuild after a flag change (C cached, objects not): about 45 s.
- Smoke run: about 205 microseconds per `step` on the `simple.json` policy, which includes
  parsing, checking and hashing the policy and parsing the state on every call.
- Memory: 10,000 alternating steps leave the WASM memory at 21,299,200 bytes, its initial
  size, and the top of the malloc heap does not move between step 100 and step 10,000. Before
  the 32-bit fixes above the same run moved it by 10.4 MB, while `HEAPU8.length` still stayed
  flat.
- Peak memory at the input cap: one `step` whose inputs total just under the 8 MiB cap of
  `@anijani/writ` (`MAX_INPUT_BYTES`) grows the WASM memory from 21,299,200 bytes to
  500,170,752 bytes (500 MB, about 60 bytes per input byte, the memory's growth steps
  included), under a quarter of the 2 GiB ceiling. Measured with `loadKernelWithMemory` from
  `packages/writ/dist/src/kernel.js`: a fresh instance, one `step`, then `memoryBytes()`
  (`HEAPU8.length`, which never shrinks, so it is the peak). The inputs were a 1-action policy
  plus either an 8,387,610-byte state holding 12,155 call records with a `step_start` event,
  or the initial state with a `session_start` event whose `audit` holds an array of one
  repeated value (`0`, `{}`, `[]`, `""` or `4294967296`) filling the rest of the cap. Every shape peaked at the
  same 500,170,752 bytes. The Node process's resident memory rose from 69 MB to 590 MB over
  the state-shaped step.
