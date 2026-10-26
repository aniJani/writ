"""Loading the standalone WebAssembly kernel (build/wasm/README.md, "The standalone module") in wasmtime."""

from __future__ import annotations

import functools
import os
from pathlib import Path
from typing import Any

import wasmtime

WASM_PATH = Path(__file__).resolve().parent / "wasm" / "writ.wasm"

WasmSource = bytes | bytearray | memoryview | str | os.PathLike[str]


@functools.lru_cache(maxsize=1)
def engine() -> wasmtime.Engine:
    return wasmtime.Engine()


@functools.lru_cache(maxsize=1)
def _default_module() -> wasmtime.Module:
    return wasmtime.Module.from_file(engine(), str(WASM_PATH))


def module(wasm: WasmSource | None = None) -> wasmtime.Module:
    """Compiles the module; the bundled one is compiled once per process and shared."""
    if wasm is None:
        if not WASM_PATH.exists():
            raise FileNotFoundError(
                f"{WASM_PATH} is missing: in a source checkout, run scripts/build-wasm.sh from the repository root")
        return _default_module()
    if isinstance(wasm, (bytes, bytearray, memoryview)):
        return wasmtime.Module(engine(), bytes(wasm))
    return wasmtime.Module.from_file(engine(), os.fspath(wasm))


def instantiate(mod: wasmtime.Module, memory_limit: int | None = None) -> tuple[wasmtime.Store, Any]:
    """Instantiates `mod` (compiled by `module`) and runs its static constructors.

    Returns the store and the instance's exports.

    `memory_limit` caps the linear memory in bytes, below the module's own 2 GiB.
    """
    linker = wasmtime.Linker(engine())
    linker.define_wasi()
    linker.define_func("env", "emscripten_notify_memory_growth",
                       wasmtime.FuncType([wasmtime.ValType.i32()], []), lambda _memory_index: None)
    store = wasmtime.Store(engine())
    if memory_limit is not None:
        store.set_limits(memory_size=memory_limit)
    wasi = wasmtime.WasiConfig()
    # Never inherit the environment: LEAN_ABORT_ON_PANIC and the like would change how the runtime fails.
    wasi.inherit_stderr()
    store.set_wasi(wasi)
    exports: Any = linker.instantiate(store, mod).exports(store)
    exports["_initialize"](store)
    return store, exports
