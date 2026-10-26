"""Refuses to build a wheel or an sdist without the kernel, which is a build product and git-ignored."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from hatchling.builders.hooks.plugin.interface import BuildHookInterface

WASM = "src/writ/wasm/writ.wasm"


class WasmCheckHook(BuildHookInterface):  # type: ignore[misc]
    PLUGIN_NAME = "custom"

    def initialize(self, version: str, build_data: dict[str, Any]) -> None:
        if not (Path(self.root) / WASM).is_file():
            raise RuntimeError(
                f"{WASM} is missing, so the package would have no kernel: "
                "run scripts/build-wasm.sh from the repository root first")
