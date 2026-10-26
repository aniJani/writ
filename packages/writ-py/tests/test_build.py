from __future__ import annotations

import shutil
import subprocess
import zipfile
from pathlib import Path

import pytest
from helpers import REPO

PACKAGE = REPO / "packages/writ-py"
uv = shutil.which("uv")


def package_copy(dest: Path, with_wasm: bool) -> Path:
    for name in ("pyproject.toml", "hatch_build.py", "README.md", "LICENSE"):
        shutil.copy(PACKAGE / name, dest / name)
    shutil.copytree(PACKAGE / "src", dest / "src", ignore=shutil.ignore_patterns("wasm", "__pycache__"))
    if with_wasm:
        (dest / "src/writ/wasm").mkdir()
        shutil.copy(PACKAGE / "src/writ/wasm/writ.wasm", dest / "src/writ/wasm/writ.wasm")
    return dest


def build(project: Path, kind: str) -> subprocess.CompletedProcess[str]:
    assert uv is not None
    return subprocess.run([uv, "build", kind, "--out-dir", str(project / "dist"), str(project)],
                          capture_output=True, text=True, timeout=300)


@pytest.mark.skipif(uv is None, reason="uv is not installed")
@pytest.mark.parametrize("kind", ["--wheel", "--sdist"])
def test_a_build_without_the_kernel_fails_and_says_how_to_build_it(kind: str, tmp_path: Path) -> None:
    r = build(package_copy(tmp_path, with_wasm=False), kind)
    assert r.returncode != 0
    assert "src/writ/wasm/writ.wasm is missing" in r.stderr and "scripts/build-wasm.sh" in r.stderr, r.stderr
    assert not list((tmp_path / "dist").glob("*.whl")) and not list((tmp_path / "dist").glob("*.tar.gz"))


@pytest.mark.skipif(uv is None, reason="uv is not installed")
def test_a_build_with_the_kernel_puts_it_in_the_wheel(tmp_path: Path) -> None:
    r = build(package_copy(tmp_path, with_wasm=True), "--wheel")
    assert r.returncode == 0, r.stderr
    (wheel,) = (tmp_path / "dist").glob("*.whl")
    names = zipfile.ZipFile(wheel).namelist()
    assert "writ/wasm/writ.wasm" in names and "writ/wasm/writ.source" not in names
