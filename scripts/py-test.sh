#!/usr/bin/env bash
# Runs the Python binding's tests (packages/writ-py) with the pinned dependencies in its uv.lock,
# after refusing a missing or stale packages/writ-py/src/writ/wasm/writ.wasm: ruff, mypy, then pytest.
# Arguments go to pytest.
set -euo pipefail
cd "$(dirname "$0")/.."

wasm=packages/writ-py/src/writ/wasm
if [ ! -f "$wasm/writ.wasm" ]; then
  echo "$wasm/writ.wasm is missing: run scripts/build-wasm.sh from the repository root first" >&2
  exit 1
fi

err=$(mktemp)
trap 'rm -f "$err"' EXIT
if ! tree=$(scripts/wasm-source-hash.sh 2>"$err"); then
  why=$(tr -s '[:space:]' ' ' < "$err" | sed 's/ $//')
  echo "could not hash the WASM sources: ${why:-wasm-source-hash.sh failed}; run scripts/build-wasm.sh from the repository root" >&2
  exit 1
fi
if ! [[ $tree =~ ^sha256:[0-9a-f]{64}$ ]]; then
  echo "could not hash the WASM sources: unexpected output \"$tree\"; run scripts/build-wasm.sh from the repository root" >&2
  exit 1
fi
stamp=""
[ -f "$wasm/writ.source" ] && stamp=$(tr -d '[:space:]' < "$wasm/writ.source")
if [ "$stamp" != "$tree" ]; then
  echo "$wasm is stale (built from ${stamp:-unknown sources}, tree is $tree): run scripts/build-wasm.sh from the repository root" >&2
  exit 1
fi

cd packages/writ-py
uv sync --quiet --frozen
uv run --frozen --no-sync ruff check --quiet .
uv run --frozen --no-sync mypy
uv run --frozen --no-sync pytest -q "$@"
