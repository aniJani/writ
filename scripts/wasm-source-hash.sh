#!/usr/bin/env bash
# Prints sha256:<hex>, the hash of the sources scripts/build-wasm.sh builds from: the import closure
# of WritWasm.lean within this repository (imports with no file here, such as Std, are skipped),
# lean-toolchain, lakefile.toml, scripts/build-wasm.sh and the tracked files under build/wasm/ other than
# README.md and smoke.mjs. Each file contributes "<path>\n<sha256 of its contents>\n", in path
# order. Exit 0 with the hash, 1 if a listed file is missing.
set -euo pipefail
cd "$(dirname "$0")/.."

if command -v sha256sum >/dev/null; then
  sha() { sha256sum | cut -d ' ' -f 1; }
else
  sha() { shasum -a 256 | cut -d ' ' -f 1; }
fi

seen=""
todo="WritWasm.lean"
while [ -n "$todo" ]; do
  file=${todo%%$'\n'*}
  if [ "$todo" = "$file" ]; then todo=""; else todo=${todo#*$'\n'}; fi
  case $'\n'"$seen"$'\n' in *$'\n'"$file"$'\n'*) continue ;; esac
  seen="$seen${seen:+$'\n'}$file"
  for mod in $(sed -n 's/^[[:space:]]*import[[:space:]]\{1,\}//p' "$file"); do
    dep="$(echo "$mod" | tr . /).lean"
    [ -f "$dep" ] && todo="$todo${todo:+$'\n'}$dep"
  done
done

files=$( {
  printf '%s\n' "$seen"
  echo lean-toolchain
  echo lakefile.toml
  echo scripts/build-wasm.sh
  git ls-files build/wasm | grep -vxE 'build/wasm/(README\.md|smoke\.mjs)'
} | LC_ALL=C sort -u)

missing=""
while IFS= read -r f; do
  [ -f "$f" ] || missing="$missing  $f"$'\n'
done <<< "$files"
if [ -n "$missing" ]; then
  echo "wasm-source-hash: missing files:" >&2
  printf '%s' "$missing" >&2
  exit 1
fi

while IFS= read -r f; do
  printf '%s\n%s\n' "$f" "$(sha < "$f")"
done <<< "$files" | sha | sed 's/^/sha256:/'
