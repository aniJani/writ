#!/usr/bin/env bash
# Checks that one release version is written the same way everywhere a release reads it:
# lakefile.toml (`version`), Writ/Core/Version.lean (`cliVersion`), packages/writ/package.json
# (`version`), packages/writ/package-lock.json (`version` and `packages[""].version`),
# packages/writ-py/pyproject.toml (`[project] version`) and packages/writ-py/uv.lock (the
# writ-kernel package's `version`), both in PEP 440 form, and that CHANGELOG.md has a
# `## <version>` heading, alone or followed by ` (`.
#
#   scripts/check-version.sh [--unreleased] [v]<version>
#
# The version defaults to cliVersion in Writ/Core/Version.lean; a leading `v`, as in a tag, is
# stripped. It must be X.Y.Z or X.Y.Z-preview.N, whose PEP 440 form is X.Y.Z or X.Y.ZaN.
# --unreleased accepts a missing CHANGELOG heading, for a dry run that releases nothing.
# --lakefile, --lean, --npm, --lock, --py, --uvlock and --changelog <path> read another file in
# place of each, for the tests in tests/cli/check-version-*.case. Paths are relative to the
# repository root.
# Prints one line per file; exit 0 when all agree, 1 listing every mismatch, 2 for a usage error.
set -euo pipefail
cd "$(dirname "$0")/.."

usage() {
  echo "usage: scripts/check-version.sh [--unreleased] [v]<version>" >&2
  exit 2
}

lakefile=lakefile.toml
lean=Writ/Core/Version.lean
npm=packages/writ/package.json
lock=packages/writ/package-lock.json
py=packages/writ-py/pyproject.toml
uvlock=packages/writ-py/uv.lock
changelog=CHANGELOG.md
unreleased=0
version=""
while [ $# -gt 0 ]; do
  case "$1" in
    --unreleased) unreleased=1 ;;
    --lakefile | --lean | --npm | --lock | --py | --uvlock | --changelog)
      [ $# -ge 2 ] || usage
      case "$1" in
        --lakefile) lakefile=$2 ;;
        --lean) lean=$2 ;;
        --npm) npm=$2 ;;
        --lock) lock=$2 ;;
        --py) py=$2 ;;
        --uvlock) uvlock=$2 ;;
        --changelog) changelog=$2 ;;
      esac
      shift
      ;;
    -*) usage ;;
    *)
      [ -z "$version" ] || usage
      version=$1
      ;;
  esac
  shift
done

lean_version() { sed -n 's/^def cliVersion : String := "\([^"]*\)"$/\1/p' "$1" | head -1; }

if [ -z "$version" ]; then
  version=$(lean_version "$lean" 2>/dev/null || true)
  [ -n "$version" ] || { echo "check-version: no cliVersion in $lean" >&2; exit 2; }
fi
version=${version#v}
if ! printf '%s\n' "$version" | grep -Eqx '(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-preview\.(0|[1-9][0-9]*))?'; then
  echo "check-version: $version is not X.Y.Z or X.Y.Z-preview.N" >&2
  exit 2
fi
case "$version" in
  *-preview.*) pep440=${version%-preview.*}a${version##*-preview.} ;;
  *) pep440=$version ;;
esac

mismatches=0
# Compares the version that command $2 reads from file $1 with $3; $4 names the field, if any.
check() {
  file=$1 read=$2 want=$3 label=$1${4:+ $4}
  if [ ! -r "$file" ]; then
    echo "FAIL $label: cannot read the file"
    mismatches=$((mismatches + 1))
    return
  fi
  got=$("$read" "$file")
  if [ "$got" = "$want" ]; then
    echo "ok   $label: $got"
  else
    echo "FAIL $label: ${got:-no version found}, expected $want"
    mismatches=$((mismatches + 1))
  fi
}
# The top-level `version` comes before the first table.
lakefile_version() { awk '/^\[/ { exit } /^version *= *"/ { sub(/^version *= *"/, ""); sub(/".*/, ""); print; exit }' "$1"; }
# npm writes package.json with two-space indentation, so the top-level key is the one indented once.
npm_version() { sed -n 's/^  "version": *"\([^"]*\)".*/\1/p' "$1" | head -1; }
# The root package's entry in a lockfile v2 or v3.
lock_root_version() {
  awk '/^    "": \{/ { inside = 1; next } inside && /^    }/ { exit }
    inside && /^      "version": *"/ { sub(/^ *"version": *"/, ""); sub(/".*/, ""); print; exit }' "$1"
}
py_version() {
  awk '/^\[/ { section = $0; next }
    section == "[project]" && /^version *= *"/ { sub(/^version *= *"/, ""); sub(/".*/, ""); print; exit }' "$1"
}
# uv writes one [[package]] table per package, with `name` on the line before `version`.
uvlock_version() {
  awk '/^\[\[package\]\]$/ { inside = 0; next } /^name = "writ-kernel"$/ { inside = 1; next }
    inside && /^version = "/ { sub(/^version = "/, ""); sub(/".*/, ""); print; exit }' "$1"
}

check "$lakefile" lakefile_version "$version"
check "$lean" lean_version "$version"
check "$npm" npm_version "$version"
check "$lock" npm_version "$version"
check "$lock" lock_root_version "$version" 'packages[""]'
check "$py" py_version "$pep440"
check "$uvlock" uvlock_version "$pep440" writ-kernel
if [ ! -r "$changelog" ]; then
  echo "FAIL $changelog: cannot read the file"
  mismatches=$((mismatches + 1))
elif awk -v h="## $version" '$0 == h || index($0, h " (") == 1 { found = 1 } END { exit !found }' "$changelog"; then
  echo "ok   $changelog: ## $version"
elif [ "$unreleased" = 1 ]; then
  echo "skip $changelog: no \"## $version\" heading (--unreleased)"
else
  echo "FAIL $changelog: no \"## $version\" heading"
  mismatches=$((mismatches + 1))
fi

case "$mismatches" in
  0) echo "version $version agrees (PEP 440: $pep440)" ;;
  1) echo "1 mismatch for version $version"; exit 1 ;;
  *) echo "$mismatches mismatches for version $version"; exit 1 ;;
esac
