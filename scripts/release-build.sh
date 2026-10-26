#!/usr/bin/env bash
# Builds one release asset into <out> and checks it. scripts/release-dryrun.sh and
# .github/workflows/release.yml both build every asset through this script, so a dry run builds
# exactly what a release uploads. It never publishes.
#
#   scripts/release-build.sh <asset> <out>
#
#   binary  writ-<version>-<target>.tar.gz, holding writ-<version>-<target>/ with the writ binary
#           from `lake build writ`, LICENSE and README.md, for the host's target (linux-x64,
#           linux-arm64 or macos-arm64). The packed binary must run and print the version.
#           Like the corpus tarball, it is reproducible (scripts/tarball.py).
#   npm     anijani-writ-<version>.tgz, packed after `npm publish --dry-run` in packages/writ, whose
#           prepublishOnly runs the package tests and scripts/pack-check.sh. Needs the WebAssembly
#           kernel (scripts/build-wasm.sh).
#   python  writ_kernel-<pep440>-py3-none-any.whl and writ_kernel-<pep440>.tar.gz from `uv build`.
#           Both must hold the stamped writ/wasm/writ.wasm byte for byte, pass `twine check
#           --strict`, and the wheel must load its kernel in a fresh environment.
#   corpus  writ-corpus-<version>.tar.gz from scripts/corpus.sh --tar.
#   sums    SHA256SUMS over every other file in <out>, one "<sha256>  <name>" line each, by name.
#
# <version> is cliVersion in Writ/Core/Version.lean; scripts/check-version.sh checks the rest
# agree. Exit 0 with the asset written, 1 when a build or check fails, 2 for a usage error.
set -euo pipefail
cd "$(dirname "$0")/.."

TWINE=twine==7.0.0

usage() { echo "usage: scripts/release-build.sh binary|npm|python|corpus|sums <out>" >&2; exit 2; }
fail() { echo "release-build: $*" >&2; exit 1; }

[ $# = 2 ] || usage
asset=$1
mkdir -p "$2"
out=$(cd "$2" && pwd)

version=$(sed -n 's/^def cliVersion : String := "\([^"]*\)"$/\1/p' Writ/Core/Version.lean)
[ -n "$version" ] || fail "no cliVersion in Writ/Core/Version.lean"
case "$version" in
  *-preview.*) pep440=${version%-preview.*}a${version##*-preview.} ;;
  *) pep440=$version ;;
esac

if command -v sha256sum >/dev/null; then sha() { sha256sum "$@"; }
else sha() { shasum -a 256 "$@"; }
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

case "$asset" in
  binary)
    case "$(uname -s)-$(uname -m)" in
      Linux-x86_64) target="linux-x64" ;;
      Linux-aarch64 | Linux-arm64) target="linux-arm64" ;;
      Darwin-arm64) target="macos-arm64" ;;
      *) fail "no release target for $(uname -s) $(uname -m)" ;;
    esac
    lake build writ > "$tmp/build.log" 2>&1 || { tail -20 "$tmp/build.log"; fail "lake build writ failed"; }
    got=$(.lake/build/bin/writ --version | cut -d' ' -f2)
    [ "$got" = "$version" ] || fail "writ --version says $got, expected $version"
    name=writ-$version-$target
    mkdir "$tmp/$name"
    cp .lake/build/bin/writ LICENSE README.md "$tmp/$name/"
    python3 -I scripts/tarball.py "$out/$name.tar.gz" "$tmp" "$name"
    listed=$(tar -tzf "$out/$name.tar.gz" | sed 's|/$||' | LC_ALL=C sort | tr '\n' ' ')
    [ "$listed" = "$name $name/LICENSE $name/README.md $name/writ " ] ||
      fail "$name.tar.gz holds $listed"
    mkdir "$tmp/unpacked"
    tar -xzf "$out/$name.tar.gz" -C "$tmp/unpacked"
    got=$("$tmp/unpacked/$name/writ" --version | cut -d' ' -f2)
    [ "$got" = "$version" ] || fail "the packed writ says $got, expected $version"
    echo "wrote $name.tar.gz"
    ;;
  npm)
    tag=latest
    case "$version" in *-preview.*) tag=preview ;; esac
    (cd packages/writ && npm publish --dry-run --tag "$tag") || fail "npm publish --dry-run failed"
    name=anijani-writ-$version.tgz
    rm -f "$out/$name"
    (cd packages/writ && npm pack --pack-destination "$out" --silent > /dev/null) || fail "npm pack failed"
    [ -f "$out/$name" ] || fail "npm pack did not write $name"
    echo "wrote $name"
    ;;
  python)
    wasm=packages/writ-py/src/writ/wasm/writ.wasm
    [ -f "$wasm" ] || fail "$wasm is missing: run scripts/build-wasm.sh first"
    uv build --quiet packages/writ-py --out-dir "$tmp/dist" || fail "uv build failed"
    wheel=writ_kernel-$pep440-py3-none-any.whl
    sdist=writ_kernel-$pep440.tar.gz
    built=$(cd "$tmp/dist" && find . -type f ! -name ".*" | sed "s|^\./||" | LC_ALL=C sort | tr '\n' ' ')
    [ "$built" = "$wheel $sdist " ] || fail "uv build wrote $built, expected $wheel and $sdist"
    python3 -I - "$tmp/dist/$wheel" "$tmp/dist/$sdist" "$wasm" "writ_kernel-$pep440" <<'EOF' || fail "the Python packages do not hold the stamped kernel"
import hashlib, sys, tarfile, zipfile
wheel, sdist, wasm, root = sys.argv[1:]
want = hashlib.sha256(open(wasm, "rb").read()).hexdigest()
with zipfile.ZipFile(wheel) as z:
    names = z.namelist()
    if "writ/wasm/writ.wasm" not in names:
        sys.exit(f"{wheel} lists no writ/wasm/writ.wasm")
    if hashlib.sha256(z.read("writ/wasm/writ.wasm")).hexdigest() != want:
        sys.exit(f"{wheel}: writ/wasm/writ.wasm differs from {wasm}")
    if any(n.endswith("writ.source") for n in names):
        sys.exit(f"{wheel} holds writ.source")
with tarfile.open(sdist) as t:
    member = t.extractfile(f"{root}/src/writ/wasm/writ.wasm")
    if member is None or hashlib.sha256(member.read()).hexdigest() != want:
        sys.exit(f"{sdist}: src/writ/wasm/writ.wasm differs from {wasm}")
print(f"ok   both packages hold writ/wasm/writ.wasm, sha256 {want}")
EOF
    uvx --quiet --from "$TWINE" twine check --strict "$tmp/dist/$wheel" "$tmp/dist/$sdist" || fail "twine check failed"
    # Run from an empty directory, so `import writ` finds the installed wheel and not the sources.
    mkdir "$tmp/run"
    got=$(cd "$tmp/run" && uv run --quiet --isolated --no-project --with "$tmp/dist/$wheel" \
      python -I -c 'import writ; print(writ.load_kernel().version())') || fail "the wheel does not load its kernel"
    echo "ok   the wheel loads its kernel in a fresh environment: $got"
    cp "$tmp/dist/$wheel" "$tmp/dist/$sdist" "$out/"
    echo "wrote $wheel and $sdist"
    ;;
  corpus)
    scripts/corpus.sh --tar
    name=writ-corpus-$version.tar.gz
    [ -f "build/$name" ] || fail "scripts/corpus.sh --tar did not write build/$name"
    cp "build/$name" "$out/"
    echo "wrote $name"
    ;;
  sums)
    cd "$out"
    files=$(find . -maxdepth 1 -type f ! -name SHA256SUMS ! -name '.*' | sed 's|^\./||' | LC_ALL=C sort)
    [ -n "$files" ] || fail "$out holds no assets"
    # shellcheck disable=SC2086
    (IFS=$'\n'; sha $files) > SHA256SUMS
    sha -c --quiet SHA256SUMS || fail "SHA256SUMS does not verify"
    echo "wrote SHA256SUMS ($(wc -l < SHA256SUMS | tr -d ' ') assets)"
    ;;
  *) usage ;;
esac
