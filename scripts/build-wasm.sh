#!/bin/sh
# Builds packages/writ/wasm/writ.{mjs,wasm} from the kernel with Emscripten, and a second, standalone
# link of the same objects for wasmtime, packages/writ-py/src/writ/wasm/writ.wasm. Then runs
# build/wasm/smoke.mjs and, when uv is on the path, packages/writ-py/scripts/smoke.py.
# See build/wasm/README.md for what each step does and why.
#
# Environment:
#   WRIT_WASM_ALLOW_VERSIONS=1  build with an emcc or Lean other than the pinned ones
#   WRIT_WASM_OPT=-Os           optimization level for compile and link (default -Os)
#   WRIT_WASM_JOBS=N            parallel jobs (default: number of CPUs)
set -eu
cd "$(dirname "$0")/.."
REPO=$(pwd)

EMCC_VERSION=6.0.12
LEAN_VERSION=4.35.0
LEAN_COMMIT=eb6cafb7290e8bd5f2937522d8d804f58f02bafc
LIBUV_TAG=v1.48.0
LIBUV_COMMIT=e9f29cb984231524e3931aa0ae2c5dae1a32884e
OPT=${WRIT_WASM_OPT:--Os}
JOBS=${WRIT_WASM_JOBS:-$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)}

B=$REPO/.wasm-build
OUT=$REPO/packages/writ/wasm
OUT_PY=$REPO/packages/writ-py/src/writ/wasm
START=$(date +%s)

fail() { echo "build-wasm: $*" >&2; exit 1; }
step() { echo "== $* ($(($(date +%s) - START))s)"; }

# Hashed before building, so an edit made while the build runs leaves the stamp stale.
SOURCE=$(scripts/wasm-source-hash.sh) || fail "could not hash the sources"

step "checking tools"
command -v emcc >/dev/null || fail "emcc not found on PATH"
command -v node >/dev/null || fail "node not found on PATH"
got_emcc=$(emcc --version | head -1)
case "$got_emcc" in
  *" $EMCC_VERSION"*) ;;
  *) [ "${WRIT_WASM_ALLOW_VERSIONS:-}" = 1 ] || fail "expected emcc $EMCC_VERSION, got: $got_emcc (set WRIT_WASM_ALLOW_VERSIONS=1 to override)" ;;
esac
[ "$(cat lean-toolchain)" = "leanprover/lean4:v$LEAN_VERSION" ] ||
  [ "${WRIT_WASM_ALLOW_VERSIONS:-}" = 1 ] || fail "lean-toolchain is not leanprover/lean4:v$LEAN_VERSION"
LEAN=$(elan which lean 2>/dev/null || command -v lean)
TC=$(cd "$(dirname "$LEAN")/.." && pwd)
case "$("$LEAN" --version)" in
  *"version $LEAN_VERSION,"*"commit $LEAN_COMMIT"*) ;;
  *) [ "${WRIT_WASM_ALLOW_VERSIONS:-}" = 1 ] || fail "expected Lean $LEAN_VERSION ($LEAN_COMMIT), got: $("$LEAN" --version)" ;;
esac

# Fetches the sparse paths $5... of repository $1 at tag $2 into $3 and checks that HEAD is commit $4.
fetch() {
  url=$1 tag=$2 dir=$3 commit=$4
  shift 4
  if [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" != "$commit" ]; then
    rm -rf "$dir"
    mkdir -p "$dir"
    git -C "$dir" init -q
    git -C "$dir" remote add origin "$url"
    git -C "$dir" sparse-checkout set --no-cone "$@"
    git -C "$dir" fetch -q --depth 1 --filter=blob:none origin "refs/tags/$tag"
    git -C "$dir" -c advice.detachedHead=false checkout -q FETCH_HEAD
  fi
  got=$(git -C "$dir" rev-parse HEAD)
  [ "$got" = "$commit" ] || fail "$url $tag is $got, expected $commit"
}

step "fetching the Lean runtime sources (v$LEAN_VERSION)"
fetch https://github.com/leanprover/lean4.git "v$LEAN_VERSION" "$B/lean4" "$LEAN_COMMIT" \
  /src/runtime/ /src/include/ /src/util/ '/src/*.h.in' /LICENSE
cmp -s "$B/lean4/src/include/lean/lean.h" "$TC/include/lean/lean.h" ||
  fail "lean.h of v$LEAN_VERSION differs from the toolchain's"
# Fixes for 32-bit targets; see build/wasm/README.md.
if ! git -C "$B/lean4" apply --reverse --check "$REPO/build/wasm/lean-runtime.patch" 2>/dev/null; then
  git -C "$B/lean4" apply "$REPO/build/wasm/lean-runtime.patch" || fail "build/wasm/lean-runtime.patch does not apply"
fi
# io.cpp includes uv.h unconditionally; only the header is used, no libuv code is linked.
step "fetching the libuv header ($LIBUV_TAG)"
fetch https://github.com/libuv/libuv.git "$LIBUV_TAG" "$B/libuv" "$LIBUV_COMMIT" /include/ /LICENSE

step "writing the configuration headers"
GEN=$B/gen
mkdir -p "$GEN/include/lean"
# No LEAN_MIMALLOC: the runtime uses the Emscripten malloc.
sed -e 's/@LEAN_MIMALLOC@//' -e 's/@LEAN_IS_STAGE0@/#define LEAN_IS_STAGE0 0/' \
  "$B/lean4/src/config.h.in" > "$GEN/include/lean/config.h"
major=${LEAN_VERSION%%.*} rest=${LEAN_VERSION#*.}
minor=${rest%%.*} patch=${rest#*.}
sed -e "s/@LEAN_VERSION_MAJOR@/$major/" -e "s/@LEAN_VERSION_MINOR@/$minor/" \
  -e "s/@LEAN_VERSION_PATCH@/$patch/" -e 's/@LEAN_VERSION_IS_RELEASE@/1/' \
  -e 's/@LEAN_SPECIAL_VERSION_DESC@//' -e "s/@LEAN_VERSION_STRING@/$LEAN_VERSION/" \
  -e 's/@LEAN_PLATFORM_TARGET@/wasm32-unknown-emscripten/' \
  -e "s|@LEAN_MANUAL_ROOT@|https://lean-lang.org/doc/reference/$LEAN_VERSION/|" \
  "$B/lean4/src/version.h.in" > "$GEN/include/lean/version.h"
sed -e "s/@GIT_SHA1@/$LEAN_COMMIT/" "$B/lean4/src/githash.h.in" > "$GEN/githash.h"

step "building the Lean side with Lake"
lake build WritWasm
CLOSURE=$B/closure.txt
node build/wasm/closure.mjs "$LEAN" "$TC/lib/lean" "$TC/src/lean" "$REPO" WritWasm.Exports > "$CLOSURE"
OURS=$(grep -E '^(Writ|WritWasm)(\.|$)' "$CLOSURE" || true)
# shellcheck disable=SC2046
lake build $(for m in $OURS; do printf '+%s:c ' "$m"; done)
echo "closure: $(wc -l < "$CLOSURE" | tr -d ' ') modules ($(echo "$OURS" | wc -l | tr -d ' ') from this repository)"

step "generating C for the Init and Std modules"
LC=$B/c-$("$LEAN" --githash)
mkdir -p "$LC"
export LEAN LC TCLIB="$TC/lib/lean" TCSRC="$TC/src/lean"
grep -vE '^(Writ|WritWasm)(\.|$)' "$CLOSURE" | while read -r m; do
  [ -f "$LC/$m.c" ] || echo "$m"
done | xargs -P "$JOBS" -n 1 sh -c '
  m=$1 rel=$(echo "$1" | tr . /)
  if LEAN_PATH="$TCLIB" "$LEAN" -R "$TCSRC" -c "$LC/$m.c.tmp" "$TCSRC/$rel.lean" > "$LC/$m.log" 2>&1; then
    mv "$LC/$m.c.tmp" "$LC/$m.c"
  else
    echo "lean -c failed for $m:" >&2; cat "$LC/$m.log" >&2; exit 255
  fi' sh || fail "C generation failed"

CSRCS=$B/csrcs.txt
while read -r m; do
  case "$m" in
    Writ | Writ.* | WritWasm | WritWasm.*) echo "$REPO/.lake/build/ir/$(echo "$m" | tr . /).c" ;;
    *) echo "$LC/$m.c" ;;
  esac
done < "$CLOSURE" > "$CSRCS"

# The C comes from the 64-bit compiler. A scalar it packs into a pointer must still fit a
# wasm32 small Nat (31 bits) and a USize literal 32 bits. Nat literals are handled by
# build/wasm/lean_wasm32.h instead.
step "checking the generated C for 64-bit-only literals"
# Prints the largest number matched by the extended regex $1 in the generated C, or nothing.
largest() {
  xargs cat < "$CSRCS" | grep -ohE "$1" | sed -E 's/[^0-9]*([0-9]+).*/\1/' | sort -g | tail -1
}
# Doubles are exact below 2^53, far above both limits.
le() { awk -v a="$1" -v b="$2" 'BEGIN { exit !(a + 0 <= b + 0) }'; }
boxed=$(largest 'lean_box\([0-9]+[uUlL]*\)|\(size_t\)\([0-9]+\) << 1')
[ -z "$boxed" ] || le "$boxed" 2147483647 || fail "boxed literal $boxed does not fit a wasm32 small Nat"
usize=$(largest '\(\(size_t\)[0-9]+ULL\)')
[ -z "$usize" ] || le "$usize" 4294967295 || fail "USize literal $usize does not fit wasm32"

RT=$B/lean4/src/runtime
RTSRCS=$(sed -n '/^set($/,/^)$/p' "$RT/CMakeLists.txt" | sed -n '/RUNTIME_OBJS/,/^)$/p' |
  grep -E '^ *[a-z0-9_/]+\.cpp$' | tr -d ' ' | grep -v '^uv/')
[ -n "$RTSRCS" ] || fail "could not read RUNTIME_OBJS from $RT/CMakeLists.txt"

# LEAN_EMSCRIPTEN also matters for the Lean C: lean.h then splits 64-bit scalar literals of
# static objects into two 32-bit words.
COMMON="$OPT -DNDEBUG -DLEAN_EMSCRIPTEN -ffp-contract=off -I$GEN/include -I$B/lean4/src/include"
CXXFLAGS="$COMMON -std=c++20 -DLEAN_EXPORTING -D__CLANG__ -I$GEN -I$B/lean4/src -I$B/libuv/include -Wno-everything"
CFLAGS="$COMMON -Wno-everything"
LEANCFLAGS="$CFLAGS -include $REPO/build/wasm/lean_wasm32.h"
OBJ=$B/obj
STAMP="$got_emcc $CXXFLAGS | $LEANCFLAGS | $(cat build/wasm/lean_wasm32.h build/wasm/lean-runtime.patch | cksum)"
if [ "$(cat "$OBJ/flags" 2>/dev/null || true)" != "$STAMP" ]; then
  rm -rf "$OBJ"
  mkdir -p "$OBJ/rt" "$OBJ/lean"
  echo "$STAMP" > "$OBJ/flags"
fi

step "compiling the runtime ($(echo "$RTSRCS" | wc -l | tr -d ' ') files) and $(wc -l < "$CSRCS" | tr -d ' ') Lean modules with $OPT"
OBJS=$B/objs.txt
: > "$OBJS"
TODO=$B/todo.txt
: > "$TODO"
for f in $RTSRCS; do
  o=$OBJ/rt/$(echo "$f" | tr / _ | sed 's/\.cpp$/.o/')
  echo "$o" >> "$OBJS"
  [ "$o" -nt "$RT/$f" ] || echo "em++ $RT/$f $o" >> "$TODO"
done
while read -r c; do
  rel=${c#"$LC"/}
  rel=${rel#"$REPO"/.lake/build/ir/}
  o=$OBJ/lean/$(echo "$rel" | tr / . | sed 's/\.c$/.o/')
  echo "$o" >> "$OBJS"
  [ "$o" -nt "$c" ] || echo "leancc $c $o" >> "$TODO"
done < "$CSRCS"
for f in shim uv_stub; do
  echo "emcc $REPO/build/wasm/$f.c $OBJ/$f.o" >> "$TODO"
  echo "$OBJ/$f.o" >> "$OBJS"
done
echo "emcc $REPO/build/wasm/standalone.c $OBJ/standalone.o" >> "$TODO"
export CXXFLAGS CFLAGS LEANCFLAGS
xargs -P "$JOBS" -L 1 sh -c '
  case $1 in
    em++) cc=em++ flags=$CXXFLAGS ;;
    leancc) cc=emcc flags=$LEANCFLAGS ;;
    *) cc=emcc flags=$CFLAGS ;;
  esac
  # shellcheck disable=SC2086
  "$cc" $flags -c "$2" -o "$3.tmp" && mv "$3.tmp" "$3" || { echo "compile failed: $2" >&2; exit 255; }
' sh < "$TODO" || fail "compilation failed"

step "linking"
mkdir -p "$OUT" "$OUT_PY"
# Removed first, so a build that fails after replacing writ.wasm leaves no stamp.
rm -f "$OUT/writ.source" "$OUT_PY/writ.source"
# shellcheck disable=SC2046
em++ $OPT $(cat "$OBJS") -o "$OUT/writ.mjs" \
  --no-entry \
  -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
  -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=4MB \
  --post-js "$REPO/build/wasm/post.js" \
  -sEXPORTED_FUNCTIONS=_writ_init,_writ_call,_writ_free,_writ_heap_used,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=HEAPU8,HEAPU32

step "linking the standalone module"
# shellcheck disable=SC2046
em++ $OPT $(cat "$OBJS") "$OBJ/standalone.o" -o "$OUT_PY/writ.wasm" \
  --no-entry -sSTANDALONE_WASM \
  -sALLOW_MEMORY_GROWTH -sSTACK_SIZE=4MB \
  -Wl,--wrap=lean_io_get_random_bytes \
  -sEXPORTED_FUNCTIONS=_writ_init,_writ_call,_writ_free,_writ_heap_used,_malloc,_free

step "checking sizes"
sizes() {
  raw=$(wc -c < "$1" | tr -d ' ')
  gz=$(gzip -9 -c "$1" | wc -c | tr -d ' ')
  echo "${1#"$REPO"/}: $raw bytes raw, $gz bytes gzipped"
  [ "$raw" -le 3145728 ] || fail "${1#"$REPO"/} is $raw bytes, over the 3 MB budget"
}
sizes "$OUT/writ.wasm"
echo "packages/writ/wasm/writ.mjs: $(wc -c < "$OUT/writ.mjs" | tr -d ' ') bytes"
sizes "$OUT_PY/writ.wasm"

step "smoke tests"
node build/wasm/smoke.mjs || fail "build/wasm/smoke.mjs failed"
py_smoke=0
if command -v uv >/dev/null; then
  # smoke.py compares check with the native `writ check --json`, so the binary must be current.
  lake build writ || fail "lake build writ failed"
  uv sync --quiet --project packages/writ-py --frozen --no-install-project ||
    fail "uv sync failed (it needs network access or a cached wasmtime wheel)"
  WRIT_REQUIRE_NATIVE=1 uv run --project packages/writ-py --no-sync python packages/writ-py/scripts/smoke.py ||
    fail "packages/writ-py/scripts/smoke.py failed"
  py_smoke=1
else
  echo "uv not found: skipping packages/writ-py/scripts/smoke.py, so the standalone module gets no stamp"
fi

echo "$SOURCE" > "$OUT/writ.source"
[ "$py_smoke" = 0 ] || echo "$SOURCE" > "$OUT_PY/writ.source"
echo "writ.source: $SOURCE"
