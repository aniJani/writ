#!/usr/bin/env bash
# Regenerates the standard corpus from the fixture policies in corpus/standard/fixtures into
# build/corpus/standard/, compares each fixture's traces, states, truncated flag and SHA-256 with
# corpus/standard/manifest.json, replays the generated and hand-written corpora, judges them with the
# spec-side checkers (writ-fuzz --judge), and checks that
# every reason code in schema/reasons.json is reached by some replayed verdict or listed, with a
# reason, in corpus/standard/uncovered.json, and that no listed code is reached after all.
#   --update   rewrite the manifest from this run (a fixture missing from it gets depth 3 and
#              max_states 20000; edit them and run --update again)
#   --tar      also write build/writ-corpus-<cliVersion>.tar.gz with the generated and hand-written
#              corpora, the digest and profile vectors and the READMEs
# Needs only the writ and writ-fuzz binaries (built here), POSIX tools and, for --tar, python3
# (scripts/tarball.py, which makes the tarball reproducible). Exit 0 when everything
# holds, 2 for a bad flag or a build failure, 1 otherwise.
set -euo pipefail
cd "$(dirname "$0")/.."

update=0
tar=0
for a in "$@"; do
  case "$a" in
    --update) update=1 ;;
    --tar) tar=1 ;;
    *) echo "usage: scripts/corpus.sh [--update] [--tar]" >&2; exit 2 ;;
  esac
done

mkdir -p build/corpus
if ! lake build writ writ-fuzz > build/corpus/build.log 2>&1; then
  tail -20 build/corpus/build.log
  echo "build failed (full output in build/corpus/build.log)"
  exit 2
fi
BIN=.lake/build/bin/writ
STD=corpus/standard
MANIFEST=$STD/manifest.json
OUT=build/corpus/standard

if command -v sha256sum >/dev/null; then sha() { sha256sum "$1" | cut -d' ' -f1; }
else sha() { shasum -a 256 "$1" | cut -d' ' -f1; }
fi

# The manifest holds one fixture object per line, as --update writes it.
field() { printf '%s\n' "$1" | sed -n "s/.*\"$2\": *\"\{0,1\}\([^,\"}]*\)\"\{0,1\} *[,}].*/\1/p"; }
entry() { [ ! -f "$MANIFEST" ] || grep -F "\"policy\": \"fixtures/$1.json\"" "$MANIFEST" || true; }

rm -rf "$OUT"
mkdir -p "$OUT"
status=0
lines=()
for f in "$STD"/fixtures/*.json; do
  name=$(basename "$f" .json)
  line=$(entry "$name")
  depth=$(field "$line" depth)
  max=$(field "$line" max_states)
  if [ -z "$line" ]; then
    echo "$name: not in the manifest"
    status=1
    depth=3
    max=20000
  fi
  err=$("$BIN" traces "$f" --depth "$depth" --max-states "$max" --out "$OUT" 2>&1 >/dev/null) ||
    { echo "$name: writ traces failed: $err"; exit 1; }
  states=$(printf '%s' "$err" | sed -n 's/^states \([0-9]*\), .*/\1/p')
  traces=$(printf '%s' "$err" | sed -n 's/.*, traces \([0-9]*\) .*/\1/p')
  truncated=false
  case "$err" in *", truncated"*) truncated=true ;; esac
  digest=$(sha "$OUT/$name.jsonl")
  echo "$name: depth $depth, states $states, traces $traces, truncated $truncated"
  if [ -n "$line" ]; then
    for k in traces states truncated; do
      want=$(field "$line" "$k")
      got=${!k}
      [ "$want" = "$got" ] || { echo "$name: $k $got, the manifest says $want"; status=1; }
    done
    want=$(field "$line" sha256)
    [ "$want" = "$digest" ] || { echo "$name: sha256 $digest, the manifest says $want"; status=1; }
  fi
  lines+=("    { \"policy\": \"fixtures/$name.json\", \"depth\": $depth, \"max_states\": $max, \"traces\": $traces, \"states\": $states, \"truncated\": $truncated, \"sha256\": \"$digest\" }")
done
if [ -f "$MANIFEST" ]; then
  while IFS= read -r p; do
    [ -f "$STD/$p" ] || { echo "$p: in the manifest, but there is no such fixture"; status=1; }
  done < <(sed -n 's/.*"policy": "\([^"]*\)".*/\1/p' "$MANIFEST")
fi

if [ "$update" = 1 ]; then
  {
    printf '{\n  "generator": 1,\n  "fixtures": [\n'
    for i in "${!lines[@]}"; do
      if [ "$i" -lt $((${#lines[@]} - 1)) ]; then printf '%s,\n' "${lines[$i]}"; else printf '%s\n' "${lines[$i]}"; fi
    done
    printf '  ]\n}\n'
  } > "$MANIFEST"
  echo "wrote $MANIFEST"
  status=0
elif [ "$status" != 0 ]; then
  echo "the generated corpus changed; review the difference, then run scripts/corpus.sh --update"
  exit 1
fi

# corpus/sep-2848.json maps SEP-2848's statements to traces in corpus/examples, so it has nothing
# of its own to replay. corpus/attacks is optional.
hand=(corpus/examples/*.jsonl)
for d in corpus/attacks corpus/sep-2848; do
  for t in "$d"/*.jsonl; do
    if [ -e "$t" ]; then hand+=("$t"); fi
  done
done
log=build/corpus/replay.log
if ! "$BIN" replay --coverage "$OUT"/*.jsonl "${hand[@]}" > "$log"; then
  grep -m 20 '^FAIL ' "$log" || true
  grep -E '^[0-9]+ traces?, [0-9]+ failed$' "$log" || true
  echo "replay failed (full output in $log)"
  exit 1
fi
tail -2 "$log" | sed -n 1p
judged=build/corpus/judge.log
if ! .lake/build/bin/writ-fuzz --judge "$OUT"/*.jsonl "${hand[@]}" > "$judged"; then
  grep -v '^judged ' "$judged" | head -20
  tail -1 "$judged"
  echo "the spec-side judge failed (full output in $judged)"
  exit 1
fi
tail -1 "$judged"
coverage=$(tail -1 "$log")
covered=$(printf '%s' "$coverage" | sed 's/.*"reasons":\[\([^]]*\)\].*/\1/' | tr ',' '\n' | tr -d '"')
# Both files are a JSON array with one {"code": ..., "<key>": ...} object per line; any other layout
# is refused rather than read as fewer codes.
codes() {
  if grep -qv -e '^[][ ]*$' \
      -e '^ *\[\{0,1\} *{ *"code": "[^"]*", *"[a-z]*": *"[^"\\]*" *} *\]\{0,1\},\{0,1\} *$' "$1" ||
      ! grep -q '^ *\[' "$1"; then
    echo "$1: expected a JSON array with one {\"code\": ...} object per line" >&2
    return 1
  fi
  sed -n 's/^ *\[\{0,1\} *{ *"code": "\([^"]*\)".*/\1/p' "$1"
}
known=$(codes schema/reasons.json) || exit 1
listed=$(codes "$STD/uncovered.json") || exit 1
[ -n "$known" ] || { echo "schema/reasons.json: no reason codes"; exit 1; }
for c in $known; do
  if ! grep -qx "$c" <<< "$covered" && ! grep -qx "$c" <<< "$listed"; then
    echo "reason $c: no replayed verdict reaches it and $STD/uncovered.json does not list it"
    status=1
  fi
done
for c in $listed; do
  if ! grep -qx "$c" <<< "$known"; then
    echo "reason $c: listed in $STD/uncovered.json but not in schema/reasons.json"
    status=1
  elif grep -qx "$c" <<< "$covered"; then
    echo "reason $c: listed in $STD/uncovered.json but now covered; remove it from the list"
    status=1
  fi
done
[ "$status" = 0 ] || exit 1
echo "every reason code is covered or listed in $STD/uncovered.json ($(grep -c . <<< "$listed" || true) listed)"

if [ "$tar" = 1 ]; then
  version=$("$BIN" --version | cut -d' ' -f2)
  stage=build/tar/writ-corpus-$version
  rm -rf build/tar
  mkdir -p "$stage/standard/traces"
  cp "$OUT"/*.jsonl "$stage/standard/traces/"
  cp -R "$STD/fixtures" "$MANIFEST" "$STD/uncovered.json" "$STD/README.md" "$stage/standard/"
  cp -R corpus/examples corpus/digests corpus/profiles corpus/sep-2848.json "$stage/"
  for d in corpus/attacks corpus/sep-2848; do
    if [ -d "$d" ]; then cp -R "$d" "$stage/"; fi
  done
  if [ -f corpus/README.md ]; then cp corpus/README.md "$stage/"; fi
  tarball=build/writ-corpus-$version.tar.gz
  python3 -I scripts/tarball.py "$tarball" build/tar "writ-corpus-$version"
  rm -rf build/tar
  echo "wrote $tarball"
fi
