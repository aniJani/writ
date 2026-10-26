#!/bin/sh
# Runs every tests/cli/*.case against the writ binary from the repo root.
# A case file has lines "cmd: <path>" (optional, a program to run instead of the writ binary),
# "args: ...", "stdin: <file>" (optional), "exit: N",
# "stderr: <text>" (optional, must occur in stderr),
# "outfile: <actual> <expected>" (optional, the files must be byte-identical) and
# "errfile: <expected>" (optional, stderr must be byte-identical to that file).
# "@TMP@" in args, outfile and errfile expands to a scratch dir.
# Expected stdout is tests/cli/<name>.out.
set -u
cd "$(dirname "$0")/.." || exit 2
lake build writ >/dev/null || { echo "build failed"; exit 2; }
BIN=.lake/build/bin/writ
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
printf '{"writ":"0.1","actions":{"a\377":{}}}\n' > "$TMP/not-utf8.json"

pass=0
fail=0
for c in tests/cli/*.case; do
  name=$(basename "$c" .case)
  cmd=$(sed -n 's/^cmd: *//p' "$c")
  [ -n "$cmd" ] || cmd=$BIN
  args=$(sed -n 's/^args: *//p' "$c" | sed "s|@TMP@|$TMP|g")
  stdin=$(sed -n 's/^stdin: *//p' "$c")
  want_exit=$(sed -n 's/^exit: *//p' "$c")
  want_err=$(sed -n 's/^stderr: *//p' "$c")
  outfile=$(sed -n 's/^outfile: *//p' "$c" | sed "s|@TMP@|$TMP|g")
  errfile=$(sed -n 's/^errfile: *//p' "$c" | sed "s|@TMP@|$TMP|g")
  [ -n "$stdin" ] || stdin=/dev/null
  set -f
  # shellcheck disable=SC2086
  "$cmd" $args < "$stdin" > "$TMP/stdout" 2> "$TMP/stderr"
  got_exit=$?
  set +f
  problems=""
  [ "$got_exit" = "$want_exit" ] || problems="$problems exit $got_exit, want $want_exit;"
  if ! cmp -s "$TMP/stdout" "tests/cli/$name.out"; then
    problems="$problems stdout differs;"
    diff "tests/cli/$name.out" "$TMP/stdout" | head -20
  fi
  if [ "$want_exit" = 2 ]; then
    [ -s "$TMP/stderr" ] || problems="$problems stderr empty;"
    [ ! -s "$TMP/stdout" ] || problems="$problems stdout not empty;"
  fi
  if [ -n "$want_err" ] && ! grep -qF -- "$want_err" "$TMP/stderr"; then
    problems="$problems stderr lacks '$want_err';"
  fi
  if [ -n "$errfile" ] && ! cmp -s "$TMP/stderr" "$errfile"; then
    problems="$problems stderr differs from $errfile;"
    diff "$errfile" "$TMP/stderr" | head -20
  fi
  if [ -n "$outfile" ]; then
    set -f
    # shellcheck disable=SC2086
    set -- $outfile
    set +f
    cmp -s "$1" "$2" || problems="$problems $1 differs from $2;"
  fi
  if [ -z "$problems" ]; then
    pass=$((pass + 1))
    echo "pass $name"
  else
    fail=$((fail + 1))
    echo "FAIL $name:$problems"
  fi
done
# Every policy writ expand prints must itself pass writ check as a layer-1 policy.
for o in tests/cli/expand-*.out; do
  grep -q '^exit: 0$' "${o%.out}.case" && [ -s "$o" ] || continue
  cp "$o" "$TMP/expanded.json"
  if "$BIN" check "$TMP/expanded.json" > /dev/null 2>&1; then
    pass=$((pass + 1))
    echo "pass $(basename "$o" .out) output checks"
  else
    fail=$((fail + 1))
    echo "FAIL $(basename "$o" .out): its output fails writ check"
  fi
done
# writ traces at the default depth must give the same bytes on a second run, and its traces must replay.
for p in tests/cli/traces/tiny.json tests/cli/traces/tiny-l2.json; do
  name="traces $(basename "$p" .json)"
  "$BIN" traces "$p" > "$TMP/traces-1.jsonl" 2> /dev/null
  "$BIN" traces "$p" > "$TMP/traces-2.jsonl" 2> /dev/null
  if [ -s "$TMP/traces-1.jsonl" ] && cmp -s "$TMP/traces-1.jsonl" "$TMP/traces-2.jsonl" &&
      "$BIN" replay "$TMP/traces-1.jsonl" > /dev/null 2>&1; then
    pass=$((pass + 1))
    echo "pass $name: stable and replays"
  else
    fail=$((fail + 1))
    echo "FAIL $name: a second run differs or the traces do not replay"
  fi
done
# The four version files agree; the CHANGELOG heading waits for the release itself.
if out=$(scripts/check-version.sh --unreleased 2>&1); then
  pass=$((pass + 1))
  echo "pass check-version on this repository"
else
  fail=$((fail + 1))
  echo "FAIL check-version on this repository:"
  printf '%s\n' "$out" | grep -v '^ok ' | sed 's/^/  /'
fi
# Prints the commands in file $1 that publish, tag or push. Only release.yml's publish job may; the
# dry run and every script it calls may run `npm publish --dry-run` and nothing else of the kind.
# Comment lines are dropped and each line is split at ;, &, | and " #" first, so a --dry-run in a
# comment or in another command on the line exempts nothing, and a " #" inside quotes hides nothing. A command spelled
# through a variable, or continued onto the next line with a backslash, is a known blind spot.
publishes() {
  grep -v '^[[:space:]]*#' "$1" | awk '{ gsub(/[[:space:]]#|[;&|]/, "\n"); print }' > "$TMP/commands"
  grep -E \
    -e '(^|[^[:alnum:]_-])gh[[:space:]]+release' \
    -e '(^|[^[:alnum:]_-])gh[[:space:]]+api[[:space:]].*releases' \
    -e '(^|[^[:alnum:]_-])git([[:space:]]+[^[:space:]]+)*[[:space:]]+(tag|push)([^[:alnum:]_-]|$)' \
    -e '(^|[^[:alnum:]_-])docker([[:space:]]+[^[:space:]]+)*[[:space:]]+push([^[:alnum:]_-]|$)' \
    -e '(^|[^[:alnum:]_-])twine([[:space:]]+[^[:space:]]+)*[[:space:]]+upload' \
    -e '(^|[^[:alnum:]_-])uv([[:space:]]+[^[:space:]]+)*[[:space:]]+publish' "$TMP/commands"
  grep -E '(^|[^[:alnum:]_-])(npm|pnpm|yarn)([[:space:]]+[^[:space:]]+)*[[:space:]]+publish' "$TMP/commands" |
    grep -v -e '--dry-run'
}
for s in scripts/release-dryrun.sh scripts/release-build.sh scripts/check-version.sh scripts/tarball.py \
    scripts/build-wasm.sh scripts/py-test.sh scripts/corpus.sh scripts/check-proofs.sh scripts/pack-check.sh \
    packages/writ/package.json examples/langgraph/package.json examples/ai-sdk/package.json playground/package.json; do
  if [ -f "$s" ] && [ -z "$(publishes "$s")" ]; then
    pass=$((pass + 1))
    echo "pass $s publishes nothing"
  else
    fail=$((fail + 1))
    echo "FAIL $s is missing or publishes:"
    [ ! -f "$s" ] || publishes "$s" | sed 's/^/  /'
  fi
done
bad=0
for line in 'npm publish --tag preview' 'npm --workspace x publish' 'pnpm publish' 'yarn npm publish' \
    'git push origin v1' 'git -C . tag v1' 'docker push writ:1' 'gh release create v1 out/*' \
    'gh api repos/o/r/releases -f tag_name=v1' 'uvx twine upload out/*' 'uv publish out/*' 'uv --quiet publish' \
    'echo ok; npm publish' 'npm publish --tag preview # --dry-run' 'npm publish --dry-run && npm publish' \
    'true | uv publish' "printf ' #'; npm publish"; do
  { cat scripts/release-dryrun.sh; printf '%s\n' "$line"; } > "$TMP/publishes.sh"
  [ -n "$(publishes "$TMP/publishes.sh")" ] || { bad=1; echo "  not caught: $line"; }
done
printf '%s\n' 'npm publish --dry-run --tag preview # rehearsal' '# git push is never run here' \
  'npm pack --dry-run' 'git -C x fetch origin refs/tags/v1' > "$TMP/publishes.sh"
[ -z "$(publishes "$TMP/publishes.sh")" ] || { bad=1; echo "  flagged: a dry run, a comment, a pack or a fetch"; }
if [ "$bad" = 0 ]; then
  pass=$((pass + 1))
  echo "pass the no-publish check catches publishing added to the dry run"
else
  fail=$((fail + 1))
  echo "FAIL the no-publish check"
fi
echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
