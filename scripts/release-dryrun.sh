#!/usr/bin/env bash
# Rehearses a release on this machine and publishes nothing: runs the checks
# .github/workflows/release.yml runs, then builds every asset it uploads into build/release/out/,
# through the same scripts/release-build.sh:
#   version   scripts/check-version.sh --unreleased (nothing is released, so the CHANGELOG heading
#             may wait)
#   actionlint  both workflows, with actionlint when it is installed, otherwise the rhysd/actionlint
#             Docker image pinned by digest below
#   build, proofs, cli, traces, mutants   the green set: lake build, scripts/check-proofs.sh,
#             scripts/cli-test.sh, writ-fuzz --traces 1000 and --mutants (scripts/corpus.sh runs
#             in the corpus step)
#   wasm, npm-suites, py-test   scripts/build-wasm.sh, npm test in packages/writ, examples/langgraph,
#             examples/ai-sdk and playground, and scripts/py-test.sh
#   binary, npm, python, corpus   the assets: the host's binary tarball, the npm tarball after a dry
#             run of the npm publish, the Python wheel and sdist, and the corpus tarball
#   linux-*   with --linux only: in a linux/arm64 Ubuntu 24.04 container (build/release/Dockerfile),
#             lake build, the CLI cases, the proof checks, both fuzz runs and scripts/corpus.sh,
#             which checks the corpus manifest's sha256s on Linux, then the linux-arm64 tarball
#   sums      SHA256SUMS over the assets, after checking out/ holds exactly the expected ones
#
#   scripts/release-dryrun.sh [--linux] [--fresh]
#
# A step that passes is recorded in build/release/state/ against a hash of the source (the files git
# tracks or would track, and HEAD's commit time), and a later run on the same source skips it, so a
# run cut off by a timeout resumes. Another source, or --fresh, starts over and empties
# build/release/out/. Each step's output is in build/release/logs/<step>.log. The container keeps
# its toolchain and .lake in the Docker volumes writ-release-elan and writ-release-lake; `docker
# volume rm` them to start it clean.
# Exit 0 when every step passes, 1 naming the step that failed, 2 for a usage error.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO=$(pwd)

# actionlint 1.7.12, which bundles shellcheck for the run: scripts.
ACTIONLINT_IMAGE=rhysd/actionlint@sha256:b1934ee5f1c509618f2508e6eb47ee0d3520686341fec936f3b79331f9315667
LINUX_IMAGE=writ-release-linux
LINUX_CONTAINER=writ-release-linux
OUT=build/release/out
STATE=build/release/state
LOGS=build/release/logs

linux=0
fresh=0
for a in "$@"; do
  case "$a" in
    --linux) linux=1 ;;
    --fresh) fresh=1 ;;
    *) echo "usage: scripts/release-dryrun.sh [--linux] [--fresh]" >&2; exit 2 ;;
  esac
done

version=$(sed -n 's/^def cliVersion : String := "\([^"]*\)"$/\1/p' Writ/Core/Version.lean)
case "$version" in
  *-preview.*) pep440=${version%-preview.*}a${version##*-preview.} ;;
  *) pep440=$version ;;
esac
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) target="linux-x64" ;;
  Linux-aarch64 | Linux-arm64) target="linux-arm64" ;;
  Darwin-arm64) target="macos-arm64" ;;
  *) echo "release-dryrun: no release target for $(uname -s) $(uname -m)" >&2; exit 1 ;;
esac

if command -v sha256sum >/dev/null; then SHA=(sha256sum)
else SHA=(shasum -a 256)
fi
# NUL-separated paths of the files git tracks or would track, deleted ones left out.
sources() {
  git ls-files -z -co --exclude-standard | while IFS= read -r -d '' f; do
    if [ -f "$f" ]; then printf '%s\0' "$f"; fi
  done
}
# HEAD's commit time is in the key because scripts/tarball.py dates every tarball entry with it.
SRC=$({ sources | xargs -0 "${SHA[@]}"; git log -1 --format=%ct; } | "${SHA[@]}" | cut -d' ' -f1)

if [ "$fresh" = 1 ] || [ "$(cat "$STATE/source" 2>/dev/null || true)" != "$SRC" ]; then
  rm -rf "$OUT" "$STATE" "$LOGS"
fi
mkdir -p "$OUT" "$STATE" "$LOGS"
echo "$SRC" > "$STATE/source"
START=$(date +%s)
echo "release dry run of $version (PEP 440 $pep440), source $SRC"

# Runs "$@" as step $1 unless it passed on this source before; stops the run when it fails.
step() {
  name=$1
  shift
  if [ "$(cat "$STATE/$name" 2>/dev/null || true)" = "$SRC" ]; then
    echo "skip $name: passed on this source in an earlier run"
    return
  fi
  t=$(date +%s)
  set +e
  (set -e; "$@") > "$LOGS/$name.log" 2>&1
  rc=$?
  set -e
  if [ "$rc" != 0 ]; then
    tail -40 "$LOGS/$name.log" | sed 's/^/  | /'
    echo "release-dryrun: step $name failed (exit $rc; full output in $LOGS/$name.log)" >&2
    exit 1
  fi
  echo "$SRC" > "$STATE/$name"
  echo "ok   $name ($(($(date +%s) - t))s): $(grep . "$LOGS/$name.log" | tail -1 | cut -c1-160)"
}

lint_workflows() {
  if command -v actionlint >/dev/null; then
    actionlint .github/workflows/ci.yml .github/workflows/release.yml
  else
    docker run --rm -v "$REPO:/repo" -w /repo "$ACTIONLINT_IMAGE" -no-color \
      .github/workflows/ci.yml .github/workflows/release.yml
  fi
  echo "actionlint: both workflows clean"
}

npm_suites() {
  for d in packages/writ examples/langgraph examples/ai-sdk; do
    (cd "$d" && npm ci --no-audit --no-fund)
  done
  for d in packages/writ examples/langgraph examples/ai-sdk playground; do
    echo "== $d"
    (cd "$d" && npm test)
  done
  echo "npm suites passed in packages/writ, examples/langgraph, examples/ai-sdk and playground"
}

# Runs in the container, from its root shell. SRC is the host's source hash, FRESH is 1 for --fresh,
# SOURCE_DATE_EPOCH dates the tarball (the container has no git), and HOST_UID:HOST_GID, set on a
# Linux host, owns the tarball written to the host's out/.
read -r -d '' LINUX_SCRIPT <<'EOF' || true
set -euo pipefail
tar --warning=no-unknown-keyword -xf - -C /writ
cd /writ
marks=.lake/release-dryrun
[ "$FRESH" = 0 ] || rm -rf "$marks"
mkdir -p "$marks"
run() {
  name=$1
  shift
  if [ "$(cat "$marks/$name" 2>/dev/null || true)" = "$SRC" ]; then
    echo "skip linux-$name: passed on this source in an earlier run"
    return
  fi
  t=$(date +%s)
  if ! "$@" > "$marks/$name.log" 2>&1; then
    tail -40 "$marks/$name.log" | sed 's/^/  | /'
    echo "release-dryrun: step linux-$name failed" >&2
    exit 1
  fi
  echo "$SRC" > "$marks/$name"
  echo "ok   linux-$name ($(($(date +%s) - t))s): $(grep . "$marks/$name.log" | tail -1 | cut -c1-160)"
}
run toolchain elan toolchain install "$(cat lean-toolchain)"
run build lake build
run cli scripts/cli-test.sh
run proofs scripts/check-proofs.sh
run traces lake exe writ-fuzz --traces 1000
run mutants lake exe writ-fuzz --mutants
run corpus scripts/corpus.sh
sed "s/^/  linux-corpus | /" "$marks/corpus.log"
# The tarball goes to the host's out/, which a host run with --fresh empties, so it is always packed.
rm -f "$marks/binary"
run binary scripts/release-build.sh binary /out
if [ -n "$HOST_UID" ]; then chown "$HOST_UID:$HOST_GID" /out/writ-*-linux-arm64.tar.gz; fi
EOF

# Called in an || list, where set -e is off, so every failure returns explicitly.
linux_run() {
  docker build --quiet --platform linux/arm64 -t "$LINUX_IMAGE" - < build/release/Dockerfile > /dev/null ||
    { echo "docker build of build/release/Dockerfile failed"; return 1; }
  if docker container inspect "$LINUX_CONTAINER" > /dev/null 2>&1; then
    echo "following the container an earlier, cut-off run left"
    docker logs -f --tail 5 "$LINUX_CONTAINER" || true
    docker rm -f "$LINUX_CONTAINER" > /dev/null 2>&1 || true
  fi
  # A cut-off run stops its container rather than leave it working; .lake keeps what was built.
  trap 'docker kill "$LINUX_CONTAINER" > /dev/null 2>&1 || true; exit 130' INT TERM HUP
  host_uid="" host_gid=""
  if [ "$(uname -s)" = Linux ]; then host_uid=$(id -u) host_gid=$(id -g); fi
  rc=0
  sources | COPYFILE_DISABLE=1 tar --no-xattrs --null -T - -cf - |
    docker run --rm -i --init --name "$LINUX_CONTAINER" --platform linux/arm64 \
      -v writ-release-elan:/root/.elan -v writ-release-lake:/writ/.lake -v "$REPO/$OUT:/out" \
      -e SRC="$SRC" -e FRESH="$fresh" -e SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)" \
      -e HOST_UID="$host_uid" -e HOST_GID="$host_gid" "$LINUX_IMAGE" bash -c "$LINUX_SCRIPT" || rc=1
  trap - INT TERM HUP
  if [ "$rc" != 0 ]; then
    # The run's own output may be gone (a followed or killed container), so name the first step
    # without a mark for this source and show its log from the volume.
    docker run --rm -v writ-release-lake:/writ/.lake -e SRC="$SRC" "$LINUX_IMAGE" bash -c '
      for s in toolchain build cli proofs traces mutants corpus binary; do
        if [ "$(cat ".lake/release-dryrun/$s" 2>/dev/null || true)" != "$SRC" ]; then
          echo "release-dryrun: step linux-$s failed or did not finish; the end of its log:"
          tail -40 ".lake/release-dryrun/$s.log" 2>/dev/null | sed "s/^/  | /"
          break
        fi
      done'
  fi
  return "$rc"
}

check_assets() {
  want=("writ-$version-$target.tar.gz" "anijani-writ-$version.tgz" "writ_kernel-$pep440-py3-none-any.whl"
    "writ_kernel-$pep440.tar.gz" "writ-corpus-$version.tar.gz")
  [ "$linux" = 0 ] || want+=("writ-$version-linux-arm64.tar.gz")
  for f in "${want[@]}"; do
    [ -f "$OUT/$f" ] || { echo "$OUT/$f is missing"; return 1; }
  done
  for f in "$OUT"/*; do
    f=${f#"$OUT"/}
    case " ${want[*]} SHA256SUMS writ-$version-linux-arm64.tar.gz " in
      *" $f "*) ;;
      *) echo "$OUT/$f is not a release asset"; return 1 ;;
    esac
  done
}

step version scripts/check-version.sh --unreleased
step actionlint lint_workflows
step build lake build
step proofs scripts/check-proofs.sh
step cli scripts/cli-test.sh
step traces lake exe writ-fuzz --traces 1000
step mutants lake exe writ-fuzz --mutants
step wasm scripts/build-wasm.sh
step npm-suites npm_suites
step py-test scripts/py-test.sh
step binary scripts/release-build.sh binary "$OUT"
step npm scripts/release-build.sh npm "$OUT"
step python scripts/release-build.sh python "$OUT"
step corpus scripts/release-build.sh corpus "$OUT"
if [ "$linux" = 1 ]; then
  echo "== linux: building and testing in a linux/arm64 container"
  linux_run || { echo "release-dryrun: the Linux run failed" >&2; exit 1; }
fi
check_assets || { echo "release-dryrun: step assets failed" >&2; exit 1; }
scripts/release-build.sh sums "$OUT" > "$LOGS/sums.log" 2>&1 ||
  { cat "$LOGS/sums.log"; echo "release-dryrun: step sums failed" >&2; exit 1; }
echo "ok   sums: $OUT/SHA256SUMS"
(cd "$OUT" && while read -r hash name; do
  printf '  %s  %10s bytes  %s\n' "$hash" "$(wc -c < "$name" | tr -d ' ')" "$name"
done < SHA256SUMS)
echo "release dry run passed in $(($(date +%s) - START))s; nothing was published"
