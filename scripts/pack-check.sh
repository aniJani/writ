#!/usr/bin/env bash
# Builds packages/writ and checks what `npm publish` would upload: the tarball must hold exactly
# dist/src/<name>.js, .js.map and .d.ts for each src/<name>.ts, wasm/writ.wasm, wasm/writ.mjs,
# package.json, README.md and LICENSE. Then installs the real tarball into an empty temporary
# project, outside the repository, runs the root, simple, ai-sdk and firestore entry points from it
# and type-checks a TypeScript consumer of all four with the package's own tsc. Prints the
# tarball's size. Never publishes. Exit 0 when all hold, 1 otherwise.
set -euo pipefail
# `npm publish --dry-run` exports npm_config_dry_run=true, which stops `npm pack` writing the tarball.
unset npm_config_dry_run
cd "$(dirname "$0")/../packages/writ"
pkg=$(pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Runs `npm pack` with the given flags and prints its JSON; on failure shows npm's stderr, which
# carries a failing prepack's error.
pack() {
  if ! npm pack "$@" --json 2>"$tmp/pack.err"; then
    cat "$tmp/pack.err" >&2
    echo "npm pack $* failed" >&2
    return 1
  fi
}

node scripts/check-wasm.mjs
npm run build --silent

expected=$(
  {
    for f in src/*.ts; do
      n=$(basename "$f" .ts)
      printf 'dist/src/%s.js\ndist/src/%s.js.map\ndist/src/%s.d.ts\n' "$n" "$n" "$n"
    done
    printf '%s\n' wasm/writ.wasm wasm/writ.mjs package.json README.md LICENSE
  } | LC_ALL=C sort
)
dry=$(pack --dry-run)
actual=$(printf '%s' "$dry" | node -e '
  let s = ""
  process.stdin.on("data", (d) => (s += d)).on("end", () => {
    for (const f of JSON.parse(s)[0].files) console.log(f.path)
  })' | LC_ALL=C sort)
if [ "$expected" != "$actual" ]; then
  echo "the tarball's file list differs from the expected one (< expected, > packed):"
  diff <(printf '%s\n' "$expected") <(printf '%s\n' "$actual") | grep '^[<>]' | sed 's/^/  /'
  exit 1
fi
echo "ok   file list: $(printf '%s\n' "$actual" | wc -l | tr -d ' ') files"

real=$(pack --pack-destination "$tmp")
packed=$(printf '%s' "$real" | node -e '
  let s = ""
  process.stdin.on("data", (d) => (s += d)).on("end", () => {
    const p = JSON.parse(s)[0]
    console.log(`${p.filename} ${p.size} ${p.unpackedSize}`)
  })')
read -r tgz size unpacked <<< "$packed"

mkdir "$tmp/app"
cd "$tmp/app"
printf '{ "private": true, "type": "module" }\n' > package.json
npm install "$tmp/$tgz" --no-audit --no-fund --loglevel=error >/dev/null

cat > root.mjs <<'EOF'
import { loadKernel } from "@anijani/writ"
const kernel = await loadKernel(), policy = JSON.stringify({ writ: "0.1", actions: { search: { consent: "none" } } })
const report = kernel.check(policy); if (!report.ok) throw new Error(JSON.stringify(report.errors))
const r = kernel.step(policy, kernel.initial(policy).state, { type: "session_start", seq: 1, time: 0, state_version: 0, session_id: "s1", policy_digest: report.policy_digest, requester: "u1", permissions: [], approvers: {}, ledger: {} })
if (r.verdict.verdict !== "accepted" || r.stateVersion !== 1) throw new Error(JSON.stringify(r.verdict))
EOF

cat > simple.mjs <<'EOF'
import { simpleGate } from "@anijani/writ/simple"
const s = await (await simpleGate({ user: "user:alice", tools: { search: "none", send_email: "per_call" } })).session()
const ran = await s.run(await s.propose("search", { q: "tea" }), async () => "3 results")
const email = await s.propose("send_email", { to: "bob@example.com" })
if (!ran.ran || ran.value !== "3 results" || email.status !== "needs_approval") throw new Error(JSON.stringify({ ran, email }))
EOF

cat > ai-sdk.mjs <<'EOF'
import { createGate, loadKernel, MemoryStore } from "@anijani/writ"; import { writTools } from "@anijani/writ/ai-sdk"
const gate = createGate({ kernel: await loadKernel(), policyText: JSON.stringify({ writ: "0.1", actions: { search: { consent: "none" } } }), store: new MemoryStore() })
await gate.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: {}, userInitiated: true }); await gate.stepStart("s1")
const w = writTools({ gate, sessionId: "s1", tools: { search: { execute: async ({ q }) => `results for ${q}` } } }), toolCall = { toolCallId: "c1", toolName: "search", input: { q: "tea" } }
if (await w.toolApproval({ toolCall }) !== "not-applicable" || await w.tools.search.execute(toolCall.input, { toolCallId: "c1" }) !== "results for tea") throw new Error("ai-sdk")
EOF

# The firestore entry point types Firestore structurally, so it loads without any firebase package.
cat > firestore.mjs <<'EOF'
import { FirestoreStore, MAX_TEXT_BYTES } from "@anijani/writ/firestore"
const store = new FirestoreStore({ collection: () => ({ doc: () => ({}) }), runTransaction: async (fn) => fn({}) })
if (store.maxStateBytes !== MAX_TEXT_BYTES) throw new Error("firestore")
EOF

for entry in root simple ai-sdk firestore; do
  node "$entry.mjs"
  echo "ok   $entry entry point from the installed tarball"
done

cat > consumer.ts <<'EOF'
import { loadKernel, type Kernel } from "@anijani/writ"
import { simpleGate, type SimpleGate } from "@anijani/writ/simple"
import { writTools, type WritTools } from "@anijani/writ/ai-sdk"
import { FirestoreStore, type FirestoreLike } from "@anijani/writ/firestore"
export async function use(db: FirestoreLike): Promise<[Kernel, SimpleGate, WritTools, FirestoreStore]> {
  const kernel = await loadKernel(), simple = await simpleGate({ user: "user:alice", tools: { search: "none" } })
  const tools = writTools({ gate: simple.gate, sessionId: "s1", tools: { search: { execute: async (input: { q: string }) => input.q } } })
  return [kernel, simple, tools, new FirestoreStore(db)]
}
EOF
printf '%s\n' '{ "compilerOptions": { "module": "nodenext", "moduleResolution": "nodenext", "target": "es2022",' \
  '"strict": true, "noEmit": true, "skipLibCheck": false, "types": [] }, "files": ["consumer.ts"] }' > tsconfig.json
"$pkg/node_modules/.bin/tsc" -p tsconfig.json
echo "ok   TypeScript consumer of all four entry points type-checks"

echo "tarball: $tgz, $size bytes ($unpacked bytes unpacked)"
