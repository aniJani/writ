// Smoke test for packages/writ/wasm/writ.{mjs,wasm}: run from anywhere with `node build/wasm/smoke.mjs`.
// Exits nonzero on the first mismatch.
import { createHash } from "node:crypto";
import { readdirSync, readFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";
import { dirname, join } from "node:path";

const repo = join(dirname(fileURLToPath(import.meta.url)), "../..");
const fixture = (p) => readFileSync(join(repo, "tests/cli", p), "utf8");

let failures = 0;
function expect(ok, what, detail = "") {
  if (ok) {
    console.log(`ok   ${what}`);
  } else {
    failures++;
    console.log(`FAIL ${what}${detail ? `\n     ${detail}` : ""}`);
  }
}

const modulePath = join(repo, "packages/writ/wasm/writ.mjs");
let Factory;
try {
  Factory = (await import(pathToFileURL(modulePath).href)).default;
} catch (e) {
  console.log(`FAIL load ${modulePath}: ${e.message}`);
  process.exit(1);
}
const m = await Factory();

const enc = new TextEncoder();
const dec = new TextDecoder("utf-8", { fatal: true });

function call(fn, ...args) {
  const bufs = [0, 1, 2].map((i) => {
    const a = args[i] ?? "";
    return typeof a === "string" ? enc.encode(a) : a;
  });
  const ptrs = bufs.map((b) => {
    const p = m._malloc(Math.max(b.length, 1));
    m.HEAPU8.set(b, p);
    return p;
  });
  const outLen = m._malloc(4);
  const r = m._writ_call(fn, ptrs[0], bufs[0].length, ptrs[1], bufs[1].length, ptrs[2], bufs[2].length, outLen);
  for (const p of ptrs) m._free(p);
  if (r === 0) {
    m._free(outLen);
    throw new Error(`writ_call(${fn}) returned NULL`);
  }
  const n = m.HEAPU32[outLen >> 2];
  m._free(outLen);
  const text = dec.decode(m.HEAPU8.slice(r, r + n));
  m._writ_free(r);
  return text;
}

expect(m._writ_init() === 0, "writ_init() === 0");
expect(m._writ_init() === 0, "writ_init() is idempotent");

const version = call(7);
expect(version === fixture("version.out").trimEnd(), "version matches writ --version", version);

const shop = fixture("policies/formats-shop.json");
const digest = JSON.parse(call(2, shop)).digest;
expect(digest === fixture("formats-digest.out").trimEnd(), "digest of formats-shop.json matches writ digest", digest);

const check = JSON.parse(call(1, shop));
expect(check.ok === true && check.policy_digest === digest, "check of formats-shop.json is ok", JSON.stringify(check));

const simple = fixture("policies/simple.json");
const init = JSON.parse(call(4, simple, ""));
expect(typeof init.state === "string" && init.state_version === 0, "initial gives a state", JSON.stringify(init));

const events = fixture("oracle-events.jsonl").split("\n").filter((l, i, a) => i < a.length - 1 || l !== "");
const want = fixture("oracle-1.out").trimEnd().split("\n");
let state = init.state;
const states = [state];
const got = events.map((line) => {
  const r = JSON.parse(call(5, simple, state, line));
  if ("error" in r) return JSON.stringify({ error: r.error });
  state = r.state;
  states.push(state);
  return JSON.stringify(r.verdict);
});
expect(got.length === want.length && got.every((l, i) => l === want[i]), "oracle sequence matches oracle-1.out",
  got.map((l, i) => (l === want[i] ? "" : `line ${i + 1}: got ${l}, want ${want[i]}`)).filter(Boolean).join("; "));
expect(state + "\n" === fixture("states/after-1.json"), "final state matches states/after-1.json");

// Amounts from 2^31 up are heap Nats on wasm32, so meters run on the runtime's own mpn code,
// where the native oracle that wrote oracle-big.out uses GMP.
const bigPolicy = fixture("policies/big-amounts.json");
let bigState = JSON.parse(call(4, bigPolicy, "")).state;
const bigWant = fixture("oracle-big.out").trimEnd().split("\n");
const bigGot = fixture("oracle-big-events.jsonl").trimEnd().split("\n").map((line) => {
  const r = JSON.parse(call(5, bigPolicy, bigState, line));
  if ("error" in r) return JSON.stringify({ error: r.error });
  bigState = r.state;
  return JSON.stringify(r.verdict);
});
expect(bigGot.length === bigWant.length && bigGot.every((l, i) => l === bigWant[i]), "big-amount sequence matches oracle-big.out",
  bigGot.map((l, i) => (l === bigWant[i] ? "" : `line ${i + 1}: got ${l}, want ${bigWant[i]}`)).filter(Boolean).join("; "));
expect(bigState + "\n" === fixture("states/after-big.json"), "big-amount final state matches states/after-big.json");

// Integers above 2^31 are big Nats on wasm32, so this exercises the GMP-free bignum code.
const big = '{"s":"\\u00e9\\ud83d\\ude00","n":9007199254740991,"m":-9007199254740991,"k":4294967296}';
const bigCanon = '{"k":4294967296,"m":-9007199254740991,"n":9007199254740991,"s":"é😀"}';
const canon = JSON.parse(call(3, big)).canonical;
expect(canon === bigCanon, "canonical of large integers and non-ASCII text", canon);
const sha = "sha256:" + createHash("sha256").update(bigCanon).digest("hex");
expect(JSON.parse(call(2, big)).digest === sha, "digest is SHA-256 of the canonical text");

const corpus = readdirSync(join(repo, "corpus/examples")).filter((f) => f.endsWith(".jsonl"));
for (const f of corpus) {
  const r = JSON.parse(call(6, readFileSync(join(repo, "corpus/examples", f), "utf8")));
  expect(Array.isArray(r.traces) && r.traces.length > 0 && r.traces.every((t) => t.ok), `replay of corpus/examples/${f}`,
    JSON.stringify(r).slice(0, 300));
}

const tomb = JSON.parse(call(8, "", "1"));
expect(tomb.ledger === '{"tombstone":true,"version":1}' && tomb.ledger_version === 1 && tomb.changed === true,
  "tombstone sets the flag on an empty ledger", JSON.stringify(tomb));
const again = JSON.parse(call(8, tomb.ledger, "1"));
expect(again.ledger === tomb.ledger && again.ledger_version === 1 && again.changed === false,
  "tombstone on a tombstoned ledger changes nothing", JSON.stringify(again));
expect(typeof JSON.parse(call(8, "", "yes")).error === "string", "a tombstone flag other than 1 or 0 gives {error}");

let shopState = JSON.parse(call(4, shop, "")).state;
for (const line of fixture("formats-events-a.jsonl").trimEnd().split("\n")) {
  shopState = JSON.parse(call(5, shop, shopState, line)).state;
}
const view = JSON.parse(call(9, shop, shopState, "1100"));
expect(view.session_id === "s1" && view.calls.length === 1 && view.calls[0].status === "awaiting"
  && view.calls[0].request_id?.call === "c1" && view.meters[0]?.used === "0" && view.meters[0]?.cap === "5000",
  "inspect shows the awaiting call and the meter", JSON.stringify(view));
const badTime = JSON.parse(call(9, shop, shopState, "1.5"));
expect(badTime.input === "time", "inspect with a time that is not digits gives {error, input: time}", JSON.stringify(badTime));
const foreign = JSON.parse(call(5, simple, shopState, events[0]));
expect(foreign.input === "state", "a state from another policy gives {error, input: state}", JSON.stringify(foreign));

const vectors = readFileSync(join(repo, "corpus/profiles/mcp-tool-approval-v1.jsonl"), "utf8").trimEnd().split("\n")
  .map((l) => JSON.parse(l));
const vectorMisses = vectors.filter((v) => call(10, JSON.stringify(v.input)) !== JSON.stringify(v.output));
expect(vectorMisses.length === 0, `profile gives all ${vectors.length} vectors of corpus/profiles/mcp-tool-approval-v1.jsonl`,
  vectorMisses.map((v) => v.id).join(", "));
const badProfile = JSON.parse(call(10, '{"profile":"other","status":"unknown"}'));
expect(badProfile.input === "profile", "an unknown profile gives {error, input: profile}", JSON.stringify(badProfile));

const nul = JSON.parse(call(2, Uint8Array.of(0x7b, 0x7d, 0x00)));
expect(typeof nul.error === "string", "input with a NUL byte gives {error}", JSON.stringify(nul));
const bad = JSON.parse(call(2, Uint8Array.of(0x22, 0xff, 0x22)));
expect(typeof bad.error === "string", "input with invalid UTF-8 gives {error}", JSON.stringify(bad));
const nulB = JSON.parse(call(5, simple, Uint8Array.of(0x7b, 0x00, 0x7d), events[0]));
expect(nulB.error === "input b contains a NUL byte" && nulB.input === "state", "a NUL byte in the second input gives {error, input}",
  JSON.stringify(nulB));
expect(typeof JSON.parse(call(99)).error === "string", "unknown fn code gives {error}");

// Two fixed steps, alternated, so every result must equal the first one of its kind.
const pairs = [
  [states[3], events[4]],
  [states[4], events[5]],
];
const first = pairs.map(([s, e]) => call(5, simple, s, e));
// HEAPU8.length alone misses a slow leak: the initial memory has megabytes of slack. A block
// larger than any free chunk is placed at the top of the malloc heap, so its address tracks
// the heap's high-water mark.
const heapTop = () => {
  const p = m._malloc(1 << 20);
  m._free(p);
  return p;
};
const steps = 10000;
let heapAfter100 = 0;
let topAfter100 = 0;
let usedAfter100 = 0;
let drift = 0;
let ms = 0;
for (let i = 0; i < steps; i++) {
  const [s, e] = pairs[i % 2];
  const t = performance.now();
  const r = call(5, simple, s, e);
  ms += performance.now() - t;
  if (r !== first[i % 2]) drift++;
  if (i === 99) {
    heapAfter100 = m.HEAPU8.length;
    topAfter100 = heapTop();
    usedAfter100 = m._writ_heap_used();
  }
}
const heapEnd = m.HEAPU8.length;
const topEnd = heapTop();
expect(drift === 0, `${steps} alternating steps give unchanged results`, `${drift} differ`);
expect(heapEnd <= 2 * heapAfter100, `memory bounded: ${heapAfter100} bytes after 100 steps, ${heapEnd} after ${steps}`);
expect(topEnd - topAfter100 <= 65536, `malloc heap top moved ${topEnd - topAfter100} bytes from step 100 to step ${steps}`);
const usedEnd = m._writ_heap_used();
expect(usedEnd === usedAfter100, `bytes in use unchanged: ${usedAfter100} after 100 steps, ${usedEnd} after ${steps}`);
console.log(`time per step: ${((ms / steps) * 1000).toFixed(1)} us (${steps} steps in ${ms.toFixed(0)} ms)`);

if (failures > 0) {
  console.log(`${failures} failed`);
  process.exit(1);
}
console.log("all passed");
