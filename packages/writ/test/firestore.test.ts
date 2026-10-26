import assert from "node:assert/strict"
import { test } from "node:test"
import { createGate, WritStoreError } from "../src/index.js"
import type { Store } from "../src/index.js"
import { FirestoreStore, firestoreDocId, MAX_TEXT_BYTES } from "../src/firestore.js"
import type { FirestoreLike } from "../src/firestore.js"
import { FakeFirestore, MAX_ATTEMPTS } from "./fake-firestore.js"
import { base, storeSuite } from "./store-suite.js"
import { callsPolicy, gateSuite, kernel } from "./gate-suite.js"

storeSuite("FirestoreStore (fake)", () => new FirestoreStore(new FakeFirestore()))
gateSuite("FirestoreStore (fake)", () => new FirestoreStore(new FakeFirestore()))

test("the fake hides writes until commit and retries when a read document changed", async () => {
  const db = new FakeFirestore()
  const ref = db.collection("c").doc("d")
  const other = db.collection("c").doc("e")
  db.rawSet("c/d", { n: 1 })
  let runs = 0
  db.interleave(async () => {
    await db.runTransaction(async (tx) => { tx.set(ref, { n: 2 }) })
  })
  const seen = await db.runTransaction(async (tx) => {
    runs++
    const snap = await tx.get(ref)
    tx.set(other, { from: runs })
    assert.equal(db.raw("c/e"), undefined)
    return snap.data()
  })
  assert.equal(runs, 2)
  assert.deepEqual(seen, { n: 2 })
  assert.deepEqual(db.raw("c/e"), { from: 2 })
})

test("the fake does not retry for a document the transaction never read, and aborts after the bound", async () => {
  const db = new FakeFirestore()
  const ref = db.collection("c").doc("d")
  let runs = 0
  db.interleave(async () => { db.rawSet("c/unread", { n: 1 }) })
  await db.runTransaction(async (tx) => { runs++; await tx.get(ref); tx.set(ref, { n: 1 }) })
  assert.equal(runs, 1)
  let tries = 0
  await assert.rejects(db.runTransaction(async (tx) => {
    tries++
    await tx.get(ref)
    db.rawSet("c/d", { n: tries })
  }), /aborted/)
  assert.equal(tries, MAX_ATTEMPTS)
})

test("two overlapping commits: exactly one wins and the loser reruns against the winner", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  db.interleave(async () => {
    assert.equal(await store.commit(base({ state: "b" })), "ok")
  })
  assert.equal(await store.commit(base({ state: "a" })), "state_conflict")
  assert.equal(db.attempts, 3)
  assert.equal((await store.load("s1"))?.state, "b")
})

test("an overlapping ledger writer is a ledger conflict and the loser writes nothing", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  await store.commit(base({ sessionId: "s0", ledger: { text: "L1", version: 1 } }))
  db.interleave(async () => {
    assert.equal(await store.commit(base({ sessionId: "s2", expectedLedgerVersion: 1, ledger: { text: "L2", version: 2 } })), "ok")
  })
  const out = await store.commit(base({ state: "x", expectedLedgerVersion: 1, ledger: { text: "Lx", version: 2 } }))
  assert.equal(out, "ledger_conflict")
  assert.equal(await store.load("s1"), null)
  assert.deepEqual(await store.loadLedger("u1"), { text: "L2", version: 2 })
})

test("commitLedger is one transaction that reads and writes the ledger document only", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  await store.commit(base({ ledger: { text: "L1", version: 1 } }))
  db.log.length = 0
  assert.equal(await store.commitLedger({ principal: "u1", ledger: { text: "L2", version: 2 }, expectedLedgerVersion: 1 }), "ok")
  assert.deepEqual(db.log, [{ reads: ["writ_ledgers/u1"], writes: ["writ_ledgers/u1"] }])
  assert.deepEqual(db.raw("writ_ledgers/u1"), { ledger: "L2", version: 2 })
})

test("commitLedger reruns only for a ledger writer, and then conflicts and writes nothing", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  await store.commit(base({ ledger: { text: "L1", version: 1 } }))
  db.interleave(async () => {
    assert.equal(await store.commit(base({ state: "b", stateVersion: 2, expectedStateVersion: 1, expectedLedgerVersion: 1 })), "ok")
  })
  let attempts = db.attempts
  assert.equal(await store.commitLedger({ principal: "u1", ledger: { text: "L2", version: 2 }, expectedLedgerVersion: 1 }), "ok")
  // The commitLedger attempt and the interleaved commit, with no rerun.
  assert.equal(db.attempts - attempts, 2)
  db.interleave(async () => {
    assert.equal(await store.commit(base({ sessionId: "s2", expectedLedgerVersion: 2, ledger: { text: "L3", version: 3 } })), "ok")
  })
  attempts = db.attempts
  assert.equal(await store.commitLedger({ principal: "u1", ledger: { text: "Lx", version: 3 }, expectedLedgerVersion: 2 }), "ledger_conflict")
  assert.equal(db.attempts - attempts, 3)
  assert.deepEqual(await store.loadLedger("u1"), { text: "L3", version: 3 })
})

test("commitLedger refuses a ledger over 900000 UTF-8 bytes, and the store's state budget is the same limit", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  await assert.rejects(store.commitLedger({ principal: "u1", ledger: { text: "x".repeat(MAX_TEXT_BYTES + 1), version: 1 }, expectedLedgerVersion: null }), WritStoreError)
  assert.equal(await store.loadLedger("u1"), null)
  assert.equal(store.maxStateBytes, MAX_TEXT_BYTES)
})

test("documents use the layout state, state_version, principal, updated_at and ledger, version", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db, { sessions: "ss", ledgers: "ll" })
  const before = Date.now()
  await store.commit(base({ state: "{\"k\":1}", ledger: { text: "L1", version: 1 } }))
  const s = db.raw("ss/s1")!
  assert.deepEqual(Object.keys(s).sort(), ["principal", "state", "state_version", "updated_at"])
  assert.equal(s["state"], "{\"k\":1}")
  assert.equal(s["state_version"], 1)
  assert.equal(s["principal"], "u1")
  assert.ok((s["updated_at"] as number) >= before)
  assert.deepEqual(db.raw("ll/u1"), { ledger: "L1", version: 1 })
})

test("default collection names", async () => {
  const db = new FakeFirestore()
  await new FirestoreStore(db).commit(base({ ledger: { text: "L1", version: 1 } }))
  assert.ok(db.raw("writ_sessions/s1") !== undefined)
  assert.ok(db.raw("writ_ledgers/u1") !== undefined)
})

test("ids that Firestore would refuse as document ids are encoded, distinct and round-trip", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  const ids = ["a/b", "a%2Fb", ".", "..", "__x__", "é", "a b"]
  for (const id of ids) await store.commit(base({ sessionId: id, principal: id, state: id }))
  for (const id of ids) assert.equal((await store.load(id))?.state, id)
  await assert.rejects(store.commit(base({ sessionId: "" })), WritStoreError)
  await assert.rejects(store.load("\ud800"), WritStoreError)
})

test("firestoreDocId is the id the store uses, and the fake refuses raw ids", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  assert.equal(firestoreDocId("user_1.a/b"), "user%5F1%2Ea%2Fb")
  await store.commit(base({ sessionId: "user_1", principal: "a/b", ledger: { text: "L", version: 1 } }))
  assert.ok(db.raw(`writ_sessions/${firestoreDocId("user_1")}`) !== undefined)
  assert.ok(db.raw(`writ_ledgers/${firestoreDocId("a/b")}`) !== undefined)
  assert.throws(() => db.collection("c").doc("a/b"), /invalid document id/)
  assert.throws(() => db.collection("c").doc("__x__"), /invalid document id/)
  assert.throws(() => firestoreDocId("é".repeat(400)), /encoded form is longer than 1500 bytes/)
})

test("equal collection names are refused", () => {
  assert.throws(() => new FirestoreStore(new FakeFirestore(), { sessions: "x", ledgers: "x" }), WritStoreError)
})

test("a state above 900000 UTF-8 bytes throws WritStoreError and writes nothing", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  const limit = 900_000
  assert.equal(await store.commit(base({ state: "x".repeat(limit) })), "ok")
  // 300000 three-byte characters are 900000 bytes in 300000 UTF-16 units.
  assert.equal(await store.commit(base({ sessionId: "s2", state: "€".repeat(limit / 3) })), "ok")
  const over = "€".repeat(limit / 3 + 1)
  assert.ok(over.length < limit)
  await assert.rejects(store.commit(base({ sessionId: "s3", state: over })), (e: unknown) => e instanceof WritStoreError && /900000/.test(e.message))
  await assert.rejects(store.commit(base({ sessionId: "s4", state: "x".repeat(limit + 1) })), WritStoreError)
  await assert.rejects(store.commit(base({ sessionId: "s5", ledger: { text: "x".repeat(limit + 1), version: 1 } })), WritStoreError)
  assert.equal(await store.load("s3"), null)
  assert.equal(await store.load("s4"), null)
  assert.equal(await store.load("s5"), null)
})

test("a malformed stored document is an error, not a state", async () => {
  const db = new FakeFirestore()
  const store = new FirestoreStore(db)
  db.rawSet("writ_sessions/s1", { state: 5, state_version: 1, principal: "u1" })
  await assert.rejects(store.load("s1"), WritStoreError)
  db.rawSet("writ_ledgers/u1", { ledger: "L", version: "1" })
  await assert.rejects(store.loadLedger("u1"), WritStoreError)
  await assert.rejects(store.commit(base({ state: "a", expectedStateVersion: 1 })), WritStoreError)
})

test("a transaction that keeps aborting surfaces the Firestore error unchanged", async () => {
  const boom = new Error("deadline")
  const db: FirestoreLike = { collection: () => ({ doc: () => ({}) }), runTransaction: async () => { throw boom } }
  await assert.rejects(new FirestoreStore(db).commit(base({})), (e) => e === boom)
})

test("two gates overlapping inside Firestore's own transaction claim a dispatch once", async () => {
  const db = new FakeFirestore()
  const store: Store = new FirestoreStore(db)
  let t = 1000
  const mk = () => createGate({ kernel, policyText: callsPolicy, store, clock: () => (t += 10) })
  const a = mk()
  const b = mk()
  await a.start({ sessionId: "s1", requester: "u1", permissions: [], approvers: {}, userInitiated: true })
  await a.propose("s1", { callId: "c1", tool: "ping", callDigest: "d" })
  const dispatch = { callId: "c1", attempt: 1, callDigest: "d", idempotencyKey: "k" }
  let rb: Awaited<ReturnType<typeof b.dispatch>> | undefined
  db.interleave(async () => { rb = await b.dispatch("s1", dispatch) })
  const ra = await a.dispatch("s1", dispatch)
  const claimed = (v: { verdict: string; decision?: string }) => v.verdict === "accepted" && v.decision === "dispatch_claimed"
  assert.equal(claimed(rb!.verdict as never), true)
  assert.equal(claimed(ra.verdict as never), false)
  const s = JSON.parse((await store.load("s1"))!.state)
  assert.equal(s.calls.c1.attempts, 1)
  assert.notEqual(s.ended, true)
})

type EmulatorDb = FirestoreLike & { terminate?: () => Promise<void> }

async function emulator(): Promise<EmulatorDb | string> {
  const host = process.env["FIRESTORE_EMULATOR_HOST"]
  if (host === undefined || host === "") return "FIRESTORE_EMULATOR_HOST is not set"
  try {
    const name = "@google-cloud/firestore"
    const mod = await import(name) as { Firestore: new (o: { projectId: string }) => EmulatorDb }
    return new mod.Firestore({ projectId: "demo-writ" })
  } catch (e) {
    if ((e as { code?: string }).code === "ERR_MODULE_NOT_FOUND") return "@google-cloud/firestore is not installed"
    throw e
  }
}

const emu = await emulator()
if (typeof emu === "string") {
  test("emulator", { skip: `skipped: ${emu}` }, () => {})
} else {
  const run = Date.now().toString(36)
  let n = 0
  const fresh = () => new FirestoreStore(emu, { sessions: `writ_test_${run}_${n++}_s`, ledgers: `writ_test_${run}_${n}_l` })
  storeSuite("FirestoreStore (emulator)", fresh)
  gateSuite("FirestoreStore (emulator)", fresh)
  test("emulator: close", async () => { await emu.terminate?.() })
}
