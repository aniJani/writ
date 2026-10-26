import assert from "node:assert/strict"
import { test } from "node:test"
import type { Commit, LedgerCommit, Store } from "../src/index.js"

export const base = (over: Partial<Commit>): Commit => ({
  sessionId: "s1", state: "{}", stateVersion: 1, expectedStateVersion: null,
  principal: "u1", expectedLedgerVersion: null, ...over,
})

const ledgerOnly = (version: number, expectedLedgerVersion: number | null): LedgerCommit =>
  ({ principal: "u1", ledger: { text: `L${version}`, version }, expectedLedgerVersion })

export function storeSuite(label: string, make: () => Store | Promise<Store>): void {
  const t = (name: string, fn: () => Promise<void>) => test(`${label}: ${name}`, fn)
  t("a session is created only with expected version null", async () => {
    const store = await make()
    assert.equal(await store.commit(base({ expectedStateVersion: 0 })), "state_conflict")
    assert.equal(await store.load("s1"), null)
    assert.equal(await store.commit(base({ state: "a" })), "ok")
    assert.deepEqual(await store.load("s1"), { state: "a", stateVersion: 1, principal: "u1" })
    assert.equal(await store.commit(base({ state: "b" })), "state_conflict")
    assert.equal((await store.load("s1"))?.state, "a")
  })

  t("a stale state version is a conflict and the current one wins", async () => {
    const store = await make()
    await store.commit(base({ state: "a" }))
    assert.equal(await store.commit(base({ state: "b", stateVersion: 2, expectedStateVersion: 1 })), "ok")
    assert.equal(await store.commit(base({ state: "c", stateVersion: 2, expectedStateVersion: 1 })), "state_conflict")
    assert.deepEqual(await store.load("s1"), { state: "b", stateVersion: 2, principal: "u1" })
  })

  t("a ledger conflict writes neither record", async () => {
    const store = await make()
    assert.equal(await store.commit(base({ state: "a", ledger: { text: "L2", version: 2 } })), "ok")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L2", version: 2 })
    const stale = base({ state: "b", stateVersion: 2, expectedStateVersion: 1, ledger: { text: "L3", version: 3 }, expectedLedgerVersion: null })
    assert.equal(await store.commit(stale), "ledger_conflict")
    assert.equal(await store.commit({ ...stale, expectedLedgerVersion: 1 }), "ledger_conflict")
    assert.deepEqual(await store.load("s1"), { state: "a", stateVersion: 1, principal: "u1" })
    assert.deepEqual(await store.loadLedger("u1"), { text: "L2", version: 2 })
    assert.equal(await store.commit({ ...stale, expectedLedgerVersion: 2 }), "ok")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L3", version: 3 })
  })

  t("the ledger version is checked even when the commit does not write the ledger", async () => {
    const store = await make()
    await store.commit(base({ sessionId: "s0", ledger: { text: "L2", version: 2 } }))
    assert.equal(await store.commit(base({ state: "a" })), "ledger_conflict")
    assert.equal(await store.load("s1"), null)
    assert.equal(await store.commit(base({ state: "a", expectedLedgerVersion: 2 })), "ok")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L2", version: 2 })
  })

  t("a state conflict is reported before a ledger conflict and writes nothing", async () => {
    const store = await make()
    await store.commit(base({ state: "a", ledger: { text: "L2", version: 2 } }))
    assert.equal(await store.commit(base({ state: "b", stateVersion: 2, expectedStateVersion: 5, expectedLedgerVersion: 7 })), "state_conflict")
    assert.equal((await store.load("s1"))?.state, "a")
  })

  t("ledgers are kept per principal", async () => {
    const store = await make()
    await store.commit(base({ ledger: { text: "L1", version: 1 } }))
    await store.commit(base({ sessionId: "s2", principal: "u2" }))
    assert.equal(await store.loadLedger("u2"), null)
    assert.deepEqual(await store.loadLedger("u1"), { text: "L1", version: 1 })
  })

  t("loaded records are copies", async () => {
    const store = await make()
    await store.commit(base({ state: "a", ledger: { text: "L1", version: 1 } }))
    const s = await store.load("s1")
    const l = await store.loadLedger("u1")
    s!.stateVersion = 9
    l!.version = 9
    assert.equal((await store.load("s1"))?.stateVersion, 1)
    assert.equal((await store.loadLedger("u1"))?.version, 1)
  })

  t("commitLedger is a compare-and-swap on the ledger record alone", async () => {
    const store = await make()
    assert.equal(await store.commitLedger(ledgerOnly(1, 0)), "ledger_conflict")
    assert.equal(await store.loadLedger("u1"), null)
    assert.equal(await store.commitLedger(ledgerOnly(1, null)), "ok")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L1", version: 1 })
    assert.equal(await store.commitLedger(ledgerOnly(2, null)), "ledger_conflict")
    assert.equal(await store.commitLedger(ledgerOnly(2, 0)), "ledger_conflict")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L1", version: 1 })
    assert.equal(await store.commitLedger(ledgerOnly(2, 1)), "ok")
    assert.equal(await store.commitLedger(ledgerOnly(3, 1)), "ledger_conflict")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L2", version: 2 })
    assert.equal(await store.load("s1"), null)
    assert.equal(await store.loadLedger("u2"), null)
  })

  t("a session commit sees the version commitLedger wrote, and commitLedger leaves sessions alone", async () => {
    const store = await make()
    assert.equal(await store.commit(base({ state: "a", ledger: { text: "L1", version: 1 } })), "ok")
    assert.equal(await store.commitLedger(ledgerOnly(2, 1)), "ok")
    assert.deepEqual(await store.load("s1"), { state: "a", stateVersion: 1, principal: "u1" })
    const next = base({ state: "b", stateVersion: 2, expectedStateVersion: 1 })
    assert.equal(await store.commit({ ...next, expectedLedgerVersion: 1 }), "ledger_conflict")
    assert.equal(await store.commit({ ...next, expectedLedgerVersion: 2 }), "ok")
    assert.deepEqual(await store.loadLedger("u1"), { text: "L2", version: 2 })
  })
}
