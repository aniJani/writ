import { WritStoreError } from "./errors.js"
import type { Commit, CommitOutcome, LedgerCommit, LedgerRecord, Store, Stored } from "./store.js"

/**
 * The subset of the Firestore server API that `FirestoreStore` uses. It was type-checked against
 * the `Firestore` of `@google-cloud/firestore` 9.3.1.
 */
export interface FirestoreLike {
  collection(name: string): { doc(id: string): object }
  runTransaction<T>(fn: (tx: TransactionLike) => Promise<T>, opts?: { readOnly?: boolean }): Promise<T>
}

export interface TransactionLike {
  get(ref: any): Promise<{ exists: boolean; data(): any }>
  set(ref: any, data: Record<string, unknown>): unknown
}

export interface FirestoreStoreOptions {
  /** Collection of session documents. Defaults to `writ_sessions`. */
  sessions?: string
  /** Collection of principal ledger documents. Defaults to `writ_ledgers`. */
  ledgers?: string
}

/** Firestore documents are limited to 1 MiB; this leaves room for the other fields and indexes. */
export const MAX_TEXT_BYTES = 900_000

const utf8 = new TextEncoder()

/**
 * The Firestore document id `FirestoreStore` uses for a session id or a principal. Hosts that read,
 * clear or pre-seed these documents directly must address them with it.
 *
 * `encodeURIComponent`, then "." becomes "%2E" and "_" becomes "%5F", so the result never contains
 * "/", is never "." or "..", never looks like "__name__", and distinct ids stay distinct. The 1500
 * byte limit applies to the encoded form. An empty id or one with a lone surrogate throws `WritStoreError`.
 */
export function firestoreDocId(id: string): string {
  if (id === "") throw new WritStoreError("an empty id cannot be a Firestore document id")
  let enc: string
  try {
    enc = encodeURIComponent(id)
  } catch {
    throw new WritStoreError("an id with a lone surrogate cannot be a Firestore document id")
  }
  enc = enc.replaceAll(".", "%2E").replaceAll("_", "%5F")
  if (utf8.encode(enc).length > 1500) throw new WritStoreError("an id whose encoded form is longer than 1500 bytes cannot be a Firestore document id")
  return enc
}

function checkSize(what: string, text: string): void {
  const bytes = utf8.encode(text).length
  if (bytes > MAX_TEXT_BYTES) {
    throw new WritStoreError(`${what} is ${bytes} bytes, over the ${MAX_TEXT_BYTES} byte limit for one Firestore document (1 MiB)`)
  }
}

function sessionOf(id: string, d: any): Stored {
  if (typeof d?.state !== "string" || !Number.isSafeInteger(d.state_version) || typeof d.principal !== "string") {
    throw new WritStoreError(`session document ${id} is malformed`)
  }
  return { state: d.state, stateVersion: d.state_version, principal: d.principal }
}

function ledgerOf(id: string, d: any): LedgerRecord {
  if (typeof d?.ledger !== "string" || !Number.isSafeInteger(d.version)) {
    throw new WritStoreError(`ledger document ${id} is malformed`)
  }
  return { text: d.ledger, version: d.version }
}

/**
 * Layout, one transaction per commit (`commitLedger` reads and writes only the ledger document):
 * - `<sessions>/<firestoreDocId(sessionId)>`: `{ state: string, state_version: number, principal: string, updated_at: number }`.
 *   `state` is the canonical state text, stored as a string. `updated_at` is `Date.now()` at commit and is never read back.
 * - `<ledgers>/<firestoreDocId(principal)>`: `{ ledger: string, version: number }`.
 *
 * Collections default to `writ_sessions` and `writ_ledgers` and must differ. Ids are encoded by `firestoreDocId`.
 * State and ledger text over 900000 UTF-8 bytes are refused with `WritStoreError`.
 */
export class FirestoreStore implements Store {
  readonly maxStateBytes = MAX_TEXT_BYTES
  private readonly sessions: string
  private readonly ledgers: string

  constructor(private readonly db: FirestoreLike, opts: FirestoreStoreOptions = {}) {
    this.sessions = opts.sessions ?? "writ_sessions"
    this.ledgers = opts.ledgers ?? "writ_ledgers"
    if (this.sessions === this.ledgers) throw new WritStoreError(`sessions and ledgers must be different collections, both are "${this.sessions}"`)
  }

  private sessionRef(id: string) { return this.db.collection(this.sessions).doc(firestoreDocId(id)) }
  private ledgerRef(principal: string) { return this.db.collection(this.ledgers).doc(firestoreDocId(principal)) }

  async load(sessionId: string): Promise<Stored | null> {
    const ref = this.sessionRef(sessionId)
    return this.db.runTransaction(async (tx) => {
      const snap = await tx.get(ref)
      return snap.exists ? sessionOf(sessionId, snap.data()) : null
    }, { readOnly: true })
  }

  async loadLedger(principal: string): Promise<LedgerRecord | null> {
    const ref = this.ledgerRef(principal)
    return this.db.runTransaction(async (tx) => {
      const snap = await tx.get(ref)
      return snap.exists ? ledgerOf(principal, snap.data()) : null
    }, { readOnly: true })
  }

  async commit(c: Commit): Promise<CommitOutcome> {
    checkSize("state", c.state)
    if (c.ledger !== undefined) checkSize("ledger", c.ledger.text)
    const sessionRef = this.sessionRef(c.sessionId)
    const ledgerRef = this.ledgerRef(c.principal)
    const updatedAt = Date.now()
    // Firestore reruns this callback when a document it read changed, so it keeps no state outside itself.
    return this.db.runTransaction(async (tx): Promise<CommitOutcome> => {
      const [session, ledger] = [await tx.get(sessionRef), await tx.get(ledgerRef)]
      const stateVersion = session.exists ? sessionOf(c.sessionId, session.data()).stateVersion : null
      if (stateVersion !== c.expectedStateVersion) return "state_conflict"
      const ledgerVersion = ledger.exists ? ledgerOf(c.principal, ledger.data()).version : null
      if (ledgerVersion !== c.expectedLedgerVersion) return "ledger_conflict"
      tx.set(sessionRef, { state: c.state, state_version: c.stateVersion, principal: c.principal, updated_at: updatedAt })
      if (c.ledger !== undefined) tx.set(ledgerRef, { ledger: c.ledger.text, version: c.ledger.version })
      return "ok"
    })
  }

  async commitLedger(c: LedgerCommit): Promise<"ok" | "ledger_conflict"> {
    checkSize("ledger", c.ledger.text)
    const ledgerRef = this.ledgerRef(c.principal)
    return this.db.runTransaction(async (tx): Promise<"ok" | "ledger_conflict"> => {
      const ledger = await tx.get(ledgerRef)
      const ledgerVersion = ledger.exists ? ledgerOf(c.principal, ledger.data()).version : null
      if (ledgerVersion !== c.expectedLedgerVersion) return "ledger_conflict"
      tx.set(ledgerRef, { ledger: c.ledger.text, version: c.ledger.version })
      return "ok"
    })
  }
}
