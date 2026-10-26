export interface Stored { state: string; stateVersion: number; principal: string }

/** Version 0 is the empty ledger, which is never stored. */
export interface LedgerRecord { text: string; version: number }

/**
 * One atomic compare-and-swap over the session record and the principal's ledger record.
 * An expected version of null means the record must not exist yet. The ledger version is
 * checked on every commit, including one that writes no ledger.
 */
export interface Commit {
  sessionId: string
  state: string
  stateVersion: number
  expectedStateVersion: number | null
  principal: string
  ledger?: LedgerRecord
  expectedLedgerVersion: number | null
}

export type CommitOutcome = "ok" | "state_conflict" | "ledger_conflict"

/** A compare-and-swap over the principal's ledger record alone, to set or clear its tombstone without a session. */
export interface LedgerCommit {
  principal: string
  ledger: LedgerRecord
  expectedLedgerVersion: number | null
}

export interface Store {
  load(sessionId: string): Promise<Stored | null>
  loadLedger(principal: string): Promise<LedgerRecord | null>
  /** Writes nothing unless it returns "ok". */
  commit(c: Commit): Promise<CommitOutcome>
  /** Writes nothing unless it returns "ok"; atomic with `commit`. */
  commitLedger(c: LedgerCommit): Promise<"ok" | "ledger_conflict">
  /** The most UTF-8 bytes of session state the store can hold, when it has a limit. */
  readonly maxStateBytes?: number
}

export class MemoryStore implements Store {
  private readonly sessions = new Map<string, Stored>()
  private readonly ledgers = new Map<string, LedgerRecord>()

  async load(sessionId: string): Promise<Stored | null> {
    const s = this.sessions.get(sessionId)
    return s === undefined ? null : { ...s }
  }

  async loadLedger(principal: string): Promise<LedgerRecord | null> {
    const l = this.ledgers.get(principal)
    return l === undefined ? null : { ...l }
  }

  async commit(c: Commit): Promise<CommitOutcome> {
    if ((this.sessions.get(c.sessionId)?.stateVersion ?? null) !== c.expectedStateVersion) return "state_conflict"
    if ((this.ledgers.get(c.principal)?.version ?? null) !== c.expectedLedgerVersion) return "ledger_conflict"
    this.sessions.set(c.sessionId, { state: c.state, stateVersion: c.stateVersion, principal: c.principal })
    if (c.ledger !== undefined) this.ledgers.set(c.principal, { text: c.ledger.text, version: c.ledger.version })
    return "ok"
  }

  async commitLedger(c: LedgerCommit): Promise<"ok" | "ledger_conflict"> {
    if ((this.ledgers.get(c.principal)?.version ?? null) !== c.expectedLedgerVersion) return "ledger_conflict"
    this.ledgers.set(c.principal, { text: c.ledger.text, version: c.ledger.version })
    return "ok"
  }
}
