import type { FirestoreLike } from "../src/firestore.js"

interface Entry { data: Record<string, unknown>; version: number }

class FakeRef {
  constructor(readonly path: string) {}
}

export const MAX_ATTEMPTS = 5

/**
 * In-memory Firestore with optimistic transactions: reads are recorded with the version they saw,
 * writes stay buffered until commit, and a commit whose read documents changed meanwhile reruns
 * the callback, up to MAX_ATTEMPTS. The Admin SDK uses pessimistic locks instead; outcomes are equivalent
 * for FirestoreStore because all of its reads come first.
 */
export class FakeFirestore implements FirestoreLike {
  private readonly docs = new Map<string, Entry>()
  private nextVersion = 1
  private hook: (() => Promise<void>) | null = null
  /** Callback invocations over all transactions, retries included. */
  attempts = 0
  /** Transactions that committed at least one write. */
  commits = 0
  /** The documents each finished transaction read and wrote, in order. */
  readonly log: { reads: string[]; writes: string[] }[] = []

  collection(name: string) {
    return {
      doc: (id: string) => {
        if (id === "" || id === "." || id === ".." || id.includes("/") || /^__.*__$/.test(id) || new TextEncoder().encode(id).length > 1500) {
          throw new Error(`fake firestore: invalid document id ${JSON.stringify(id)}`)
        }
        return new FakeRef(`${name}/${id}`)
      },
    }
  }

  /** Runs once, inside the next transaction attempt that has finished its callback and not yet validated. */
  interleave(hook: () => Promise<void>): void {
    this.hook = hook
  }

  raw(path: string): Record<string, unknown> | undefined {
    const e = this.docs.get(path)
    return e === undefined ? undefined : structuredClone(e.data)
  }

  rawSet(path: string, data: Record<string, unknown>): void {
    this.docs.set(path, { data: structuredClone(data), version: this.nextVersion++ })
  }

  async runTransaction<T>(fn: (tx: any) => Promise<T>, _opts?: { readOnly?: boolean }): Promise<T> {
    for (let attempt = 1; attempt <= MAX_ATTEMPTS; attempt++) {
      this.attempts++
      const reads = new Map<string, number>()
      const writes = new Map<string, Record<string, unknown>>()
      const tx = {
        get: async (ref: FakeRef) => {
          if (writes.size > 0) throw new Error("fake firestore: all reads must come before any write")
          const e = this.docs.get(ref.path)
          reads.set(ref.path, e?.version ?? 0)
          return { exists: e !== undefined, data: () => (e === undefined ? undefined : structuredClone(e.data)) }
        },
        set: (ref: FakeRef, data: Record<string, unknown>) => {
          writes.set(ref.path, structuredClone(data))
          return tx
        },
      }
      const result = await fn(tx)
      const hook = this.hook
      if (hook !== null) {
        this.hook = null
        await hook()
      }
      let stale = false
      for (const [path, seen] of reads) if ((this.docs.get(path)?.version ?? 0) !== seen) stale = true
      if (stale) continue
      for (const [path, data] of writes) this.docs.set(path, { data, version: this.nextVersion++ })
      if (writes.size > 0) this.commits++
      this.log.push({ reads: [...reads.keys()], writes: [...writes.keys()] })
      return result
    }
    throw new Error(`fake firestore: transaction aborted after ${MAX_ATTEMPTS} attempts`)
  }
}
