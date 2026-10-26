export class WritInputError extends Error {
  readonly path: string
  constructor(message: string, path = "") {
    super(path === "" ? message : `${path}: ${message}`)
    this.name = "WritInputError"
    this.path = path
  }
}

export class WritKernelError extends Error {
  constructor(message: string, options?: ErrorOptions) {
    super(message, options)
    this.name = "WritKernelError"
  }
}

/** A commit kept losing to other writers, so the step was given up without an effect. */
export class WritConflictError extends Error {
  constructor(message: string) {
    super(message)
    this.name = "WritConflictError"
  }
}

/** A store refused a record it cannot hold, or found one it cannot read. */
export class WritStoreError extends Error {
  constructor(message: string) {
    super(message)
    this.name = "WritStoreError"
  }
}

/** A session's stored state has no room for the step: end the session and start a new one. */
export class WritStateFullError extends Error {
  readonly sessionId: string
  /** UTF-8 bytes of the state that did not fit. */
  readonly bytes: number
  /** The byte limit it is over. */
  readonly limit: number
  constructor(message: string, sessionId: string, bytes: number, limit: number) {
    super(message)
    this.name = "WritStateFullError"
    this.sessionId = sessionId
    this.bytes = bytes
    this.limit = limit
  }
}

/** A stored session was started under a policy this gate does not run, or runs only to settle and end. */
export class WritPolicyChangedError extends Error {
  readonly sessionId: string
  /** The digest of the policy the session was started under. */
  readonly policyDigest: string
  constructor(message: string, sessionId: string, policyDigest: string) {
    super(message)
    this.name = "WritPolicyChangedError"
    this.sessionId = sessionId
    this.policyDigest = policyDigest
  }
}
