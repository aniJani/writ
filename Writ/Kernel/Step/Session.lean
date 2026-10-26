import Writ.Kernel.Calls

namespace Writ

def handleSessionStart (s : State) (sessionId policyDigest requester : String)
    (permissions : List String) (approvers : List (String × ApproverInfo))
    (ledger : Ledger) : State × Verdict :=
  if policyDigest ≠ s.expectedPolicyDigest then (s, .rejected .policyDigestMismatch)
  -- Meter entries are keyed by session id, so a reused id would let this session release or
  -- overwrite an earlier session's spend.
  else if ledger.entries.any (·.session == sessionId) then (s, .rejected .alreadyStarted)
  else
    ({ s with
        started := true, sessionId, requester, permissions, ledger
        approvers := s.approvers.insertMany approvers },
     .ok .none Option.none)

def State.interrupt (s : State) : State :=
  let s := cancelPending s
  { s with
      calls := s.calls.map fun _ c =>
        if c.status = .dispatched then { c with status := .unknown } else c
      grants := s.grants.map fun _ g => { g with revoked := true } }

def handleSessionEnd (s : State) : State × Verdict :=
  ({ s.interrupt with ended := true }, .ok .none Option.none)

/-- A tombstone that arrives here leaves `killed` unset: this session was not killed, and the
tombstone alone already puts it under the kill check. -/
def handleLedgerSync (s : State) (ledger : Ledger) : State × Verdict :=
  let own (l : Ledger) := l.entries.filter (·.session == s.sessionId)
  let mine := own s.ledger
  let stored := own ledger
  -- Another session may prune this session's committed entries, but never its reservations.
  let fits := stored.all (fun x => stored.count x ≤ mine.count x) &&
    (mine.filter (!stored.contains ·)).all (·.committed)
  -- An ended session takes only reconcile and ledger_sync, so a cleared tombstone reopens nothing
  -- there, and accepting it lets the late reconcile commit.
  let clears := s.ledger.tombstone && !ledger.tombstone && !s.ended
  if ledger.version < s.ledger.version || !fits || clears then
    (s, .rejected .ledgerConflict)
  else
    let s' := if ledger.tombstone && !s.ledger.tombstone then cancelPending s else s
    ({ s' with ledger }, .ok .none Option.none)

def handleTurnStart (s : State) (userInitiated : Bool) : State × Verdict :=
  if s.turnActive then (s, .rejected .turnState)
  else
    ({ s with
        turnActive := true, turnIndex := s.turnIndex + 1
        stepsThisTurn := 0, proposalsThisTurn := 0, approvalsThisTurn := 0
        rejectedMemory := if userInitiated then [] else s.rejectedMemory },
     .ok .none Option.none)

def handleTurnEnd (s : State) : State × Verdict :=
  if !s.turnActive then (s, .rejected .turnState)
  else
    let grants := s.grants.map fun _ g =>
      if g.scope = .turn ∧ g.turn = s.turnIndex then { g with revoked := true } else g
    ({ s with turnActive := false, grants }, .ok .none Option.none)

def handleStepStart (p : Policy) (s : State) : State × Verdict :=
  let over := match p.limits.maxStepsPerTurn with
    | some n => decide (s.stepsThisTurn ≥ n)
    | Option.none => false
  let s' := { s with stepsThisTurn := s.stepsThisTurn + 1 }
  if !over then (s', .ok .none Option.none)
  else match p.mode with
    | .enforce => (s, .rejected .stepLimit)
    | .logOnly => (s', .ok .none (some (.wouldDeny .stepLimit)))

-- Tallies were counted against the attested principal, kind and roles, so an id is immutable once
-- attested; otherwise one id could count twice or pass a humanOnly quorum retroactively.
def handleApproverAttest (s : State) (approver : String) (info : ApproverInfo) : State × Verdict :=
  if (s.approvers.get? approver).any (· != info) then (s, .rejected .approverChanged)
  else ({ s with approvers := s.approvers.insert approver info }, .ok .none Option.none)

def handlePermissionRevoke (s : State) (permission : String) : State × Verdict :=
  ({ s with permissions := s.permissions.filter (· ≠ permission) }, .ok .none Option.none)

end Writ
