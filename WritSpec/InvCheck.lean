import Writ.Kernel.Meter
import Writ.Kernel.Grants
import Writ.Kernel.Failures

namespace Writ

namespace Inv

def distinct [BEq α] (l : List α) : Bool :=
  l.zipIdx.all fun (x, i) => !(l.take i).contains x

def authorizedOrLater : CallStatus → Bool
  | .authorized | .dispatched | .succeeded | .failed | .declined | .unknown => true
  | _ => false

def dispatchedOrLater : CallStatus → Bool
  | .dispatched | .succeeded | .failed | .declined | .unknown => true
  | _ => false

def reqs (p : Policy) (c : CallRec) : Requirements := (p.action? c.tool).getD {}

def epochOk (s : State) (c : CallRec) : Bool :=
  c.epoch ≤ s.epoch && (c.status.terminal || c.epoch == s.epoch)

/-- An enforced call past authorization was authorized by its tally or by a grant for its tool
whose creator is eligible for every clause of its consent. -/
def consentOk (p : Policy) (s : State) (c : CallRec) : Bool :=
  !authorizedOrLater c.status || p.modeOf c.tool != .enforce || c.shadow.isSome
    || c.consent.clauses.isEmpty || s.satisfied p c.consent c.tally
    || c.grant.any fun gid => (s.grants.get? gid).any fun g =>
      g.tool == c.tool && (s.eligibleAll p c.consent g.approver).isNone

def tallyOk (s : State) (c : CallRec) : Bool :=
  distinct (c.tally.map (·.1))
    && c.tally.all fun (who, a) => (s.approvers.get? a).any (·.principal == who)

def attemptsOk (p : Policy) (c : CallRec) : Bool :=
  let r := reqs p c
  if dispatchedOrLater c.status then
    1 ≤ c.attempts && c.attempts ≤ r.maxAttempts && (r.retryAfterUnknown || c.attempts == 1)
  else c.attempts == 0

def generationsOk (c : CallRec) : Bool :=
  c.generations.length == c.generation + 1
    && c.generations.head? == some (c.proposedDigest, c.proposedCost)
    && c.generations[c.generation]? == some (c.digest, c.cost)

def recordOk (c : CallRec) : Bool :=
  (!authorizedOrLater c.status || c.authorizedAt.isSome)
    && (c.reconciled.isNone || c.status == .unknown)

/-- Uses and cost are consumed at a call's first claim and reserved while it is authorized and
unclaimed, and calls never leave `s.calls`, so both counts are exact. -/
def grantOk (s : State) (gid : String) (g : GrantRec) : Bool :=
  let mine := s.calls.toList.filterMap fun (_, c) => if c.grant == some gid then some c else none
  let used := mine.filter (1 ≤ ·.attempts)
  let holders := mine.filter fun c => c.status == .authorized && c.attempts == 0
  let cost (cs : List CallRec) := (cs.map fun c => g.costHeld c.cost).foldl (· + ·) 0
  g.consumed == used.length && g.reserved == holders.length
    && g.costConsumed == cost used && g.costReserved == cost holders
    && g.consumed + g.reserved ≤ g.maxUses
    && g.maxCost.all fun m => g.costConsumed + g.costReserved ≤ m.amount

/-- An entry holds exactly the call's reservation until a report commits it; a commit keeps at
most the reservation in `amount` and puts an overrun in `excess`. -/
def entryOk (p : Policy) (s : State) (e : MeterEntry) : Bool :=
  match s.calls.get? e.call with
  | Option.none => false
  | some c =>
    let held := p.callAmount e.meter c.cost
    dispatchedOrLater c.status && e.meter ∈ (reqs p c).meters
      && (if e.committed then e.amount ≤ held && (e.excess == 0 || e.amount == held)
          else e.amount == held && e.excess == 0)

/-- Theorem 8: a call that may still run or settle holds one uncommitted entry on each meter of its
action, in the list its meter's scope names. -/
def heldOk (p : Policy) (s : State) (id : String) (c : CallRec) : Bool :=
  !(c.status == .dispatched || (c.status == .unknown && c.reconciled.isNone))
    || (reqs p c).meters.all fun m =>
      let es := (s.meterEntries p m).filter (·.isFor m s.sessionId id)
      es.length == 1 && es.all (!·.committed)

/-- Section 6, Meters: a declined report releases every meter of the call. A `no_effect` release
leaves no trace in the call record, so only declined calls are checked here. -/
def releasedOk (p : Policy) (s : State) (id : String) (c : CallRec) : Bool :=
  !(c.status == .declined || c.reconciled == some .declined)
    || (reqs p c).meters.all fun m => !(s.meterEntries p m).any (·.isFor m s.sessionId id)

def metersOk (p : Policy) (s : State) : Bool :=
  let mine := s.sessionMeters ++ s.ledger.entries.filter (·.session == s.sessionId)
  s.sessionMeters.all (·.session == s.sessionId) && mine.all (entryOk p s)
    && distinct (mine.map fun e => (e.meter, e.session, e.call)) && s.calls.all (heldOk p s)

/-- A kill or a tombstone cancels every pending call. -/
def haltedOk (s : State) : Bool :=
  !(s.killed || s.ledger.tombstone) || s.calls.all fun _ c => c.status != .awaiting && c.status != .authorized

/-- A dispatch after a kill is rejected before re-evaluation, so no call ever ends
`DeniedAtDispatch killed`. -/
def noKilledDispatchOk (s : State) : Bool := s.calls.all fun _ c => c.status != .deniedAtDispatch .killed

/-- A principal kill keeps the tombstone in the session's ledger until the session ends; an ended
session may take a ledger whose tombstone was cleared (section 6, Ledger), and nothing it holds may
then run again. -/
def killPersistsOk (p : Policy) (s : State) : Bool :=
  !(s.killed && p.killSetsTombstone) || s.ledger.tombstone
    || (s.ended && s.calls.all fun _ c => c.status != .awaiting && c.status != .authorized && c.status != .dispatched)

/-- Only the direction from counters to blocks holds: a success reported for a call in flight
resets its tool's counter while the block it raised stays until acknowledged. -/
def escalationOk (p : Policy) (s : State) : Bool :=
  let reached (limit : Option Nat) (n : Nat) := limit.any (n ≥ ·)
  s.failures.all (fun tool n => !reached p.limits.maxConsecutiveFailures n ||
      match p.limits.escalationScope with
      | .session => s.escalated
      | .tool => tool ∈ s.blockedTools)
    && (!reached p.limits.maxFailuresPerSession s.failuresThisSession || s.escalated)
    && (!s.anyBlocked || s.escalations ≥ 1)

def eachCall (f : CallRec → Bool) (s : State) : Bool := s.calls.all fun _ c => f c

def clauses : List (String × (Policy → State → Bool)) :=
  [ ("started", fun _ s => s.started || s.calls.isEmpty)
  , ("epoch", fun _ s => eachCall (epochOk s) s)
  , ("consent", fun p s => eachCall (consentOk p s) s)
  , ("tally", fun _ s => eachCall (tallyOk s) s)
  , ("attempts", fun p s => eachCall (attemptsOk p) s)
  , ("generations", fun _ s => eachCall generationsOk s)
  , ("record", fun _ s => eachCall recordOk s)
  , ("grants", fun _ s => s.grants.all (grantOk s))
  , ("meters", metersOk)
  , ("released", fun p s => s.calls.all (releasedOk p s))
  , ("halted", fun _ s => haltedOk s)
  , ("noKilledDispatch", fun _ s => noKilledDispatchOk s)
  , ("killPersists", killPersistsOk)
  , ("escalation", escalationOk) ]

/-- The names of the clauses `s` violates, for reporting a state the explorer reached. -/
def failing (p : Policy) (s : State) : List String :=
  (clauses.filter fun (_, f) => !f p s).map (·.1)

end Inv

def Inv.check (p : Policy) (s : State) : Bool := Inv.clauses.all fun (_, f) => f p s

end Writ
