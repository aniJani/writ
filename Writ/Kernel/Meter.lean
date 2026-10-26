import Writ.Core.State

namespace Writ

def MeterSpec.inWindowAt (spec : MeterSpec) (time now : Nat) : Bool :=
  match spec.windowMs with
  | some w => decide (time + w > now)
  | Option.none => true

def MeterSpec.inWindow (spec : MeterSpec) (e : MeterEntry) (now : Nat) : Bool := spec.inWindowAt e.time now

/-- The amount up to the reservation counts from the reservation's time and an overrun's excess
from its report, so a commit never moves spend into a window that did not check it. -/
def Meter.usage (spec : MeterSpec) (entries : List MeterEntry) (meter : String) (now : Nat) : Nat :=
  entries.foldl (init := 0) fun acc e =>
    if e.meter = meter then
      acc + (if spec.inWindow e now then e.amount else 0)
        + (if spec.inWindowAt e.excessAt now then e.excess else 0)
    else acc

def MeterSpec.amount (spec : MeterSpec) (cost : Option Cost) : Nat :=
  match spec.unit with
  | .money _ => (cost.map (·.amount)).getD 0
  | .calls => 1

def Policy.callAmount (p : Policy) (meter : String) (cost : Option Cost) : Nat :=
  ((p.meter? meter).map (·.amount cost)).getD 0

def Policy.isMoney (p : Policy) (meter : String) : Bool :=
  (p.meter? meter).any fun spec => spec.unit matches .money _

def State.meterEntries (p : Policy) (s : State) (meter : String) : List MeterEntry :=
  match (p.meter? meter).map (·.scope) with
  | some MeterScope.principal => s.ledger.entries
  | _ => s.sessionMeters

/-- A committed entry whose reserved part and excess part have both left the window. An entry
dated after `now` (another session's clock running ahead) has not left it. -/
def MeterSpec.expired (spec : MeterSpec) (e : MeterEntry) (now : Nat) : Bool :=
  e.committed && spec.windowMs.isSome && !spec.inWindow e now
    && (e.excess == 0 || !spec.inWindowAt e.excessAt now)

/-- An entry's meter prunes only when this policy defines it in `scope`: the principal ledger is
shared with sessions whose policy may define that meter name only in the other scope, or not at all. -/
def Policy.prune (p : Policy) (scope : MeterScope) (now : Nat) (es : List MeterEntry) :
    List MeterEntry :=
  es.filter fun e => !(p.meter? e.meter).any fun spec => spec.scope == scope && spec.expired e now

/-- Prunes the list only when `f` changes it: section 6 prunes only a list the step changes, and a
retime to the same time or a settle with no entry changes nothing. -/
def State.updateEntries (p : Policy) (s : State) (meter : String) (time : Nat)
    (f : List MeterEntry → List MeterEntry) : State :=
  let update (scope : MeterScope) (es : List MeterEntry) :=
    let es' := f es; if es' == es then es else p.prune scope time es'
  match (p.meter? meter).map (·.scope) with
  | some MeterScope.principal =>
    { s with ledger := { s.ledger with entries := update .principal s.ledger.entries
                                       version := s.ledger.version + 1 } }
  | _ => { s with sessionMeters := update .session s.sessionMeters }

def MeterEntry.isFor (e : MeterEntry) (meter session callId : String) : Bool :=
  e.meter == meter && e.session == session && e.call == callId

def State.entry? (p : Policy) (s : State) (meter callId : String) : Option MeterEntry :=
  (s.meterEntries p meter).find? (·.isFor meter s.sessionId callId)

def State.reserved (p : Policy) (s : State) (meter callId : String) : Nat :=
  ((s.entry? p meter callId).map (·.amount)).getD 0

/-- An unknown meter has no room, so a call never spends on a meter the policy does not define. -/
def State.hasRoom (p : Policy) (s : State) (time : Nat) (meter : String) (cost : Option Cost) : Bool :=
  match p.meter? meter with
  | Option.none => false
  | some spec => spec.cap.all (Meter.usage spec (s.meterEntries p meter) meter time + spec.amount cost ≤ ·)

/-- The meters on which a retry no longer holds a reservation inside the window. -/
def State.staleMeters (p : Policy) (s : State) (time : Nat) (meters : List String) (callId : String) :
    List String :=
  meters.filter fun m =>
    !((p.meter? m).any fun spec => (s.entry? p m callId).any (spec.inWindow · time))

def State.reserve (p : Policy) (s : State) (meter callId : String) (amount time : Nat) : State :=
  s.updateEntries p meter time (· ++ [{ meter, session := s.sessionId, call := callId, time, amount, committed := false }])

def State.retime (p : Policy) (s : State) (meter callId : String) (time : Nat) : State :=
  s.updateEntries p meter time (·.map fun e => if e.isFor meter s.sessionId callId then { e with time } else e)

def State.commit (p : Policy) (s : State) (meter callId : String) (amount time : Nat) : State :=
  s.updateEntries p meter time (·.map fun e =>
    if !e.isFor meter s.sessionId callId then e
    else if amount > e.amount then { e with excess := amount - e.amount, excessAt := time, committed := true }
    else { e with amount, committed := true })

def State.release (p : Policy) (s : State) (meter callId : String) (time : Nat) : State :=
  s.updateEntries p meter time (·.filter (!·.isFor meter s.sessionId callId))

/-- Releases every meter on `noEffect` or a `declined` outcome, else commits the actual cost (or the
reservation) on money meters and the reservation on calls meters. Returns the money meters whose
reservation the actual cost overran, in the order given; a release overruns nothing. -/
def State.settle (p : Policy) (s : State) (meters : List String) (callId : String) (outcome : Outcome)
    (actual : Option Nat) (noEffect : Bool) (time : Nat) : State × List String :=
  let release := noEffect || outcome == .declined
  meters.foldl (init := (s, [])) fun (acc, over) m =>
    let held := acc.reserved p m callId
    if release then (acc.release p m callId time, over)
    else if p.isMoney m then
      let amount := actual.getD held
      (acc.commit p m callId amount time, if amount > held then over ++ [m] else over)
    else (acc.commit p m callId held time, over)

end Writ
