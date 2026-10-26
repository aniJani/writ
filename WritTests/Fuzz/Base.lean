import Writ
import WritSpec

open Writ

namespace WritTests.Fuzz

abbrev Gen := StateM UInt64

def mix (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- splitmix64. -/
def next : Gen UInt64 := modifyGet fun s => let s := s + 0x9e3779b97f4a7c15; (mix s, s)

def below (n : Nat) : Gen Nat := do
  let x ← next
  pure (if n == 0 then 0 else x.toNat % n)

def chance (pct : Nat) : Gen Bool := do pure ((← below 100) < pct)

def pick [Inhabited α] (xs : List α) : Gen α := do pure (xs.getD (← below xs.length) default)

def weighted [Inhabited α] (xs : List (Nat × α)) : Gen α := do
  let total := xs.foldl (· + ·.1) 0
  let r ← below total
  let rec go (r : Nat) : List (Nat × α) → α
    | [] => default
    | (w, x) :: rest => if r < w then x else go (r - w) rest
  pure (go r xs)

def subset (xs : List α) (pct : Nat) : Gen (List α) := xs.filterM fun _ => chance pct

def nonEmptySubset [Inhabited α] (xs : List α) (pct : Nat) : Gen (List α) := do
  let s ← subset xs pct
  if s.isEmpty then pure [← pick xs] else pure s

inductive Intent where | valid | staleSeq | timeBack | wrongVersion
  deriving DecidableEq, Repr, Inhabited

/-- How a generated `ledgerSync` alters the stored ledger before sending it. -/
inductive SyncMode where | store | older | clearTomb | foreignEntry | reorder | dropReservation | duplicateReservation
  deriving DecidableEq, Repr, Inhabited

/-- An event body for one lane (one live session at a time). The replayer fills seq, time, state
version and the ledgers of `sessionStart` and `ledgerSync`, so deleting steps keeps the rest
replayable. `oob` clears the stored tombstone out of band instead of sending an event. -/
structure GStep where
  lane : Nat := 0
  intent : Intent := .valid
  dt : Nat := 1
  body : EventBody
  sync : SyncMode := .store
  oob : Bool := false
  deriving Repr

structure GTrace where
  policy : Policy
  initLedger : Ledger := {}
  lanes : Nat := 1
  /-- Every store compares the ledger version, not only stores that write the ledger. -/
  strict : Bool := true
  /-- Odd lanes run their clock this many ms behind, so they see entries dated ahead of them. -/
  skew : Nat := 0
  steps : List GStep
  deriving Repr

def GTrace.length (g : GTrace) : Nat := g.steps.length

structure Lane where
  s : State
  n : Nat := 0
  inst : Nat
  dead : Bool := false

structure World where
  store : Ledger
  lanes : Array Lane
  nextInst : Nat
  clock : Nat := 0
  strict : Bool
  skew : Nat := 0

def World.init (g : GTrace) : World :=
  { store := g.initLedger, strict := g.strict, skew := g.skew, nextInst := max g.lanes 1
    lanes := (List.range (max g.lanes 1)).toArray.map fun i => { s := State.initial "pd", inst := i } }

def World.lane (w : World) (i : Nat) : Lane := w.lanes.getD (i % w.lanes.size) { s := State.initial "pd", inst := 0 }

def World.setLane (w : World) (i : Nat) (l : Lane) : World :=
  { w with lanes := w.lanes.set! (i % w.lanes.size) l }

def rolePool : List String := ["owner", "admin", "ops", "finance", "requester_manager"]
def digests : List String := ["d1", "d2", "d3"]
def permPool : List String := ["p0", "p1", "p2"]
def currencies : List String := ["USD", "EUR"]
def amounts : List Nat := [0, 1, 2, 3, 4, 5, 8, 13]

def startPool : List (String × ApproverInfo) :=
  [ ("alice", ⟨"alice", .human, ["owner"]⟩), ("bob", ⟨"bob", .human, ["admin"]⟩)
  , ("bot", ⟨"reviewer-bot", .automated, ["admin"]⟩), ("carol", ⟨"carol", .human, ["ops"]⟩)
  , ("alice2", ⟨"alice", .human, ["owner"]⟩), ("self", ⟨"u1", .human, ["owner", "admin"]⟩)
  , ("agentid", ⟨"agent", .human, ["owner"]⟩), ("dave", ⟨"dave", .human, ["admin", "ops"]⟩)
  , ("fin1", ⟨"fiona", .human, ["finance"]⟩), ("fin2", ⟨"felix", .human, ["finance", "admin"]⟩)
  , ("mgr", ⟨"maria", .human, ["requester_manager", "finance"]⟩) ]

def latePool : List (String × ApproverInfo) :=
  [ ("erin", ⟨"erin", .human, ["owner"]⟩), ("frank", ⟨"frank", .automated, ["ops"]⟩)
  , ("gina", ⟨"gina", .human, ["admin", "finance"]⟩) ]

instance : Inhabited ApproverInfo := ⟨⟨"nobody", .human, []⟩⟩
instance : Inhabited Mode := ⟨.enforce⟩
instance : Inhabited GrantScope := ⟨.session⟩
instance : Inhabited MeterScope := ⟨.session⟩
instance : Inhabited Outcome := ⟨.succeeded⟩
instance : Inhabited EscalationScope := ⟨.session⟩
instance : Inhabited SyncMode := ⟨.store⟩
instance : Inhabited Clause := ⟨⟨1, none, true, false⟩⟩
instance : Inhabited MeterSpec := ⟨{ unit := .calls }⟩
instance : Inhabited MeterUnit := ⟨.calls⟩
instance : Inhabited Requirements := ⟨{}⟩
instance : Inhabited GrantRec :=
  ⟨{ approver := "", principal := "", tool := "", digest := none, scope := .session, maxUses := 0, maxCost := none
     notBefore := none, expiresAt := none, epoch := 0, turn := 0, reviewedScopeDigest := "" }⟩

def currencyOf : MeterUnit → Option String
  | .money c => some c
  | .calls => none

def toolsOf (p : Policy) : List String := p.actions.map (·.1)

def reqOf (p : Policy) (tool : String) : Requirements := (Checks.reqOf p tool).getD {}

def callsWhere (s : State) (f : CallStatus → Bool) : List (String × CallRec) :=
  s.calls.toList.filter (f ·.2.status)

def pickApprover (s : State) : Gen String := do
  let ids := s.approvers.keys
  match ← weighted [(85, 0), (10, 1), (5, 2)] with
  | 0 => if ids.isEmpty then pure "alice" else pick ids
  | 1 => pure (← pick latePool).1
  | _ => pure "ghost"

def moneyCurrency (p : Policy) (r : Requirements) : Option String :=
  (r.meters.filterMap fun n => (Checks.meterOf p n).bind fun m => currencyOf m.unit).head?

def genCost (p : Policy) (r : Requirements) : Gen (Option Cost) := do
  let amt ← pick amounts
  match moneyCurrency p r with
  | some cur =>
    weighted [(80, some ⟨amt, cur⟩), (10, none), (10, some ⟨amt, if cur == "USD" then "EUR" else "USD"⟩)]
  | none =>
    if r.consentIfCostOver.isSome || (← chance 15) then do pure (some ⟨amt, ← pick currencies⟩)
    else pure none

def liveGrants (s : State) : List GrantRec :=
  s.grants.toList.filterMap fun (_, g) =>
    if !g.revoked && g.epoch == s.epoch && (g.scope != .turn || (s.turnActive && g.turn == s.turnIndex))
      && g.consumed + g.reserved < g.maxUses then some g else none

/-- A cost that fails step 8's shape check on an action with a money meter. -/
def badCost (p : Policy) (r : Requirements) : Gen (Option Cost) := do
  match moneyCurrency p r with
  | some cur => pick [none, some ⟨1, if cur == "USD" then "EUR" else "USD"⟩, some ⟨100, cur⟩]
  | none => genCost p r

def rawEligible (p : Policy) (s : State) (consent : Consent) (info : ApproverInfo) : Bool :=
  (Checks.clausesOf consent).any (Checks.eligibleFor p s.requester info ·)

/-- A retry's dt sometimes jumps past every meter window, so the reservation has left it. -/
def retryJump (p : Policy) : Nat := (p.meters.filterMap (·.2.windowMs)).foldl max 0 + 1

end WritTests.Fuzz
