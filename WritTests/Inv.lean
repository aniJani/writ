import WritTests.Witness
import WritTests.Control
import WritTests.Propose

open Writ WritTests.Witness

namespace WritTests.Inv

def ip : Policy := { wp with
  meters := wp.meters ++ [("pm", { unit := .calls, cap := some 5, scope := .principal })]
  actions := wp.actions ++
    [ ("multi", { maxAttempts := 3 })
    , ("mgcall", { consent := .perCall, meters := ["m"]
                   grantable := some { scope := .session, maxUses := 3 } })
    , ("both", { meters := ["m", "pm"] })
    , ("pretry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2
                   meters := ["m", "pm"] }) ] }

#guard ip.check.isEmpty

def iw (steps : List (Nat × EventBody)) (p : Policy := ip) : State × List Verdict × Bool := w steps p

def modGrant (s : State) (id : String) (f : GrantRec → GrantRec) : State :=
  match s.grants.get? id with
  | some g => { s with grants := s.grants.insert id (f g) }
  | Option.none => s

def mgc (id : String) : EventBody :=
  .grantCreate id "alice" "mgcall" (some "d1") .session 3 (usd 50) Option.none Option.none "rd"

def failFree : List (Nat × EventBody) :=
  [(2, pr "f" "free"), (3, dis "f"), (4, .result "f" .failed Option.none false)]

def lp (l : Limits) : Policy := { ip with limits := l }
def toolScope : Limits := { maxConsecutiveFailures := some 1, escalationScope := .tool }

def humanApproved := iw [(2, pr "c1" "human"), (3, appr "c1" "alice")]
def granted := iw [(2, gc "g1" "gcall"), (3, pr "c1" "gcall")]
def grantDispatched := iw [(2, gc "g1" "gcall"), (3, pr "c1" "gcall"), (4, dis "c1")]
def costGranted := iw [(2, mgc "g1"), (3, pr "c1" "mgcall" (usd 10)), (4, dis "c1" (cost := usd 10)),
  (5, pr "c2" "mgcall" (usd 15))]
def multiClaimed := iw [(2, pr "c1" "multi"), (3, dis "c1")]
def cancelledCall := iw [(2, pr "c1" "call"), (3, .cancel "c1")]
def approved := iw [(2, pr "c1" "call"), (3, appr "c1" "alice")]
def metered := iw [(2, pr "c1" "both" (usd 10)), (3, dis "c1" (cost := usd 10))]
def unknownMetered := iw [(2, pr "c1" "pretry" (usd 10)), (3, dis "c1" (cost := usd 10)),
  (4, .outcomeUnknown "c1")]
def sessionTotal := iw failFree (lp { maxFailuresPerSession := some 1 })
def sessionCounter := iw failFree (lp { maxConsecutiveFailures := some 1 })
def toolCounter := iw failFree (lp toolScope)
def killedTomb := iw [(2, .kill)] { ip with killSetsTombstone := true }

def forged : List (String × Policy × State) :=
  [ ("consent", ip, modCall humanApproved.1 "c1" ({ · with tally := [("reviewer-bot", "bot")] }))
  , ("consent", ip, modGrant (modCall granted.1 "c1" ({ · with grant := some "nope" })) "g1"
      ({ · with reserved := 0 }))
  , ("consent", ip, modGrant granted.1 "g1" ({ · with approver := "bot" }))
  , ("consent", ip, modGrant granted.1 "g1" ({ · with tool := "call" }))
  , ("grants", ip, modGrant grantDispatched.1 "g1" ({ · with consumed := 0 }))
  , ("grants", ip, modGrant costGranted.1 "g1" ({ · with costConsumed := 0 }))
  , ("attempts", ip, modCall multiClaimed.1 "c1" ({ · with attempts := 2 }))
  , ("attempts", ip, modCall cancelledCall.1 "c1" ({ · with attempts := 1 }))
  , ("halted", ip, { approved.1 with killed := true })
  , ("meters", ip, { metered.1 with sessionMeters := [] })
  , ("meters", ip, { metered.1 with ledger := { metered.1.ledger with entries := [] } })
  , ("meters", ip, { metered.1 with ledger := { metered.1.ledger with entries := [] }
                                    sessionMeters := metered.1.sessionMeters ++ metered.1.ledger.entries })
  , ("meters", ip, { unknownMetered.1 with sessionMeters := [] })
  , ("meters", ip, modCall metered.1 "c1" ({ · with tool := "metered" }))
  , ("record", ip, modCall approved.1 "c1" ({ · with authorizedAt := Option.none }))
  , ("record", ip, modCall multiClaimed.1 "c1" ({ · with authorizedAt := Option.none }))
  , ("record", ip, modCall multiClaimed.1 "c1" ({ · with reconciled := some .succeeded }))
  , ("escalation", lp { maxFailuresPerSession := some 1 }, { sessionTotal.1 with escalated := false })
  , ("escalation", lp { maxConsecutiveFailures := some 1 }, { sessionCounter.1 with escalated := false })
  , ("escalation", lp toolScope, { toolCounter.1 with blockedTools := [] })
  , ("escalation", lp toolScope, { toolCounter.1 with escalations := 0 })
  , ("generations", ip, modCall approved.1 "c1"
      ({ · with generations := [("d1", Option.none), ("d1", Option.none)] }))
  , ("killPersists", { ip with killSetsTombstone := true },
      { killedTomb.1 with ledger := { killedTomb.1.ledger with tombstone := false } }) ]

#guard [humanApproved, granted, grantDispatched, costGranted, multiClaimed, cancelledCall, approved,
  metered, unknownMetered, sessionTotal, sessionCounter, toolCounter, killedTomb].all (·.2.2)
#guard forged.all fun (_, p, s) => !Inv.check p s
#guard forged.all fun (n, p, s) => Inv.failing p s == [n]

#guard sessionTotal.1.escalated && sessionCounter.1.escalated && !toolCounter.1.escalated
#guard toolCounter.1.blockedTools == ["free"] && killedTomb.1.ledger.tombstone
#guard (costGranted.1.grants.get? "g1").map (fun g => (g.costConsumed, g.costReserved)) == some (10, 15)

def released := iw [(2, pr "c1" "pretry" (usd 10)), (3, dis "c1" (cost := usd 10)),
  (4, .outcomeUnknown "c1"), (5, .reconcile "c1" .succeeded Option.none true)]
#guard released.2.2 && released.1.sessionMeters.isEmpty && released.1.ledger.entries.isEmpty
def committed := iw [(2, pr "c1" "pretry" (usd 10)), (3, dis "c1" (cost := usd 10)),
  (4, .outcomeUnknown "c1"), (5, .reset), (6, .reconcile "c1" .failed (some 12) false)]
#guard committed.2.2 && committed.1.ledger.entries.length == 1
def retried := iw [(2, pr "c1" "pretry" (usd 10)), (3, dis "c1" (cost := usd 10)),
  (4, .outcomeUnknown "c1"), (5, dis "c1" 2 (cost := usd 10)), (6, .result "c1" .succeeded (some 4) false)]
#guard retried.2.2 && lastChecked retried == .ok .none Option.none
def costCycle := iw [(2, mgc "g1"), (3, pr "c1" "mgcall" (usd 10)), (4, pr "c2" "mgcall" (usd 20)),
  (5, .cancel "c2"), (6, dis "c1" (cost := usd 10)), (7, .result "c1" .succeeded Option.none true),
  (8, pr "c3" "mgcall" (usd 40)), (9, pr "c4" "mgcall" (usd 30)), (10, .reset)]
#guard costCycle.2.2 && lastChecked costCycle == .ok .none Option.none
#guard (costCycle.1.grants.get? "g1").map (fun g => (g.consumed, g.reserved, g.costConsumed))
  == some (1, 0, 10)
def inFlightSuccess (l : Limits) := iw [(2, pr "c1" "free"), (3, pr "c2" "free"), (4, dis "c1"),
  (5, dis "c2"), (6, .result "c1" .failed Option.none false), (7, .result "c2" .succeeded Option.none false)]
  (lp l)
#guard (inFlightSuccess { maxConsecutiveFailures := some 1 }).2.2
#guard (inFlightSuccess { maxConsecutiveFailures := some 1 }).1.escalated
#guard (inFlightSuccess toolScope).2.2
#guard (inFlightSuccess toolScope).1.blockedTools == ["free"]
def killAfterSync := iw [(2, pr "c1" "call"), (3, appr "c1" "alice"), (4, .kill), (5, .sessionEnd),
  (6, .ledgerSync { killedTomb.1.ledger with version := 5 })] { ip with killSetsTombstone := true }
#guard killAfterSync.2.2 && lastChecked killAfterSync == .ok .none Option.none

def cgo (b : List (Nat × EventBody)) (p : Policy := Control.cp) : State × List Verdict × Bool :=
  checkedScript p (Control.ctx ++ b)

#guard (cgo Control.flakyTwice Control.tp2).2.2
#guard (cgo (Control.flakyTwice ++ [(4, .escalationAck "alice" 1), (5, pr "c1" "flaky")]) Control.tp2).2.2
#guard (cgo (Control.failOf "a1" "a" 2 ++ Control.failOf "b1" "b" 3 ++ [(4, pr "c1" "free")])
  Control.tp2s).2.2
#guard (cgo (Control.failX ++ [(5, .escalationAck "alice" 2), (6, pr "z1" "z")]) Control.c4p).2.2
#guard (cgo ([(2, pr "c0" "free"), (2, dis "c0")] ++ Control.failA ++ Control.failA2 ++
  [(4, .result "c0" .failed Option.none false), (5, .escalationAck "alice" 2)])).2.2
#guard (cgo (Control.failA ++ Control.succB ++ Control.failA2 ++ [(4, pr "c1" "b")])).2.2
#guard (cgo [(2, pr "c1" "call"), (3, appr "c1" "alice"), (4, .kill), (5, pr "c2" "free")] Control.tp).2.2
#guard (cgo [(2, pr "c1" "retry"), (3, dis "c1"), (4, .outcomeUnknown "c1"), (5, dis "c1" 2),
  (6, .outcomeUnknown "c1"), (7, .reset), (8, .reconcile "c1" .declined Option.none true)]).2.2

def ppgo (b : List EventBody) : State × List Verdict × Bool :=
  checkedScript Propose.pp ([(0, start ["perm"] []), (1, .turnStart true)] ++ b.map (2, ·))

#guard (ppgo [Propose.prop "c1" "shadowCall", .dispatch "c1" 1 "d1" Option.none [] "k",
  Propose.prop "c2" "metered" (usd 30), .dispatch "c2" 1 "d1" (usd 30) [] "k",
  .result "c2" .succeeded (some 50) false, Propose.prop "c3" "shadowPerm"]).2.2

end WritTests.Inv
