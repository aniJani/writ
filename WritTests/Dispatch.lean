import WritTests.Fixtures

open Writ

namespace WritTests.Dispatch

def dp : Policy where
  approverRoles := ["owner"]
  meters :=
    [ ("m", { unit := .money "USD", cap := some 100 })
    , ("pm", { unit := .money "USD", cap := some 100, scope := .principal })
    , ("wm", { unit := .money "USD", cap := some 100, windowMs := some 1000 }) ]
  actions :=
    [ ("free", {}), ("call", { consent := .perCall }), ("metered", { meters := ["m"] })
    , ("pmetered", { meters := ["pm"] }), ("wmetered", { meters := ["wm"] })
    , ("needsPerm", { permission := some "perm" }), ("guarded", { guards := ["g"] })
    , ("retry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2
                  meters := ["m"] })
    , ("once", { meters := ["m"] })
    , ("gcall", { consent := .perCall, grantable := some { scope := .session, maxUses := 3 } })
    , ("shadowPerm", { permission := some "perm", mode := some .logOnly })
    , ("shadowMetered", { meters := ["m"], mode := some .logOnly }) ]

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩

def pr (id tool : String) (cost : Option Cost := Option.none) (g : List (String × Bool) := []) :
    EventBody :=
  .propose id tool "d1" cost g []

def dis (id : String) (n : Nat := 1) (d : String := "d1") (cost : Option Cost := Option.none)
    (g : List (String × Bool) := []) (key : String := "k1") : EventBody :=
  .dispatch id n d cost g key

def ctx : List (Nat × EventBody) := [(0, start ["perm"] [("alice", alice)]), (1, .turnStart true)]
def go (b : List (Nat × EventBody)) (p : Policy := dp) : State × List Verdict := script p (ctx ++ b)
def statusOf (r : State × List Verdict) (id : String) : Option CallStatus :=
  (r.1.calls.get? id).map (·.status)
def claimed : Verdict := .ok .dispatchClaimed Option.none
def okNone : Verdict := .ok .none Option.none
def usage (r : State × List Verdict) (m : String := "m") (now : Nat := 10) : Nat :=
  match dp.meter? m with
  | some spec => Meter.usage spec (r.1.meterEntries dp m) m now
  | Option.none => 0

#guard last (go [(2, pr "c1" "free"), (3, dis "c1")]) == claimed
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, dis "c1")]) == .rejected .callDispatched
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, dis "c1" 2)]) == .rejected .callDispatched
#guard last (go [(2, dis "c1")]) == .rejected .unknownCall
#guard last (go [(2, pr "c1" "call"), (3, dis "c1")]) == .rejected .callAwaiting
#guard last (go [(2, pr "c1" "free"), (3, dis "c1" (d := "d2"))]) == .rejected .digestMismatch
#guard last (go [(2, pr "c1" "free"), (3, dis "c1" 2)]) == .rejected .attemptOrder
#guard last (go [(2, pr "c1" "metered" (usd 5)), (3, dis "c1" (cost := usd 6))])
        == .rejected .costMismatch
#guard ((go [(2, pr "c1" "free"), (3, dis "c1")]).1.calls.get? "c1").map
        (fun c => (c.attempts, c.idempotencyKey)) == some (1, some "k1")

def cancelled := go [(2, pr "c1" "free"), (3, dis "c1"), (4, .cancel "c1")]
#guard last cancelled == .rejected .callDispatched
#guard statusOf cancelled "c1" == some .dispatched
#guard last (go [(2, pr "c1" "free"), (3, .cancel "c1")]) == okNone
#guard statusOf (go [(2, pr "c1" "free"), (3, .cancel "c1")]) "c1" == some .cancelled
#guard statusOf (go [(2, pr "c1" "call"), (3, .cancel "c1")]) "c1" == some .cancelled
#guard last (go [(2, .cancel "c1")]) == .rejected .unknownCall
#guard last (go [(2, pr "c1" "free"), (3, .cancel "c1"), (4, dis "c1")]) == .rejected .callEnded

def two : List (Nat × EventBody) :=
  [(2, pr "c1" "metered" (usd 60)), (3, pr "c2" "metered" (usd 60)), (4, dis "c1" (cost := usd 60))]
#guard (go two).2.getLast? == some claimed
#guard last (go (two ++ [(5, dis "c2" (cost := usd 60))])) == .rejected .meterExceeded
#guard statusOf (go (two ++ [(5, dis "c2" (cost := usd 60))])) "c2" == some .authorized
#guard last (go (two ++ [(5, .result "c1" .failed Option.none true), (6, dis "c2" (cost := usd 60))]))
        == claimed
#guard usage (go (two ++ [(5, .result "c1" .failed Option.none true)])) == 0
#guard usage (go (two ++ [(5, .result "c1" .failed Option.none false)])) == 60
#guard statusOf (go (two ++ [(5, .result "c1" .failed Option.none false)])) "c1" == some .failed
#guard last (go [(2, pr "c1" "metered" (usd 40)), (3, pr "c2" "metered" (usd 60)),
        (4, dis "c1" (cost := usd 40)), (5, dis "c2" (cost := usd 60))]) == claimed
#guard last (go [(2, pr "c1" "metered" (usd 40)), (3, pr "c2" "metered" (usd 61)),
        (4, dis "c1" (cost := usd 40)), (5, dis "c2" (cost := usd 61))]) == .rejected .meterExceeded

def over := go (two ++ [(5, .result "c1" .succeeded (some 80) false)])
#guard usage over == 80
#guard over.1.sessionMeters.map (·.committed) == [true]
#guard over.1.failures.get? "metered" == some 1
#guard statusOf over "c1" == some .succeeded
#guard usage (go (two ++ [(5, .result "c1" .succeeded (some 40) false)])) == 40
#guard usage (go (two ++ [(5, .result "c1" .succeeded Option.none false)])) == 60
#guard (go (two ++ [(5, .result "c1" .failed Option.none false), (6, .result "c1" .succeeded Option.none false)])).2.getLast?
        == some (.rejected .callEnded)
#guard (go (two ++ [(5, .result "c1" .succeeded Option.none false)])).1.failures.get? "metered" == some 0
#guard last (go [(2, .result "c1" .succeeded Option.none false)]) == .rejected .unknownCall
#guard last (go [(2, pr "c1" "free"), (3, .result "c1" .succeeded Option.none false)])
        == .rejected .callAuthorized

def atZero : List (Nat × EventBody) :=
  [(0, start [] []), (0, .turnStart true), (0, pr "c1" "wmetered" (usd 60)),
   (0, pr "c2" "wmetered" (usd 60)), (0, dis "c1" (cost := usd 60))]
def windowed := script dp atZero
#guard windowed.1.sessionMeters.map (·.time) == [0]
#guard usage windowed "wm" 999 == 60
#guard usage windowed "wm" 1000 == 0
#guard last (script dp (atZero ++ [(999, dis "c2" (cost := usd 60))])) == .rejected .meterExceeded
#guard last (script dp (atZero ++ [(1000, dis "c2" (cost := usd 60))])) == claimed

def principal := go [(2, pr "c1" "pmetered" (usd 60)), (3, dis "c1" (cost := usd 60))]
#guard (go [(2, pr "c1" "pmetered" (usd 60))]).1.ledger.version == 0
#guard principal.1.ledger.version == 2
#guard principal.1.sessionMeters == []
#guard (go (two ++ [(5, .result "c1" .succeeded Option.none false)])).1.ledger.version == 1
#guard (go [(2, pr "c1" "pmetered" (usd 60)), (3, dis "c1" (cost := usd 60)),
        (4, .result "c1" .succeeded Option.none false)]).1.ledger.version == 3
def secondStart (id : String) : EventBody :=
  .sessionStart id "pd" "u1" ["perm"] [("alice", alice)] principal.1.ledger
def second := script dp [(0, secondStart "s2"), (1, .turnStart true), (2, pr "c9" "pmetered" (usd 60))]
def reused := checkedScript dp [(0, secondStart "s1")]
#guard lastChecked reused == .rejected .alreadyStarted
#guard reused.2.2 && !reused.1.started
#guard lastChecked (checkedScript dp [(0, secondStart "s2")]) == .ok .none Option.none
#guard (checkedScript dp [(0, secondStart "s2")]).2.2
#guard usage second "pm" == 60
#guard last second == .ok (.denied .meterExceeded) Option.none
#guard second.1.ledger.version == 2

def revoked := go [(2, pr "c1" "needsPerm"), (3, .permissionRevoke "perm"), (4, dis "c1")]
#guard last revoked == .ok (.dispatchDenied .permissionMissing) Option.none
#guard statusOf revoked "c1" == some (.deniedAtDispatch .permissionMissing)

-- Review Focus 5: TTLs are half-open, valid while time < authorizedAt + ttl (spec section 5, limits)
def ttl : Policy := { dp with limits := { authorizedTtlMs := some 10 } }
#guard last (go [(2, pr "c1" "free"), (13, dis "c1")] ttl)
        == .ok (.dispatchDenied .authorizationExpired) Option.none
#guard statusOf (go [(2, pr "c1" "free"), (13, dis "c1")] ttl) "c1" == some .expired
#guard last (go [(2, pr "c1" "free"), (12, dis "c1")] ttl)
        == .ok (.dispatchDenied .authorizationExpired) Option.none
#guard last (go [(2, pr "c1" "free"), (11, dis "c1")] ttl) == claimed

def perAction : Policy := { ttl with actions := dp.actions ++ [("slow", { authorizedTtlMs := some 100 })] }
#guard last (go [(2, pr "c1" "slow"), (101, dis "c1")] perAction) == claimed
#guard last (go [(2, pr "c1" "slow"), (102, dis "c1")] perAction)
        == .ok (.dispatchDenied .authorizationExpired) Option.none
#guard last (go [(2, pr "c1" "free"), (12, dis "c1")] perAction)
        == .ok (.dispatchDenied .authorizationExpired) Option.none
#guard last (go [(2, pr "c1" "slow"), (102, pr "c1" "slow")] perAction)
        == .ok (.denied .authorizationExpired) Option.none
#guard last (go [(2, pr "c1" "slow"), (101, pr "c1" "slow")] perAction) == .ok .allowed Option.none

def guardOff := go [(2, pr "c1" "guarded" (g := [("g", true)])), (3, dis "c1" (g := [("g", false)]))]
#guard last guardOff == .rejected .guardFalse
#guard statusOf guardOff "c1" == some .authorized
#guard last (go [(2, pr "c1" "guarded" (g := [("g", true)])), (3, dis "c1")]) == .rejected .guardFalse
#guard last (go [(2, pr "c1" "guarded" (g := [("g", true)])), (3, dis "c1" (g := [("g", true)]))])
        == claimed

def retried : List (Nat × EventBody) :=
  [(2, pr "c1" "retry" (usd 60)), (3, dis "c1" (cost := usd 60)), (4, .outcomeUnknown "c1")]
#guard (go retried).2.getLast? == some okNone
#guard statusOf (go retried) "c1" == some .unknown
#guard (go retried).1.failures.get? "retry" == some 1
#guard last (go (retried ++ [(5, dis "c1" 2 (cost := usd 60))])) == claimed
#guard last (go (retried ++ [(5, dis "c1" 2 (cost := usd 60) (key := "k2"))]))
        == .rejected .idempotencyKeyMismatch
#guard last (go (retried ++ [(5, dis "c1" 2 (cost := usd 60)), (6, .outcomeUnknown "c1"),
        (7, dis "c1" 3 (cost := usd 60))])) == .rejected .attemptLimit
#guard usage (go retried) == 60
#guard usage (go (retried ++ [(5, dis "c1" 2 (cost := usd 60))])) == 60
#guard (go (retried ++ [(5, dis "c1" 2 (cost := usd 60))])).1.sessionMeters.length == 1
#guard last (go (retried ++ [(5, .reconcile "c1" .succeeded Option.none false), (6, dis "c1" 2 (cost := usd 60))]))
        == .rejected .alreadyReconciled

def onceUnknown : List (Nat × EventBody) :=
  [(2, pr "c1" "once" (usd 60)), (3, dis "c1" (cost := usd 60)), (4, .outcomeUnknown "c1")]
#guard last (go (onceUnknown ++ [(5, dis "c1" 2 (cost := usd 60))])) == .rejected .retryNotAllowed
#guard last (go [(2, pr "c1" "free"), (3, .outcomeUnknown "c1")]) == .rejected .callAuthorized
#guard last (go [(2, .outcomeUnknown "c1")]) == .rejected .unknownCall

#guard usage (go (onceUnknown ++ [(5, .reconcile "c1" .failed Option.none true)])) == 0
#guard usage (go (onceUnknown ++ [(5, .reconcile "c1" .succeeded (some 30) false)])) == 30
#guard statusOf (go (onceUnknown ++ [(5, .reconcile "c1" .succeeded (some 30) false)])) "c1" == some .unknown
#guard last (go (onceUnknown ++ [(5, .reconcile "c1" .succeeded (some 30) false),
        (6, .reconcile "c1" .succeeded (some 30) false)])) == .rejected .alreadyReconciled
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .reconcile "c1" .succeeded Option.none false)])
        == .rejected .callDispatched
#guard last (go [(2, .reconcile "c1" .succeeded Option.none false)]) == .rejected .unknownCall

def shadowRevoked := go [(2, pr "c1" "shadowPerm"), (3, .permissionRevoke "perm"), (4, dis "c1")]
#guard last shadowRevoked == .ok .dispatchClaimed (some (.wouldDeny .permissionMissing))
#guard statusOf shadowRevoked "c1" == some .dispatched
#guard last (go [(2, pr "c1" "shadowPerm"), (3, dis "c1" (d := "d2"))]) == .rejected .digestMismatch
def shadowOver := go [(2, pr "c1" "shadowMetered" (usd 60)), (3, pr "c2" "shadowMetered" (usd 60)),
  (4, dis "c1" (cost := usd 60)), (5, dis "c2" (cost := usd 60))]
#guard last shadowOver == .ok .dispatchClaimed (some (.wouldDeny .meterExceeded))
#guard usage shadowOver == 120

def authorizedState (p : Policy) (tool : String) : State := (go [(2, pr "c1" tool)] p).1
def stepAt (p : Policy) (s : State) (b : EventBody) : State × Verdict :=
  step p s ⟨s.lastSeq + 1, 5, s.version, Option.none, b⟩
#guard (stepAt dp { authorizedState dp "free" with killed := true } (dis "c1")).2 == .rejected .killed
#guard statusOf ((stepAt dp { authorizedState dp "free" with killed := true } (dis "c1")).1, []) "c1"
        == some .authorized
#guard (stepAt dp { authorizedState dp "shadowPerm" with killed := true } (dis "c1")).2 == .rejected .killed
#guard (stepAt dp { authorizedState dp "free" with ledger := { tombstone := true } } (dis "c1")).2
        == .rejected .killed
#guard (stepAt dp { authorizedState dp "free" with escalated := true } (dis "c1")).2
        == .rejected .escalated
def unknownRetry : State := (go retried).1
#guard (stepAt dp { unknownRetry with killed := true } (dis "c1" 2 (cost := usd 60))).2
        == .rejected .killed
#guard statusOf ((stepAt dp { unknownRetry with killed := true } (dis "c1" 2 (cost := usd 60))).1, [])
        "c1"
        == some .unknown

def gctx : List (Nat × EventBody) :=
  [(2, .grantCreate "g1" "alice" "gcall" (some "d1") .session 3 Option.none Option.none Option.none "rd"),
   (3, pr "c1" "gcall")]
def grantOf (r : State × List Verdict) : Option (Nat × Nat) :=
  (r.1.grants.get? "g1").map (fun g => (g.reserved, g.consumed))
#guard (go gctx).2.getLast? == some (.ok (.allowedByGrant "g1") Option.none)
#guard grantOf (go gctx) == some (1, 0)
#guard grantOf (go (gctx ++ [(4, dis "c1")])) == some (0, 1)
#guard grantOf (go (gctx ++ [(4, .cancel "c1")])) == some (0, 0)
def grantGone := go (gctx ++ [(4, .grantRevoke "g1"), (5, dis "c1")])
#guard last grantGone == .ok (.dispatchDenied .grantInvalid) Option.none
#guard statusOf grantGone "c1" == some (.deniedAtDispatch .grantInvalid)
#guard grantOf grantGone == some (0, 0)

def fl : Policy := { dp with limits := { maxConsecutiveFailures := some 2 } }
def fails (n : Nat) : List (Nat × EventBody) :=
  (List.range n).flatMap fun i =>
    let id := s!"f{i}"
    [(2, pr id "free"), (2, dis id), (2, .result id .failed Option.none false)]
#guard (go (fails 1) fl).1.escalated == false
#guard (go (fails 2) fl).1.escalated == true
#guard (go (fails 2) fl).1.failures.get? "free" == some 2
#guard last (go (fails 1 ++ [(3, pr "c1" "free"), (3, dis "c1"), (3, .result "c1" .succeeded Option.none false)]) fl)
        == okNone
#guard (go (fails 1 ++ [(3, pr "c1" "free"), (3, dis "c1"), (3, .result "c1" .succeeded Option.none false)]) fl).1.failures.get? "free"
        == some 0
#guard last (go (fails 1 ++ [(3, pr "c1" "free"), (3, pr "c2" "free"), (3, .result "f0" .succeeded Option.none false)]) fl)
        == .rejected .callEnded
#guard last (go ([(2, pr "c1" "free")] ++ fails 2 ++ [(3, dis "c1")]) fl) == .rejected .escalated

def res (id : String) (o : Outcome) (actual : Option Nat := Option.none) (noEffect : Bool := false) :
    EventBody :=
  .result id o actual noEffect
def w (b : List (Nat × EventBody)) (p : Policy := dp) : State × List Verdict × Bool :=
  checkedScript p (ctx ++ b)
def runOf (r : State × List Verdict × Bool) : State × List Verdict := (r.1, r.2.1)

def declines := w [(2, pr "c1" "free"), (2, dis "c1"), (2, res "c1" .declined),
  (3, pr "c2" "free"), (3, dis "c2"), (3, res "c2" .declined), (4, pr "c3" "free")] fl
#guard declines.2.2
#guard declines.1.escalated == false
#guard lastChecked declines == .ok .allowed Option.none
#guard statusOf (runOf declines) "c1" == some .declined
#guard CallStatus.terminal .declined

def failThenDecline : List (Nat × EventBody) :=
  [(2, pr "c1" "free"), (2, dis "c1"), (2, res "c1" .failed),
   (3, pr "c2" "free"), (3, dis "c2"), (3, res "c2" .declined)]
#guard ((w failThenDecline fl).1.failures.get? "free") == some 1
#guard (w failThenDecline fl).1.failuresThisSession == 1
#guard (w (failThenDecline ++ [(4, pr "c3" "free"), (4, dis "c3"), (4, res "c3" .failed)]) fl).1.escalated
#guard last (go (failThenDecline ++ [(4, res "c2" .succeeded)]) fl) == .rejected .callEnded

def reconciledOk := w (retried ++ [(5, .reconcile "c1" .succeeded Option.none false)])
#guard reconciledOk.2.2
#guard (reconciledOk.1.calls.get? "c1").map (fun c => (c.status, c.reconciled))
        == some (.unknown, some .succeeded)
#guard ((w (retried ++ [(5, .reconcile "c1" .declined Option.none true)])).1.calls.get? "c1").map
        (·.reconciled) == some (some .declined)
#guard (w (retried ++ [(5, .reconcile "c1" .failed Option.none false)])).1.failures.get? "retry"
        == some 1
#guard (w (retried ++ [(5, .reconcile "c1" .failed Option.none false)])).1.failuresThisSession == 1
#guard ((w retried).1.calls.get? "c1").map (·.reconciled) == some Option.none

def declinedNoEffect := w (two ++ [(5, res "c1" .declined (noEffect := true))])
#guard declinedNoEffect.2.2
#guard usage (runOf declinedNoEffect) == 0
#guard usage (runOf (w (two ++ [(5, res "c1" .declined)]))) == 0
#guard (w (two ++ [(5, res "c1" .declined)])).2.2
#guard statusOf (runOf (w (two ++ [(5, res "c1" .declined)]))) "c1" == some .declined
#guard usage (runOf (w (two ++ [(5, res "c1" .succeeded (some 40) true)]))) == 0
#guard last (go (two ++ [(5, res "c1" .declined (noEffect := true)), (6, dis "c2" (cost := usd 60))]))
        == claimed

#guard grantOf (runOf (w (gctx ++ [(4, dis "c1"), (5, res "c1" .declined (noEffect := true))])))
        == some (0, 1)

def interrupted (b : EventBody) := w [(2, pr "c1" "free"), (3, dis "c1"), (4, b)] fl
#guard statusOf (runOf (interrupted .reset)) "c1" == some .unknown
#guard (interrupted .reset).1.failures.get? "free" == Option.none
#guard (interrupted .reset).1.failuresThisSession == 0
#guard statusOf (runOf (interrupted .sessionEnd)) "c1" == some .unknown
#guard (interrupted .sessionEnd).1.failuresThisSession == 0

namespace Meters

def mp : Policy where
  meters :=
    [ ("usd_day", { unit := .money "USD", cap := some 100, windowMs := some 1000 })
    , ("usd_month", { unit := .money "USD", cap := some 150 })
    , ("calls_h", { unit := .calls, cap := some 2, windowMs := some 1000 })
    , ("track", { unit := .money "USD" }) ]
  actions :=
    [ ("pay", { meters := ["usd_day", "usd_month"] })
    , ("ping", { meters := ["calls_h"] })
    , ("watch", { meters := ["track"] })
    , ("retry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 3
                  meters := ["usd_day"] }) ]

#guard mp.check.isEmpty

def mw (b : List (Nat × EventBody)) : State × List Verdict × Bool :=
  checkedScript mp ([(0, start [] []), (0, .turnStart true)] ++ b)
def entriesOf (r : State × List Verdict × Bool) (m id : String) : List MeterEntry :=
  (r.1.meterEntries mp m).filter fun e => e.meter == m && e.call == id
def amountTime (r : State × List Verdict × Bool) (m id : String) : List (Nat × Nat × Bool) :=
  (entriesOf r m id).map fun e => (e.amount, e.time, e.committed)
def excessOf (r : State × List Verdict × Bool) (m id : String) : List (Nat × Nat) :=
  (entriesOf r m id).map fun e => (e.excess, e.excessAt)
def musage (r : State × List Verdict × Bool) (m : String) (now : Nat) : Nat :=
  match mp.meter? m with
  | some spec => Meter.usage spec (r.1.meterEntries mp m) m now
  | Option.none => 0
def holds (r : State × List Verdict × Bool) (v : Verdict) : Bool := r.2.2 && lastChecked r == v

-- Review Focus 1: all or nothing across meters, in both meter orders
def aon := mw [(0, pr "c1" "pay" (usd 60)), (0, pr "c2" "pay" (usd 60)),
  (1, dis "c1" (cost := usd 60)), (2, dis "c2" (cost := usd 60))]
#guard holds aon (.rejected .meterExceeded)
#guard entriesOf aon "usd_month" "c2" == [] && entriesOf aon "usd_day" "c2" == []
#guard statusOf (runOf aon) "c2" == some .authorized
#guard amountTime aon "usd_day" "c1" == [(60, 1, false)] && amountTime aon "usd_month" "c1" == [(60, 1, false)]
def aonMonth := mw [(0, pr "c1" "pay" (usd 60)), (0, pr "c2" "pay" (usd 60)), (0, pr "c3" "pay" (usd 40)),
  (1, dis "c1" (cost := usd 60)), (1500, dis "c2" (cost := usd 60)), (1600, dis "c3" (cost := usd 40))]
#guard holds aonMonth (.rejected .meterExceeded)
#guard entriesOf aonMonth "usd_day" "c3" == [] && entriesOf aonMonth "usd_month" "c3" == []
#guard musage aonMonth "usd_day" 1600 == 60

#guard holds (mw [(0, pr "c1" "pay")]) (.ok (.denied .costMissing) Option.none)
#guard holds (mw [(0, pr "c1" "pay" (some ⟨1, "EUR"⟩))]) (.ok (.denied .currencyMismatch) Option.none)

-- calls meter: one per call, cost not required
def pings (t : Nat) := mw [(0, pr "p1" "ping"), (0, pr "p2" "ping"), (0, pr "p3" "ping"),
  (0, dis "p1"), (0, dis "p2"), (t, dis "p3")]
#guard holds (pings 999) (.rejected .meterExceeded)
#guard holds (pings 1000) claimed
#guard amountTime (pings 1000) "calls_h" "p3" == [(1, 1000, false)]
#guard holds (mw [(0, pr "p1" "ping"), (0, dis "p1"), (1, pr "p2" "ping"), (1, dis "p2"), (2, pr "p3" "ping")])
        (.ok (.denied .meterExceeded) Option.none)
#guard amountTime (mw [(0, pr "p1" "ping" (usd 70)), (0, dis "p1" (cost := usd 70)),
        (5, res "p1" .succeeded (some 90))]) "calls_h" "p1" == [(1, 0, true)]

-- a meter without a cap only records usage
def watched := mw [(0, pr "c1" "watch" (usd (10 ^ 9))), (0, dis "c1" (cost := usd (10 ^ 9)))]
#guard holds watched claimed
#guard musage watched "track" 0 == 10 ^ 9
#guard holds (mw [(0, pr "c1" "watch")]) (.ok (.denied .costMissing) Option.none)

-- partial capture frees the difference
def captured := mw [(1, pr "c1" "pay" (usd 50)), (1, dis "c1" (cost := usd 50)),
  (2, res "c1" .succeeded (some 20)), (3, pr "c2" "pay" (usd 80)), (3, dis "c2" (cost := usd 80))]
#guard holds captured claimed
#guard amountTime captured "usd_day" "c1" == [(20, 1, true)] && amountTime captured "usd_month" "c1" == [(20, 1, true)]
#guard excessOf captured "usd_day" "c1" == [(0, 0)]
#guard (captured.1.failures.get? "pay") == some 0

-- red-team L1: an overrun commits in full on a failed or succeeded report, and counts one failure per
-- event; a declined report releases, whatever actual cost it carries
def reported (o : Outcome) (actual : Option Nat) := mw [(1, pr "c1" "pay" (usd 50)),
  (1, dis "c1" (cost := usd 50)), (2, res "c1" o actual)]
def failureCounts (r : State × List Verdict × Bool) : Option Nat × Nat :=
  (r.1.failures.get? "pay", r.1.failuresThisSession)
#guard holds (reported .failed (some 90)) (.ok (.overrun ["usd_day", "usd_month"]) Option.none)
#guard amountTime (reported .failed (some 90)) "usd_day" "c1" == [(50, 1, true)]
#guard excessOf (reported .failed (some 90)) "usd_day" "c1" == [(40, 2)]
#guard amountTime (reported .failed (some 90)) "usd_month" "c1" == [(50, 1, true)]
#guard excessOf (reported .failed (some 90)) "usd_month" "c1" == [(40, 2)]
#guard failureCounts (reported .failed (some 90)) == (some 1, 1)
#guard failureCounts (reported .succeeded (some 90)) == (some 1, 1)
#guard failureCounts (reported .declined (some 90)) == (Option.none, 0)
#guard holds (reported .declined (some 90)) okNone
#guard entriesOf (reported .declined (some 90)) "usd_day" "c1" == []
#guard entriesOf (reported .declined (some 90)) "usd_month" "c1" == []
#guard failureCounts (reported .declined (some 50)) == (Option.none, 0)
#guard failureCounts (reported .succeeded (some 50)) == (some 0, 0)
#guard amountTime (reported .failed (some 20)) "usd_day" "c1" == [(20, 1, true)]
#guard amountTime (reported .failed Option.none) "usd_day" "c1" == [(50, 1, true)]
#guard holds (reported .succeeded (some 90)) (.ok (.overrun ["usd_day", "usd_month"]) Option.none)
        && musage (reported .succeeded (some 90)) "usd_day" 2 == 90

-- red-team L3: a late overrun's excess is dated at the report; the reserved part keeps its time
def late := mw [(3, pr "c1" "pay" (usd 10)), (3, dis "c1" (cost := usd 10)), (2000, res "c1" .succeeded (some 100))]
#guard amountTime late "usd_day" "c1" == [(10, 3, true)] && excessOf late "usd_day" "c1" == [(90, 2000)]
#guard musage late "usd_day" 2000 == 90
#guard musage late "usd_day" 2999 == 90 && musage late "usd_day" 3000 == 0
def afterLate (n : Nat) := mw [(3, pr "c1" "pay" (usd 10)), (3, dis "c1" (cost := usd 10)),
  (2000, res "c1" .succeeded (some 100)), (2001, pr "c2" "pay" (usd n))]
#guard holds (afterLate 11) (.ok (.denied .meterExceeded) Option.none)
#guard holds (afterLate 10) (.ok .allowed Option.none)

-- a commit without overrun never moves checked spend into a later window
def probe := mw [(0, pr "c1" "pay" (usd 60)), (0, pr "c2" "pay" (usd 90)), (0, dis "c1" (cost := usd 60)),
  (1500, dis "c2" (cost := usd 90)), (1600, res "c1" .succeeded (some 60))]
#guard holds probe okNone
#guard probe.2.1[5]? == some claimed
-- the commit at 1600 is already outside the window, so the step that commits it also prunes it
#guard entriesOf probe "usd_day" "c1" == [] && amountTime probe "usd_month" "c1" == [(60, 0, true)]
#guard musage probe "usd_day" 1600 == 90

def unknownAt0 : List (Nat × EventBody) :=
  [(0, pr "c1" "retry" (usd 60)), (0, dis "c1" (cost := usd 60)), (1, .outcomeUnknown "c1")]
def reconciledLate := mw (unknownAt0 ++ [(2000, .reconcile "c1" .succeeded Option.none false)])
#guard entriesOf reconciledLate "usd_day" "c1" == []
def reconciledInWindow := mw (unknownAt0 ++ [(999, .reconcile "c1" .succeeded Option.none false)])
#guard holds reconciledInWindow okNone
#guard amountTime reconciledInWindow "usd_day" "c1" == [(60, 0, true)]
        && excessOf reconciledInWindow "usd_day" "c1" == [(0, 0)]
def reconciledOver := mw (unknownAt0 ++ [(2000, .reconcile "c1" .failed (some 70) false)])
#guard amountTime reconciledOver "usd_day" "c1" == [(60, 0, true)] && excessOf reconciledOver "usd_day" "c1" == [(10, 2000)]
#guard musage reconciledOver "usd_day" 2000 == 10
#guard (let r := mw (unknownAt0 ++ [(2000, .reconcile "c1" .declined (some 70) false)])
        (r.1.failures.get? "retry", r.1.failuresThisSession)) == (some 1, 1)
#guard entriesOf (mw (unknownAt0 ++ [(2000, .reconcile "c1" .failed (some 70) true)])) "usd_day" "c1" == []

-- red-team L2: a retry whose reservation left the window must fit the cap again
def outsideRetry := mw [(0, pr "c1" "retry" (usd 60)), (0, pr "c2" "pay" (usd 100)),
  (0, dis "c1" (cost := usd 60)), (1, .outcomeUnknown "c1"), (1500, dis "c2" (cost := usd 100)),
  (1600, dis "c1" 2 (cost := usd 60))]
#guard holds outsideRetry (.rejected .meterExceeded)
#guard outsideRetry.2.1[6]? == some claimed
#guard statusOf (runOf outsideRetry) "c1" == some .unknown
#guard amountTime outsideRetry "usd_day" "c1" == [(60, 0, false)]
def retimed := mw (unknownAt0 ++ [(1600, dis "c1" 2 (cost := usd 60))])
#guard holds retimed claimed
#guard amountTime retimed "usd_day" "c1" == [(60, 1600, false)]
#guard amountTime (mw (unknownAt0 ++ [(999, dis "c1" 2 (cost := usd 60))])) "usd_day" "c1" == [(60, 0, false)]
-- inside the window the reservation is reused even with usage above the cap
def overCap := mw (unknownAt0 ++ [(2, pr "c2" "pay" (usd 40)), (2, dis "c2" (cost := usd 40)),
  (3, res "c2" .succeeded (some 90)), (4, dis "c1" 2 (cost := usd 60))])
#guard holds overCap claimed
#guard musage overCap "usd_day" 4 == 150

-- Review Focus 5: half-open windows
def spec1000 : MeterSpec := { unit := .money "USD", cap := some 100, windowMs := some 1000 }
def entryAt (t : Nat) : MeterEntry :=
  { meter := "m", session := "s1", call := "c1", time := t, amount := 10, committed := false }
#guard Meter.usage spec1000 [entryAt 5] "m" 1004 == 10
#guard Meter.usage spec1000 [entryAt 5] "m" 1005 == 0
def overrunAt (t : Nat) : MeterEntry := { entryAt 0 with committed := true, excess := 7, excessAt := t }
#guard Meter.usage spec1000 [overrunAt 5] "m" 1004 == 7
#guard Meter.usage spec1000 [overrunAt 5] "m" 1005 == 0

end Meters

namespace Settle

def sp : Policy where
  meters := [("m", { unit := .money "USD", cap := some 1000, windowMs := some 100 })]
  actions := [("buy", { meters := ["m"] })]

#guard sp.check.isEmpty

def sw (b : List (Nat × EventBody)) : State × List Verdict × Bool :=
  checkedScript sp ([(0, start [] []), (0, .turnStart true)] ++ b)
def bought (t : Nat) (id : String) (n : Nat := 300) : List (Nat × EventBody) :=
  [(t, pr id "buy" (usd n)), (t, dis id (cost := usd n))]
def heldBy (r : State × List Verdict × Bool) : List String := r.1.sessionMeters.map (·.call)
def holds (r : State × List Verdict × Bool) (v : Verdict) : Bool := r.2.2 && lastChecked r == v

def declinedReleases := sw (bought 1 "c1" ++ [(2, res "c1" .declined)])
#guard holds declinedReleases okNone
#guard heldBy declinedReleases == []
#guard holds (sw (bought 1 "c1" ++ [(2, res "c1" .declined (some 500))])) okNone

def overrunDecision (actual : Nat) := sw (bought 1 "c1" ++ [(2, res "c1" .succeeded (some actual))])
#guard holds (overrunDecision 500) (.ok (.overrun ["m"]) Option.none)
#guard holds (overrunDecision 300) okNone

def pruneOnUpdate := sw (bought 10 "c1" ++ [(20, res "c1" .succeeded)] ++ bought 200 "c2")
#guard holds pruneOnUpdate claimed
#guard heldBy pruneOnUpdate == ["c2"]

def noPruneWithoutUpdate := sw (bought 10 "c1" ++ [(20, res "c1" .succeeded), (200, .turnEnd)])
#guard holds noPruneWithoutUpdate okNone
#guard heldBy noPruneWithoutUpdate == ["c1"]

def uncommittedStays := sw (bought 1 "c1" ++ [(2, .outcomeUnknown "c1")] ++ bought 3 "c2"
  ++ [(4, res "c2" .succeeded)] ++ bought 500 "c3")
#guard holds uncommittedStays claimed
#guard heldBy uncommittedStays == ["c1", "c3"]

end Settle

end WritTests.Dispatch
