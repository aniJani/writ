import WritTests.Fixtures

open Writ

namespace WritTests.Attacks

def ap : Policy where
  approverRoles := ["owner", "admin"]
  meters := [("pm", { unit := .money "USD", cap := some 100, scope := .principal })]
  limits := { maxConsecutiveFailures := some 2 }
  actions :=
    [ ("free", {}), ("a", {}), ("b", {}), ("call", { consent := .perCall })
    , ("q2", { consent := .quorum 2 Option.none false false })
    , ("human", { consent := .quorum 1 Option.none true false })
    , ("pmetered", { meters := ["pm"] }) ]

#guard ap.check.isEmpty

def alice2 : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def apprs : List (String × ApproverInfo) :=
  [("alice", alice), ("alice2", alice2), ("bob", bob), ("bot", bot)]

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩
def rid (id : String) (g : Nat := 0) : RequestId := ⟨"s1", id, g⟩
def pr (id tool : String) (cost : Option Cost := Option.none) : EventBody :=
  .propose id tool "d1" cost [] []
def appr (id who : String) (g : Nat := 0) (d : String := "d1") (e : Option Edit := Option.none) :
    EventBody :=
  .approve id (rid id g) who d Option.none e
def dis (id : String) (cost : Option Cost := Option.none) : EventBody := .dispatch id 1 "d1" cost [] "k"
def res (id : String) (o : Outcome) : EventBody := .result id o Option.none false

def ctx : List (Nat × EventBody) := [(0, start [] apprs), (1, .turnStart true)]
def w (steps : List (Nat × EventBody)) : State × List Verdict × Bool := checkedScript ap (ctx ++ steps)
def holds (r : State × List Verdict × Bool) (v : Verdict) : Bool := r.2.2 && lastChecked r == v

def spent := w [(2, pr "c1" "pmetered" (usd 100)), (3, dis "c1" (usd 100)), (4, res "c1" .succeeded)]
def escape := checkedScript ap
  [(0, .sessionStart "s2" "pd" "u1" [] apprs spent.1.ledger), (1, .turnStart true),
   (2, pr "c1" "pmetered" (usd 1))]
#guard holds spent (.ok .none Option.none)
#guard holds escape (.ok (.denied .meterExceeded) Option.none)

def beforeDispatch : State := (w [(2, pr "c1" "free")]).1
def afterDispatch : State :=
  (step ap beforeDispatch ⟨beforeDispatch.lastSeq + 1, 3, beforeDispatch.version, Option.none, dis "c1"⟩).1
def rollback := step ap afterDispatch
  ⟨afterDispatch.lastSeq + 1, 4, beforeDispatch.version, Option.none, dis "c1"⟩
#guard rollback.2 == .rejected .stateVersionMismatch
#guard rollback.1.version == afterDispatch.version
#guard Inv.check ap afterDispatch && Inv.check ap rollback.1

#guard holds (w [(2, pr "c1" "q2"), (3, appr "c1" "alice" (e := some { newDigest := "d2" })),
  (4, appr "c1" "bob" (g := 1) (d := "d1"))]) (.rejected .digestMismatch)

#guard holds (w [(2, pr "c1" "call"), (3, .reset), (4, appr "c1" "alice")]) (.rejected .callEnded)

#guard holds (w [(2, pr "c1" "call"), (3, .reject "c1" (rid "c1") "alice"), (4, .turnEnd),
  (5, .turnStart false), (6, pr "c2" "call")]) (.ok (.denied .previouslyRejected) Option.none)

#guard holds (w [(2, pr "c1" "pmetered")]) (.ok (.denied .costMissing) Option.none)

#guard holds (w [(2, pr "c1" "q2"), (3, appr "c1" "alice"), (4, appr "c1" "alice2")])
  (.rejected .alreadyApproved)

#guard holds (w [(2, pr "c1" "human"), (3, appr "c1" "bot")]) (.rejected .approverNotEligible)

#guard holds (w [(2, pr "a1" "a"), (2, dis "a1"), (2, res "a1" .failed),
  (3, pr "b1" "b"), (3, dis "b1"), (3, res "b1" .succeeded),
  (4, pr "a2" "a"), (4, dis "a2"), (4, res "a2" .failed),
  (5, pr "c1" "b")]) (.ok (.denied .escalated) Option.none)

#guard holds (w [(2, pr "c1" "free"), (3, dis "c1"), (4, dis "c1")]) (.rejected .callDispatched)
#guard holds (w [(2, pr "c1" "free"), (3, dis "c1"), (4, .cancel "c1")]) (.rejected .callDispatched)

namespace RejectionMemory

def rejectThenApprove := w [(2, pr "c1" "call"), (3, pr "c2" "call"),
  (4, .reject "c1" (rid "c1") "alice"), (5, appr "c2" "bob"), (6, dis "c2")]
#guard rejectThenApprove.2.2
#guard rejectThenApprove.2.1.drop 5 == [.rejected .previouslyRejected, .rejected .callAwaiting]
#guard (rejectThenApprove.1.calls.get? "c2").map (·.status) == some .awaiting

def editToRejected := w [(2, .propose "c1" "call" "bad" Option.none [] []), (3, pr "c2" "call"),
  (4, .reject "c1" (rid "c1") "alice"), (5, appr "c2" "bob" (e := some { newDigest := "bad" })),
  (6, .dispatch "c2" 1 "bad" Option.none [] "k")]
#guard editToRejected.2.2
#guard editToRejected.2.1.drop 5 == [.rejected .previouslyRejected, .rejected .callAwaiting]

def approveThenReject := w [(2, pr "c1" "call"), (3, pr "c2" "call"), (4, appr "c2" "bob"),
  (5, .reject "c1" (rid "c1") "alice"), (6, dis "c2")]
#guard holds approveThenReject (.ok (.dispatchDenied .previouslyRejected) Option.none)
#guard (approveThenReject.1.calls.get? "c2").map (·.status)
  == some (.deniedAtDispatch .previouslyRejected)

def gp : Policy := { ap with actions := ap.actions ++
  [("gcall", { consent := .perCall, grantable := some { scope := .session, maxUses := 2 } })] }
def grantHeld := checkedScript gp (ctx ++ [(2, pr "c1" "gcall"),
  (3, .grantCreate "g1" "alice" "gcall" (some "d1") .session 2 Option.none Option.none Option.none "rd"),
  (4, pr "c2" "gcall"), (5, .reject "c1" (rid "c1") "alice"), (6, dis "c2")])
#guard holds grantHeld (.ok (.dispatchDenied .previouslyRejected) Option.none)
#guard (grantHeld.1.grants.get? "g1").map (fun g => (g.reserved, g.consumed)) == some (0, 0)

-- a veto of a grant-authorized call before dispatch returns the grant use
def grantVeto := checkedScript gp (ctx ++
  [(2, .grantCreate "g1" "alice" "gcall" (some "d1") .session 2 Option.none Option.none Option.none "rd"),
   (3, pr "c1" "gcall"), (4, .reject "c1" (rid "c1") "bob")])
#guard holds grantVeto (.ok .none Option.none)
#guard (grantVeto.1.calls.get? "c1").map (·.status) == some .rejected
#guard (grantVeto.1.grants.get? "g1").map (fun g => (g.reserved, g.consumed)) == some (0, 0)
#guard ("gcall", "d1") ∈ grantVeto.1.rejectedMemory
#guard holds (checkedScript gp (ctx ++
  [(2, .grantCreate "g1" "alice" "gcall" (some "d1") .session 2 Option.none Option.none Option.none "rd"),
   (3, pr "c1" "gcall"), (4, .reject "c1" (rid "c1") "bob"), (5, pr "c1" "gcall")]))
  (.ok (.existing .rejected) Option.none)

-- theorem 12: a veto after quorum keeps the pair out of every later authorization in the turn
def lateVeto := w [(2, pr "c1" "q2"), (3, appr "c1" "alice"), (4, appr "c1" "bob"),
  (5, .reject "c1" (rid "c1") "bob"), (6, pr "c2" "q2")]
#guard holds lateVeto (.ok (.denied .previouslyRejected) Option.none)

def sp : Policy := { ap with actions := ap.actions ++ [("shadow", { mode := some .logOnly })] }
def shadowAuthorized : State :=
  let s := (checkedScript sp (ctx ++ [(2, pr "c1" "shadow")])).1
  { s with rejectedMemory := [("shadow", "d1")] }
#guard (step sp shadowAuthorized ⟨shadowAuthorized.lastSeq + 1, 3, shadowAuthorized.version,
    Option.none, dis "c1"⟩).2 == .ok .dispatchClaimed (some (.wouldDeny .previouslyRejected))

#guard holds (w [(2, pr "c1" "call"), (3, .reject "c1" (rid "c1") "alice"), (4, .reset),
  (5, pr "c2" "call")]) (.ok (.denied .previouslyRejected) Option.none)

end RejectionMemory

namespace EditEscalators

def ep : Policy := { ap with actions := ap.actions ++
  [ ("esc", { consent := .perCall, escalate := [("over_limit", { consent := .quorum 2 Option.none false false })] })
  , ("escAdmin", { consent := .perCall
                   escalate := [("e", { consent := .quorum 1 (some ["admin"]) false false })] }) ] }
#guard ep.check.isEmpty

def proposeUnder (id tool esc : String) : EventBody := .propose id tool "d1" Option.none [] [(esc, false)]
def edit (id who : String) (esc : List (String × Bool) := []) : EventBody :=
  appr id who (e := some { newDigest := "huge", escalators := esc })
def go (steps : List (Nat × EventBody)) := checkedScript ep (ctx ++ steps)

def editRaised := go [(2, proposeUnder "c1" "esc" "over_limit"), (3, edit "c1" "alice")]
#guard holds editRaised (.ok .pending Option.none)
#guard (editRaised.1.calls.get? "c1").map (fun c => (c.tally, c.consent.clauses.map (·.k), c.generation))
  == some ([("alice", "alice")], [1, 2], 1)
#guard holds (go [(2, proposeUnder "c1" "esc" "over_limit"), (3, edit "c1" "alice"),
  (4, appr "c1" "bob" (g := 1) (d := "huge"))]) (.ok .authorized Option.none)
#guard holds (go [(2, proposeUnder "c1" "esc" "over_limit"),
  (3, edit "c1" "alice" [("over_limit", false)])]) (.ok .authorized Option.none)
#guard holds (go [(2, proposeUnder "c1" "escAdmin" "e"), (3, edit "c1" "alice")])
  (.ok .pending Option.none)
#guard holds (go [(2, proposeUnder "c1" "escAdmin" "e"), (3, edit "c1" "alice"),
  (4, appr "c1" "alice2" (g := 1) (d := "huge"))]) (.rejected .alreadyApproved)
#guard holds (go [(2, proposeUnder "c1" "escAdmin" "e"), (3, edit "c1" "alice"),
  (4, appr "c1" "bob" (g := 1) (d := "huge"))]) (.ok .authorized Option.none)
#guard holds (go [(2, proposeUnder "c1" "escAdmin" "e"), (3, edit "c1" "bob")])
  (.ok .authorized Option.none)

end EditEscalators

namespace CostThreshold

def tp : Policy := { ap with actions := ap.actions ++
  [("buy", { consent := .perCall, consentIfCostOver := some ⟨1000, "USD"⟩ })] }
#guard tp.check.isEmpty

def buy (cost : Option Cost) := checkedScript tp (ctx ++ [(2, pr "c1" "buy" cost)])
#guard holds (buy (some ⟨1, "XAU"⟩)) (.ok (.needsApproval (rid "c1")) Option.none)
#guard holds (buy (usd 999)) (.ok .allowed Option.none)
#guard holds (buy (usd 1000)) (.ok (.needsApproval (rid "c1")) Option.none)
#guard holds (buy Option.none) (.ok (.needsApproval (rid "c1")) Option.none)

end CostThreshold

namespace SessionFailures

def fp (limit : Option Nat) : Policy :=
  { approverRoles := ["owner", "admin"], limits := { maxFailuresPerSession := limit }
    actions := [("a", {}), ("b", {}), ("c", {})] }

def once (id tool : String) (o : Outcome := .failed) : List (Nat × EventBody) :=
  [(2, pr id tool), (2, dis id), (2, res id o)]
def threeTools : List (Nat × EventBody) := once "a1" "a" ++ once "b1" "b" ++ once "c1" "c"
def go (limit : Option Nat) (steps : List (Nat × EventBody)) := checkedScript (fp limit) (ctx ++ steps)

def limited := go (some 3) (threeTools ++ [(3, pr "x" "a")])
#guard holds limited (.ok (.denied .escalated) Option.none)
#guard limited.1.escalated && limited.1.failuresThisSession == 3
def unlimited := go Option.none (threeTools ++ [(3, pr "x" "a")])
#guard holds unlimited (.ok .allowed Option.none)
#guard !unlimited.1.escalated && unlimited.1.failuresThisSession == 3
#guard (go (some 3) (once "a1" "a" ++ once "b1" "b" .succeeded)).1.failuresThisSession == 1
def acked := go (some 3) (threeTools ++ [(3, .escalationAck "alice" 1)])
#guard holds acked (.ok .none Option.none)
#guard !acked.1.escalated && acked.1.failuresThisSession == 0

end SessionFailures

namespace ReconcileOverrun

def rp : Policy := { ap with actions := ap.actions ++
  [("mretry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2, meters := ["pm"] })] }
#guard rp.check.isEmpty

def unknown : List (Nat × EventBody) :=
  [(2, pr "c1" "mretry" (usd 10)), (3, dis "c1" (usd 10)), (4, .outcomeUnknown "c1")]
def go (steps : List (Nat × EventBody)) := checkedScript rp (ctx ++ steps)
def counts (r : State × List Verdict × Bool) : Nat × Nat :=
  (r.1.failures.getD "mretry" 0, r.1.failuresThisSession)

#guard (go unknown).2.2 && counts (go unknown) == (1, 1)
def overrun := go (unknown ++ [(5, .reconcile "c1" .succeeded (some 30) false)])
#guard holds overrun (.ok (.overrun ["pm"]) Option.none)
#guard counts overrun == (2, 2)
#guard overrun.1.escalated
#guard counts (go (unknown ++ [(5, .reconcile "c1" .succeeded (some 10) false)])) == (1, 1)
#guard counts (go (unknown ++ [(5, .reconcile "c1" .succeeded (some 30) true)])) == (1, 1)

end ReconcileOverrun

namespace RetryTtl

def tp : Policy := { ap with
  limits := { authorizedTtlMs := some 10 }
  actions := ap.actions ++
    [("retry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 })] }
#guard tp.check.isEmpty

def go (retryAt : Nat) := checkedScript tp (ctx ++
  [(2, pr "c1" "retry"), (3, dis "c1"), (4, .outcomeUnknown "c1"),
   (retryAt, .dispatch "c1" 2 "d1" Option.none [] "k")])
#guard holds (go 13) (.rejected .authorizationExpired)
#guard ((go 13).1.calls.get? "c1").map (fun c => (c.status, c.attempts)) == some (.unknown, 1)
-- half-open: authorized at 2 with TTL 10, valid while time < 12 (spec section 5, limits)
#guard holds (go 12) (.rejected .authorizationExpired)
#guard holds (go 11) (.ok .dispatchClaimed Option.none)

end RetryTtl

namespace KilledReplay

def killed := w [(2, pr "c1" "free"), (3, .kill), (4, pr "c1" "free")]
#guard holds killed (.ok (.denied .killed) Option.none)
#guard (killed.1.calls.get? "c1").map (fun c => (c.status, c.decision))
  == some (.cancelled, .allowed)
#guard holds (w [(2, pr "c1" "free"), (3, .kill), (4, pr "c1" "a")]) (.rejected .duplicateCall)

def tombstoned : State :=
  let s := (w [(2, pr "c1" "free")]).1
  { s with ledger := { s.ledger with tombstone := true } }
#guard (step ap tombstoned
    ⟨tombstoned.lastSeq + 1, 3, tombstoned.version, Option.none, pr "c1" "free"⟩).2
  == .ok (.denied .killed) Option.none
-- a tombstone never coexists with a pending call: kill and ledgerSync both void them
#guard Inv.check ap (w [(2, pr "c1" "free")]).1 && !Inv.check ap tombstoned

end KilledReplay

namespace UnmeteredEditCost

def priced : Option Edit := some { newDigest := "d2", newCost := usd 5 }
def edit (cost : Option Cost) (e : Option Edit) (dispatchCost : Option Cost) := w
  [(2, pr "c1" "call" cost), (3, .approve "c1" (rid "c1") "alice" "d1" cost e),
   (4, .dispatch "c1" 1 "d2" dispatchCost [] "k")]

def edited := edit Option.none priced (usd 5)
#guard holds edited (.ok .dispatchClaimed Option.none)
#guard (edited.1.calls.get? "c1").map (·.cost) == some (usd 5)
#guard holds (edit Option.none priced Option.none) (.rejected .costMismatch)
#guard holds (edit (usd 3) (some { newDigest := "d2" }) (usd 3)) (.ok .dispatchClaimed Option.none)

end UnmeteredEditCost

namespace SessionEnd

def ep : Policy where
  approverRoles := ["owner"]
  meters := [("m", { unit := .money "USD", cap := some 100 })]
  actions := [("metered", { meters := ["m"] }),
    ("gcall", { consent := .perCall, grantable := some { scope := .session, maxUses := 2 } })]

def endSteps : List (Nat × EventBody) := ctx ++
  [(2, .grantCreate "g1" "alice" "gcall" (some "d1") .session 2 Option.none Option.none Option.none "rd"),
   (3, pr "c1" "metered" (usd 10)), (4, dis "c1" (usd 10)), (5, .sessionEnd)]
def ended := checkedScript ep endSteps
#guard holds ended (.ok .none Option.none)
#guard ended.1.ended
#guard (ended.1.calls.get? "c1").map (·.status) == some .unknown
#guard (ended.1.grants.get? "g1").map (·.revoked) == some true
#guard ended.1.sessionMeters.map (fun e => (e.call, e.amount)) == [("c1", 10)]

def afterEnd (b : EventBody) := checkedScript ep (endSteps ++ [(6, b)])
def released := afterEnd (.reconcile "c1" .succeeded Option.none true)
#guard holds released (.ok .none Option.none)
#guard released.1.sessionMeters == []
#guard (released.1.calls.get? "c1").map (fun c => (c.status, c.reconciled)) == some (.unknown, some .succeeded)
#guard released.1.failuresThisSession == 0
def lateOverrun := afterEnd (.reconcile "c1" .succeeded (some 30) false)
#guard holds lateOverrun (.ok (.overrun ["m"]) Option.none)
#guard lateOverrun.1.failuresThisSession == 1
#guard holds (afterEnd (pr "c2" "metered" (usd 1))) (.rejected .sessionEnded)
#guard holds (afterEnd (dis "c1" (usd 10))) (.rejected .sessionEnded)
#guard holds (afterEnd (.ledgerSync ended.1.ledger)) (.ok .none Option.none)

end SessionEnd

-- Two live sessions A ("s1") and B ("s2") of principal u1 under a gateway binding (section 7).
namespace LedgerSync

def lp : Policy := { ap with killSetsTombstone := true }
def l0 : Ledger := {}
def sessA (steps : List (Nat × EventBody)) := checkedScript lp (ctx ++ steps)
def sessB (steps : List (Nat × EventBody)) := checkedScript lp
  ([(0, .sessionStart "s2" "pd" "u1" [] apprs l0), (1, .turnStart true)] ++ steps)
def statusOf (r : State × List Verdict × Bool) (id : String) : Option CallStatus :=
  (r.1.calls.get? id).map (·.status)

def aSpent := sessA [(2, pr "c1" "pmetered" (usd 90)), (3, dis "c1" (usd 90)), (4, res "c1" .succeeded)]
#guard holds aSpent (.ok .none Option.none)
#guard holds (sessB [(2, pr "c1" "pmetered" (usd 90))]) (.ok .allowed Option.none)
def bSynced := sessB [(2, .ledgerSync aSpent.1.ledger)]
#guard holds bSynced (.ok .none Option.none)
#guard bSynced.1.ledger == aSpent.1.ledger
#guard holds (sessB [(2, .ledgerSync aSpent.1.ledger), (3, pr "c1" "pmetered" (usd 90))])
  (.ok (.denied .meterExceeded) Option.none)
#guard holds (sessB [(2, .ledgerSync aSpent.1.ledger), (3, pr "c1" "pmetered" (usd 10))])
  (.ok .allowed Option.none)

-- every claim moves the version off the one it read, so a second compare-and-swap on l0 fails
def aIdle := sessA [(2, pr "a1" "free")]
def bIdle := sessB [(2, pr "b1" "free")]
def aClaim := sessA [(2, pr "a1" "free"), (3, dis "a1")]
def bClaim := sessB [(2, pr "b1" "free"), (3, dis "b1")]
#guard aIdle.1.ledger.version == l0.version && bIdle.1.ledger.version == l0.version
#guard aClaim.1.ledger.version == l0.version + 1 && bClaim.1.ledger.version == l0.version + 1
#guard aSpent.1.ledger.version == 3
#guard (sessB [(2, .ledgerSync aSpent.1.ledger), (3, pr "b1" "free"), (4, dis "b1")]).1.ledger.version
  == aSpent.1.ledger.version + 1

def aKilled := sessA [(2, .kill)]
#guard aKilled.1.ledger.tombstone && aKilled.1.ledger.version == l0.version + 1
def bPending : List (Nat × EventBody) := [(2, pr "b1" "call"), (3, pr "b2" "free")]
def bVoided := sessB (bPending ++ [(4, .ledgerSync aKilled.1.ledger)])
#guard holds bVoided (.ok .none Option.none)
#guard statusOf bVoided "b1" == some .cancelled && statusOf bVoided "b2" == some .cancelled
#guard !bVoided.1.killed && bVoided.1.ledger.tombstone
#guard holds (sessB (bPending ++ [(4, .ledgerSync aKilled.1.ledger), (5, dis "b2")]))
  (.rejected .killed)
#guard holds (sessB (bPending ++ [(4, .ledgerSync aKilled.1.ledger), (5, pr "b3" "free")]))
  (.ok (.denied .killed) Option.none)

def bBase := sessB [(2, pr "b1" "pmetered" (usd 10)), (3, dis "b1" (usd 10))]
#guard bBase.1.ledger.entries.length == 1
def syncB (base : State) (l : Ledger) : State × Verdict :=
  step lp base ⟨base.lastSeq + 1, 9, base.version, Option.none, .ledgerSync l⟩
def conflicts (base : State) (l : Ledger) : Bool :=
  let (s', v) := syncB base l
  v == .rejected .ledgerConflict && s'.version == base.version && s'.ledger == base.ledger
    && s'.lastSeq == base.lastSeq && s'.calls.toList.map (·.2.status) == base.calls.toList.map (·.2.status)
def bumped (l : Ledger) : Ledger := { l with version := l.version + 5 }

#guard conflicts bBase.1 { bBase.1.ledger with version := bBase.1.ledger.version - 1 }
#guard conflicts bBase.1
  (bumped { bBase.1.ledger with entries := bBase.1.ledger.entries.map ({ · with amount := 1 }) })
#guard conflicts bBase.1 (bumped { bBase.1.ledger with entries := [] })
def bTomb := (syncB bBase.1 (bumped { bBase.1.ledger with tombstone := true })).1
#guard bTomb.ledger.tombstone
#guard conflicts bTomb (bumped { bTomb.ledger with tombstone := false })
#guard (syncB bBase.1 bBase.1.ledger).2 == .ok .none Option.none
def withA := syncB bBase.1
  (bumped { bBase.1.ledger with entries := aSpent.1.ledger.entries ++ bBase.1.ledger.entries })
#guard withA.2 == .ok .none Option.none
#guard Inv.check lp bTomb && Inv.check lp withA.1

end LedgerSync

end WritTests.Attacks
