import WritTests.Fixtures

open Writ

namespace WritTests.Control

def cp : Policy where
  approverRoles := ["owner", "admin"]
  escalationRoles := some ["owner"]
  limits := { maxConsecutiveFailures := some 2 }
  actions :=
    [ ("free", {}), ("a", {}), ("b", {}), ("call", { consent := .perCall })
    , ("needsPerm", { permission := some "perm" })
    , ("retry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 })
    , ("flaky", {}), ("x", {}), ("y", {}), ("z", {}) ]

def zed : ApproverInfo := ⟨"zed", .human, ["intern"]⟩
def agentA : ApproverInfo := ⟨"agent", .human, ["owner"]⟩
def apprs : List (String × ApproverInfo) :=
  [("alice", alice), ("bob", bob), ("zed", zed), ("agent", agentA)]

def ctx : List (Nat × EventBody) := [(0, start [] apprs), (1, .turnStart true)]
def go (b : List (Nat × EventBody)) (p : Policy := cp) : State × List Verdict := script p (ctx ++ b)
def pr (id tool : String) : EventBody := .propose id tool "d1" Option.none [] []
def dis (id : String) (n : Nat := 1) : EventBody := .dispatch id n "d1" Option.none [] "k"
def res (id : String) (o : Outcome) : EventBody := .result id o Option.none false
def statusOf (r : State × List Verdict) (id : String) : Option CallStatus :=
  (r.1.calls.get? id).map (·.status)
def okNone : Verdict := .ok .none Option.none

def killed := go [(2, pr "c1" "call"), (3, .approve "c1" ⟨"s1", "c1", 0⟩ "alice" "d1" Option.none Option.none),
  (4, .kill)]
#guard statusOf (go [(2, pr "c1" "call"), (3, .kill)]) "c1" == some .cancelled
#guard statusOf killed "c1" == some .cancelled
#guard last killed == okNone
#guard last (go [(2, .kill), (3, pr "c2" "free")]) == .ok (.denied .killed) Option.none
#guard (go [(2, .kill)]).1.ledger.tombstone == false

#guard last (go [(2, .kill), (3, .stepStart)]) == .rejected .killed
#guard last (go [(2, .kill), (3, .turnEnd)]) == .rejected .killed
#guard last (go [(2, pr "c1" "call"), (3, .kill),
    (4, .approve "c1" ⟨"s1", "c1", 0⟩ "alice" "d1" Option.none Option.none)]) == .rejected .killed
#guard last (go [(2, pr "c1" "free"), (3, .kill), (4, dis "c1")]) == .rejected .killed
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .kill), (5, res "c1" .succeeded)]) == okNone
#guard last (go [(2, .kill), (3, .sessionEnd)]) == okNone
#guard last (go [(2, .sessionEnd), (3, start [] apprs)]) == .rejected .sessionEnded
#guard last (go [(2, pr "c1" "call"), (3, dis "c1")]) == .rejected .callAwaiting
#guard last (go [(2, pr "c1" "free"), (3, res "c1" .succeeded)]) == .rejected .callAuthorized
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .cancel "c1")]) == .rejected .callDispatched
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"), (5, res "c1" .succeeded)])
        == .rejected .callUnknown
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, res "c1" .succeeded), (5, res "c1" .succeeded)])
        == .rejected .callEnded
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"), (5, dis "c1" 2)])
        == .rejected .retryNotAllowed
#guard last (go [(2, pr "c1" "retry"), (3, dis "c1"), (4, .outcomeUnknown "c1"),
    (5, .reconcile "c1" .failed Option.none false), (6, dis "c1" 2)]) == .rejected .alreadyReconciled
#guard last (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"),
    (5, .reconcile "c1" .failed Option.none false), (6, .reconcile "c1" .failed Option.none false)])
        == .rejected .alreadyReconciled
#guard last (go [(2, .escalationAck "alice" 0)]) == .rejected .notEscalated
#guard last (go [(2, .approverAttest "alice" zed)]) == .rejected .approverChanged
#guard Reason.all.all fun r => r.code != "protocol_order"

def tp : Policy := { cp with killSetsTombstone := true }
def firstSession := go [(2, .kill)] tp
#guard firstSession.1.ledger.tombstone == true
#guard firstSession.1.ledger.version == 1
def secondBody : EventBody := .sessionStart "s2" "pd" "u1" [] apprs firstSession.1.ledger
def secondRun := script tp [(0, secondBody), (1, .turnStart true), (2, pr "c1" "free")]
#guard secondRun.2[0]? == some (.ok .none Option.none)
#guard secondRun.2[1]? == some (.rejected .killed)
#guard last secondRun == .ok (.denied .killed) Option.none

def resetRun := go [(2, pr "c1" "call"), (3, .reset),
  (4, .approve "c1" ⟨"s1", "c1", 0⟩ "alice" "d1" Option.none Option.none)]
#guard (go [(2, pr "c1" "call"), (3, .reset)]).1.epoch == 1
#guard statusOf (go [(2, pr "c1" "call"), (3, .reset)]) "c1" == some .cancelled
#guard last resetRun == .rejected .callEnded
#guard last (go [(2, pr "c1" "call"), (3, .reset), (4, pr "c2" "call"),
    (5, .approve "c2" ⟨"s1", "c2", 0⟩ "alice" "d1" Option.none Option.none)])
        == .ok .authorized Option.none
#guard statusOf (go [(2, pr "c1" "free"), (3, .reset)]) "c1" == some .cancelled
#guard statusOf (go [(2, pr "c1" "free"), (3, dis "c1"), (4, .reset)]) "c1" == some .unknown

def lp : Policy := { cp with mode := .logOnly }
#guard last (go [(2, pr "c1" "retry"), (3, dis "c1"), (4, .outcomeUnknown "c1"), (5, .reset),
    (6, dis "c1" 2)] lp) == .rejected .staleRequest

def failA : List (Nat × EventBody) :=
  [(2, pr "a1" "a"), (2, dis "a1"), (2, res "a1" .failed)]
def failA2 : List (Nat × EventBody) :=
  [(3, pr "a2" "a"), (3, dis "a2"), (3, res "a2" .failed)]
def succB : List (Nat × EventBody) :=
  [(2, pr "b1" "b"), (2, dis "b1"), (2, res "b1" .succeeded)]
#guard (go failA).1.escalated == false
#guard last (go (failA ++ failA2 ++ [(4, pr "c1" "b")])) == .ok (.denied .escalated) Option.none
#guard last (go (failA ++ succB ++ failA2 ++ [(4, pr "c1" "b")])) == .ok (.denied .escalated) Option.none
#guard last (go (failA ++ failA2 ++ [(4, .escalationAck "bob" 1)])) == .rejected .approverNotEligible
#guard last (go (failA ++ failA2 ++ [(4, .escalationAck "zed" 1)])) == .rejected .approverNotEligible
#guard last (go (failA ++ failA2 ++ [(4, .escalationAck "agent" 1)])) == .rejected .approverNotEligible
#guard last (go (failA ++ failA2 ++ [(4, .escalationAck "nobody" 1)])) == .rejected .unknownApprover
#guard last (go (failA ++ failA2 ++ [(4, .escalationAck "alice" 1)])) == okNone
#guard last (go (failA ++ failA2 ++ [(4, .escalationAck "alice" 1), (5, pr "c1" "b")]))
        == .ok .allowed Option.none
#guard (go (failA ++ failA2 ++ [(4, .escalationAck "alice" 1)])).1.failures.isEmpty

def failOf (id tool : String) (t : Nat) : List (Nat × EventBody) :=
  [(t, pr id tool), (t, dis id), (t, res id .failed)]
def flakyTwice : List (Nat × EventBody) := failOf "f1" "flaky" 2 ++ failOf "f2" "flaky" 3
def tp2 : Policy := { cp with limits := { maxConsecutiveFailures := some 2, escalationScope := .tool } }

def toolBlocked := go flakyTwice tp2
#guard toolBlocked.1.blockedTools == ["flaky"] && !toolBlocked.1.escalated
#guard toolBlocked.1.escalations == 1
#guard last (go (flakyTwice ++ [(4, pr "c1" "flaky")]) tp2) == .ok (.denied .escalated) Option.none
#guard last (go (flakyTwice ++ [(4, pr "c1" "free")]) tp2) == .ok .allowed Option.none
#guard last (go ([(2, pr "c0" "flaky")] ++ flakyTwice ++ [(4, dis "c0")]) tp2) == .rejected .escalated
#guard last (go ([(2, pr "c0" "free")] ++ flakyTwice ++ [(4, dis "c0")]) tp2) == .ok .dispatchClaimed Option.none
#guard last (go (flakyTwice ++ [(4, .escalationAck "alice" 1), (5, pr "c1" "flaky")]) tp2)
        == .ok .allowed Option.none
#guard (go (flakyTwice ++ [(4, .escalationAck "alice" 1)]) tp2).1.blockedTools.isEmpty
#guard last (go (flakyTwice ++ [(4, pr "c1" "free")])) == .ok (.denied .escalated) Option.none
#guard last (go ([(2, pr "c0" "free")] ++ flakyTwice ++ [(4, dis "c0")])) == .rejected .escalated

def tp2s : Policy := { tp2 with limits := { tp2.limits with maxFailuresPerSession := some 2 } }
def twoTools := go (failOf "a1" "a" 2 ++ failOf "b1" "b" 3 ++ [(4, pr "c1" "free")]) tp2s
#guard last twoTools == .ok (.denied .escalated) Option.none
#guard twoTools.1.escalated && twoTools.1.blockedTools.isEmpty && twoTools.1.escalations == 1

def escFields (s : State) :=
  (s.escalated, s.blockedTools, s.escalations, s.failures.toList, s.failuresThisSession, s.version, s.lastSeq)
def blockedRun := go flakyTwice
#guard blockedRun.1.escalated && blockedRun.1.escalations == 1
def staleAck := go (flakyTwice ++ [(4, .escalationAck "alice" 0)])
#guard last staleAck == .rejected .staleRequest
#guard escFields staleAck.1 == escFields blockedRun.1
def idleAck := go [(2, .escalationAck "alice" 0)]
#guard last idleAck == .rejected .notEscalated
#guard escFields idleAck.1 == escFields (go []).1
#guard last (go [(2, .escalationAck "nobody" 0)]) == .rejected .notEscalated
#guard last (go (flakyTwice ++ [(4, .escalationAck "bob" 0)])) == .rejected .approverNotEligible

def c4p : Policy := { cp with limits := { maxConsecutiveFailures := some 1 } }
def failX := failOf "x1" "x" 2 ++ [(3, .escalationAck "alice" 1)] ++ failOf "y1" "y" 4
def lateAck := go (failX ++ [(5, .escalationAck "alice" 1)]) c4p
#guard (go (failOf "x1" "x" 2) c4p).1.escalations == 1
#guard (go failX c4p).1.escalations == 2
#guard last lateAck == .rejected .staleRequest
#guard last (go (failX ++ [(5, .escalationAck "alice" 1), (6, pr "z1" "z")]) c4p)
        == .ok (.denied .escalated) Option.none
#guard last (go (failX ++ [(5, .escalationAck "alice" 2), (6, pr "z1" "z")]) c4p) == .ok .allowed Option.none
#guard (go (failX ++ [(5, .escalationAck "alice" 2)]) c4p).1.escalations == 2

def failWhileBlocked := go ([(2, pr "c0" "free"), (2, dis "c0")] ++ failA ++ failA2 ++ [(4, res "c0" .failed)])
#guard failWhileBlocked.1.escalations == 2
#guard last (go ([(2, pr "c0" "free"), (2, dis "c0")] ++ failA ++ failA2 ++
    [(4, res "c0" .failed), (5, .escalationAck "alice" 1)])) == .rejected .staleRequest
#guard last (go ([(2, pr "c0" "free"), (2, dis "c0")] ++ failA ++ failA2 ++
    [(4, res "c0" .failed), (5, .escalationAck "alice" 2)])) == okNone

#guard last (go [(2, .permissionAdd "perm" "nobody")]) == .rejected .unknownApprover
#guard last (go [(2, .permissionAdd "perm" "agent")]) == .rejected .approverNotEligible
#guard last (go [(2, .permissionAdd "perm" "zed")]) == .rejected .approverNotEligible
#guard last (go [(2, pr "c1" "needsPerm")]) == .ok (.denied .permissionMissing) Option.none
#guard last (go [(2, .permissionAdd "perm" "alice"), (3, pr "c1" "needsPerm")])
        == .ok .allowed Option.none
#guard (go [(2, .permissionAdd "perm" "bob"), (3, .permissionAdd "perm" "alice")]).1.permissions
        == ["perm"]

end WritTests.Control
