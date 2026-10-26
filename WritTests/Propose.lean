import WritTests.Fixtures

open Writ

namespace WritTests.Propose

def prop (id tool : String) (cost : Option Cost := Option.none) (g : List (String × Bool) := [])
    (e : List (String × Bool) := []) : EventBody :=
  .propose id tool "d1" cost g e

def pp : Policy where
  meters := [("m", { unit := .money "USD", cap := some 100, maxPerCall := some 80 })]
  actions :=
    [ ("free", {}), ("hidden", { exposed := false }), ("needsPerm", { permission := some "perm" })
    , ("guarded", { guards := ["g"] }), ("esc", { escalate := [("e", { consent := .perCall })] })
    , ("metered", { meters := ["m"] }), ("call", { consent := .perCall })
    , ("shadowPerm", { permission := some "perm", mode := some .logOnly })
    , ("shadowCall", { consent := .perCall, mode := some .logOnly }) ]

def pl (l : Limits) : Policy := { pp with limits := l }
def run1 (p : Policy) (b : List EventBody) : State × List Verdict :=
  script p ([(0, start ["perm"] []), (1, .turnStart true)] ++ b.map (2, ·))
def v1 (b : EventBody) : Verdict := last (run1 pp [b])
def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩

#guard v1 (prop "c1" "nope") == .ok (.denied .unknownTool) Option.none
#guard v1 (prop "c1" "hidden") == .ok (.denied .notExposed) Option.none
#guard last (script pp [(0, start [] []), (1, .turnStart true), (2, prop "c1" "needsPerm")])
        == .ok (.denied .permissionMissing) Option.none
#guard v1 (prop "c1" "needsPerm") == .ok .allowed Option.none
#guard v1 (prop "c1" "guarded") == .ok (.denied .guardFalse) Option.none
#guard v1 (prop "c1" "guarded" (g := [("g", false)])) == .ok (.denied .guardFalse) Option.none
#guard v1 (prop "c1" "guarded" (g := [("g", true), ("g", false)])) == .ok .allowed Option.none
#guard v1 (prop "c1" "esc") == .ok (.needsApproval ⟨"s1", "c1", 0⟩) Option.none
#guard v1 (prop "c1" "esc" (e := [("e", false)])) == .ok .allowed Option.none
#guard v1 (prop "c1" "metered") == .ok (.denied .costMissing) Option.none
#guard v1 (prop "c1" "metered" (some ⟨1, "EUR"⟩)) == .ok (.denied .currencyMismatch) Option.none
#guard v1 (prop "c1" "metered" (usd 81)) == .ok (.denied .costAbovePerCall) Option.none
#guard v1 (prop "c1" "metered" (usd 80)) == .ok .allowed Option.none
#guard last (run1 { pp with meters := [("m", { unit := .money "USD", cap := some 100 })] }
        [prop "c1" "metered" (usd 100)]) == .ok .allowed Option.none
#guard last (run1 { pp with meters := [("m", { unit := .money "USD", cap := some 100 })] }
        [prop "c1" "metered" (usd 101)]) == .ok (.denied .meterExceeded) Option.none
#guard v1 (prop "c1" "free") == .ok .allowed Option.none
#guard v1 (prop "c1" "call") == .ok (.needsApproval ⟨"s1", "c1", 0⟩) Option.none

def lim1 : Limits := { maxProposalsPerTurn := some 1 }
#guard last (run1 (pl lim1) [prop "c1" "free", prop "c2" "free"]) == .ok (.denied .proposalLimit) Option.none
#guard last (run1 (pl lim1) [prop "c1" "nope", prop "c2" "free"]) == .ok (.denied .proposalLimit) Option.none
#guard last (script (pl lim1) [(0, start [] []), (1, .turnStart true), (2, prop "c1" "free"),
        (3, .turnEnd), (4, .turnStart true), (5, prop "c2" "free")]) == .ok .allowed Option.none
#guard last (run1 (pl { maxApprovalRequestsPerTurn := some 1 }) [prop "c1" "call", prop "c2" "call"])
        == .ok (.denied .approvalBudget) Option.none

def buyPolicy (l : Limits) : Policy :=
  { limits := l, meters := [("m", { unit := .money "USD", cap := some 100, maxPerCall := some 10 })]
    actions := [("free", {}), ("buy", { permission := some "p", meters := ["m"] })] }
def firstFailingCheck (l : Limits) (perms : List String := []) : Verdict :=
  last (script (buyPolicy l) [(0, start perms []), (1, .turnStart true), (2, prop "c1" "free"),
    (3, prop "c2" "buy" (usd 20))])
#guard (buyPolicy lim1).check.isEmpty
#guard firstFailingCheck lim1 == .ok (.denied .proposalLimit) Option.none
#guard firstFailingCheck {} == .ok (.denied .permissionMissing) Option.none
#guard firstFailingCheck {} ["p"] == .ok (.denied .costAbovePerCall) Option.none

def rep := run1 pp [prop "c1" "call", prop "c1" "call"]
#guard rep.2 == [.ok .none Option.none, .ok .none Option.none,
        .ok (.needsApproval ⟨"s1", "c1", 0⟩) Option.none, .ok (.needsApproval ⟨"s1", "c1", 0⟩) Option.none]
#guard rep.1.proposalsThisTurn == 1
#guard rep.1.approvalsThisTurn == 1
#guard last (run1 pp [prop "c1" "free", .propose "c1" "free" "d2" Option.none [] []])
        == .rejected .duplicateCall

#guard v1 (prop "c1" "shadowPerm") == .ok .allowed Option.none
#guard last (script pp [(0, start [] []), (1, .turnStart true), (2, prop "c1" "shadowPerm")])
        == .ok .allowed (some (.wouldDeny .permissionMissing))
#guard v1 (prop "c1" "shadowCall") == .ok .allowed (some .wouldNeedApproval)
#guard ((run1 pp [prop "c1" "shadowCall"]).1.calls.get? "c1").map (·.status) == some .authorized

def killed : State := { (run1 { pp with mode := .logOnly } []).1 with killed := true }
#guard (step { pp with mode := .logOnly } killed
        ⟨killed.lastSeq + 1, 5, killed.version, none, prop "c1" "free"⟩).2 == .ok (.denied .killed) Option.none

def lo : Policy := { pp with mode := .logOnly }
def loChecked (tool : String) (extra : List EventBody := []) :=
  checkedScript lo ([(0, start ["perm"] []), (1, .turnStart true), (2, prop "c1" tool)]
    ++ extra.map (3, ·))
def loRun (tool : String) (extra : List EventBody := []) : State × List Verdict :=
  ((loChecked tool extra).1, (loChecked tool extra).2.1)
#guard last (loRun "nope") == .ok (.denied .unknownTool) Option.none
#guard last (loRun "hidden") == .ok (.denied .notExposed) Option.none
#guard (loChecked "nope").2.2 && (loChecked "hidden").2.2
#guard last (loRun "nope" [.dispatch "c1" 1 "d1" Option.none [] "k"]) == .rejected .unknownCall
#guard last (loRun "hidden" [.dispatch "c1" 1 "d1" Option.none [] "k"]) == .rejected .callEnded
#guard last (loRun "nope" [prop "c1" "nope"]) == .ok (.denied .unknownTool) Option.none
#guard last (loRun "hidden" [prop "c1" "hidden"]) == .ok (.denied .notExposed) Option.none
#guard last (loRun "free") == .ok .allowed Option.none

def esc1 : Policy := { lo with limits := { maxConsecutiveFailures := some 1 } }
def escRun (tool : String) (extra : List EventBody := []) :=
  checkedScript esc1 ([(0, start ["perm"] []), (1, .turnStart true), (2, prop "f1" "free"),
    (2, .dispatch "f1" 1 "d1" Option.none [] "k"), (2, .result "f1" .failed Option.none false), (3, prop "c1" tool)]
    ++ extra.map (4, ·))
#guard (escRun "free").1.escalated
#guard last ((escRun "nope").1, (escRun "nope").2.1) == .ok (.denied .unknownTool) Option.none
#guard last ((escRun "hidden").1, (escRun "hidden").2.1) == .ok (.denied .notExposed) Option.none
#guard last ((escRun "nope" [.dispatch "c1" 1 "d1" Option.none [] "k"]).1,
    (escRun "nope" [.dispatch "c1" 1 "d1" Option.none [] "k"]).2.1) == .rejected .unknownCall
#guard last ((escRun "hidden" [.dispatch "c1" 1 "d1" Option.none [] "k"]).1,
    (escRun "hidden" [.dispatch "c1" 1 "d1" Option.none [] "k"]).2.1) == .rejected .callEnded
#guard ((escRun "nope" [prop "c1" "nope"]).1.calls.get? "c1").isNone
def escLast (tool : String) (p : Policy) : Verdict :=
  (checkedScript p [(0, start ["perm"] []), (1, .turnStart true), (2, prop "c0" tool),
    (2, prop "f1" "free"), (2, .dispatch "f1" 1 "d1" Option.none [] "k"),
    (2, .result "f1" .failed Option.none false), (3, prop "c0" tool)]).2.1.getLast?.getD (.rejected .notStarted)
def esc1e : Policy := { pp with limits := { maxConsecutiveFailures := some 1 } }
-- an unknown tool leaves no record, so its second proposal is fresh and unknown_tool comes first
#guard escLast "nope" esc1 == .ok (.denied .unknownTool) Option.none
#guard escLast "hidden" esc1 == .ok (.denied .escalated) Option.none
#guard escLast "nope" esc1e == .ok (.denied .unknownTool) Option.none
#guard escLast "hidden" esc1e == .ok (.denied .escalated) Option.none
#guard (escRun "nope").2.2 && (escRun "hidden").2.2
def stepRaw (s : State) (time : Nat) (b : EventBody) : State × Verdict :=
  step pp s ⟨s.lastSeq + 1, time, s.version, none, b⟩
def entry (meter : String) (time amount : Nat) : MeterEntry := { meter, session := "s0", call := "x", time, amount, committed := true }
def base : State := (run1 pp []).1
def pm (scope : MeterScope) (w : Option Nat := Option.none) : Policy :=
  { pp with meters := [("m", { unit := .money "USD", cap := some 100, scope, windowMs := w })] }
def withSpend : State := { base with sessionMeters := [entry "m" 0 60] }
def mstep (p : Policy) (s : State) (time : Nat) (amt : Nat) : Verdict :=
  (step p s ⟨s.lastSeq + 1, time, s.version, none, prop "c9" "metered" (usd amt)⟩).2

#guard mstep (pm .session) withSpend 5 40 == .ok .allowed Option.none
#guard mstep (pm .session) withSpend 5 41 == .ok (.denied .meterExceeded) Option.none

def spec1 : MeterSpec := { unit := .money "USD", cap := some 100, windowMs := some 1000 }
#guard Meter.usage spec1 [entry "m" 0 7] "m" 999 == 7
#guard Meter.usage spec1 [entry "m" 0 7] "m" 1000 == 0
#guard Meter.usage spec1 [entry "other" 0 7] "m" 0 == 0
def full : State := { base with sessionMeters := [entry "m" 0 100] }
#guard mstep (pm .session (some 1000)) full 999 1 == .ok (.denied .meterExceeded) Option.none
#guard mstep (pm .session (some 1000)) full 1000 1 == .ok .allowed Option.none

def withLedger (p : Policy) : State :=
  (script p [(0, start ["perm"] [] { entries := [entry "m" 0 60] }), (1, .turnStart true)]).1
#guard mstep (pm .principal) (withLedger (pm .principal)) 5 41 == .ok (.denied .meterExceeded) Option.none
#guard mstep (pm .principal) (withLedger (pm .principal)) 5 40 == .ok .allowed Option.none
#guard mstep (pm .session) (withLedger (pm .session)) 5 41 == .ok .allowed Option.none

#guard last (run1 pp [prop "c1" "free", .propose "c1" "free" "d1" Option.none [("g", true)] []])
        == .ok .allowed Option.none
#guard last (run1 pp [prop "c1" "free", .propose "c1" "free" "d1" Option.none [] [("e", true)]])
        == .ok .allowed Option.none

#guard (stepRaw { base with killed := true } 5 (prop "c1" "free")).2 == .ok (.denied .killed) Option.none
#guard last (script pp [(0, start ["perm"] [] { tombstone := true }), (1, .turnStart true),
        (2, prop "c1" "free")]) == .ok (.denied .killed) Option.none
#guard (stepRaw { base with escalated := true } 5 (prop "c1" "free")).2
        == .ok (.denied .escalated) Option.none
#guard (stepRaw { base with rejectedMemory := [("free", "d1")] } 5 (prop "c1" "free")).2
        == .ok (.denied .previouslyRejected) Option.none
#guard (stepRaw { base with rejectedMemory := [("free", "other")] } 5 (prop "c1" "free")).2
        == .ok .allowed Option.none

#guard last (script (pl { maxProposalsPerSession := some 1 }) [(0, start [] []), (1, .turnStart true),
        (2, prop "c1" "free"), (3, .turnEnd), (4, .turnStart true), (5, prop "c2" "free")])
        == .ok (.denied .sessionProposalLimit) Option.none
#guard last (script (pl { maxApprovalRequestsPerSession := some 1 }) [(0, start [] []), (1, .turnStart true),
        (2, prop "c1" "call"), (3, .turnEnd), (4, .turnStart true), (5, prop "c2" "call")])
        == .ok (.denied .sessionApprovalBudget) Option.none
#guard last (run1 (pl { maxProposalsPerTurn := some 1, maxProposalsPerSession := some 1 })
        [prop "c1" "free", prop "c2" "free"]) == .ok (.denied .sessionProposalLimit) Option.none
#guard last (run1 (pl { maxApprovalRequestsPerTurn := some 1, maxApprovalRequestsPerSession := some 1 })
        [prop "c1" "call", prop "c2" "call"]) == .ok (.denied .sessionApprovalBudget) Option.none
#guard Reason.retry .sessionProposalLimit == .never && Reason.retry .sessionApprovalBudget == .never

def shadowRun := run1 pp [prop "c1" "shadowCall"]
#guard shadowRun.1.approvalsThisTurn == 0
#guard shadowRun.1.approvalsThisSession == 0
#guard last (run1 (pl { maxApprovalRequestsPerTurn := some 1 }) [prop "c1" "shadowCall", prop "c2" "call"])
        == .ok (.needsApproval ⟨"s1", "c2", 0⟩) Option.none

def recs := run1 pp [prop "cd" "nope", prop "ca" "free", prop "cn" "call"]
def recOf (id : String) : Option CallRec := recs.1.calls.get? id
#guard (recOf "cd").isNone
#guard (recOf "ca").map (·.status) == some .authorized
#guard (recOf "ca").map (·.authorizedAt) == some (some 2)
#guard (recOf "ca").map (·.consent) == some .none
#guard (recOf "cn").map (·.status) == some .awaiting
#guard (recOf "cn").map (·.requestedAt) == some 2
#guard (recOf "cn").map (·.authorizedAt) == some Option.none
#guard (recOf "cn").map (·.consent) == some .perCall

namespace Repeat

def rp : Policy where
  approverRoles := ["owner", "admin"]
  limits := { maxConsecutiveFailures := some 1 }
  actions :=
    [ ("free", {}), ("needsPerm", { permission := some "perm" }), ("guarded", { guards := ["g"] })
    , ("call", { consent := .perCall }), ("q2", { consent := .quorum 2 Option.none false false })
    , ("gcall", { consent := .perCall, grantable := some { scope := .session, maxUses := 2 } })
    , ("shadow", { permission := some "perm", mode := some .logOnly }) ]

#guard rp.check.isEmpty

def apprs : List (String × ApproverInfo) := [("alice", alice), ("bob", bob)]
def go (steps : List EventBody) (p : Policy := rp) : State × List Verdict × Bool :=
  checkedScript p ([(0, start ["perm"] apprs), (1, .turnStart true)] ++ steps.map (2, ·))
def holds (r : State × List Verdict × Bool) (v : Verdict) : Bool := r.2.2 && lastChecked r == v
def pr (tool : String) (d : String := "d1") (g : List (String × Bool) := []) : EventBody :=
  .propose "c1" tool d Option.none g []
def appr (who : String) (g : Nat := 0) (d : String := "d1") (e : Option Edit := Option.none) : EventBody :=
  .approve "c1" ⟨"s1", "c1", g⟩ who d Option.none e
def dis (id : String) (d : String := "d1") : EventBody := .dispatch id 1 d Option.none [] "k"
def fail : List EventBody :=
  [.propose "f" "free" "d1" Option.none [] [], dis "f", .result "f" .failed Option.none false]

-- red-team C1/L6: a repeat reports the denial dispatch would now give
#guard holds (go [pr "needsPerm", .permissionRevoke "perm", pr "needsPerm"])
  (.ok (.denied .permissionMissing) Option.none)
#guard ((go [pr "needsPerm", .permissionRevoke "perm", pr "needsPerm"]).1.calls.get? "c1").map (·.status)
  == some .authorized
#guard holds (go [pr "needsPerm", pr "needsPerm"]) (.ok .allowed Option.none)

-- theorem 3 as amended: an awaiting call whose permission was revoked is denied on a repeat
def permCall : Policy := { rp with actions := rp.actions ++
  [("permCall", { permission := some "perm", consent := .perCall })] }
def awaitingRevoked := go [pr "permCall", .permissionRevoke "perm", pr "permCall"] permCall
#guard holds awaitingRevoked (.ok (.denied .permissionMissing) Option.none)
#guard (awaitingRevoked.1.calls.get? "c1").map (·.status) == some .awaiting
#guard holds (go [pr "permCall", pr "permCall"] permCall) (.ok (.needsApproval ⟨"s1", "c1", 0⟩) Option.none)
-- permission comes before the per-status rule, so before an expired authorization
#guard holds (go [pr "needsPerm", .permissionRevoke "perm", pr "needsPerm"]
  { rp with limits := { authorizedTtlMs := some 0 } }) (.ok (.denied .permissionMissing) Option.none)
#guard holds (go [pr "needsPerm", pr "needsPerm"] { rp with limits := { authorizedTtlMs := some 0 } })
  (.ok (.denied .authorizationExpired) Option.none)
-- `existing` reports the past and is exempt
#guard holds (go [pr "needsPerm", dis "c1", .permissionRevoke "perm", pr "needsPerm"])
  (.ok (.existing .dispatched) Option.none)

#guard holds (go [pr "free", .reject "c1" ⟨"s1", "c1", 0⟩ "alice"]) (.ok .none Option.none)
#guard holds (go [pr "free", .propose "c2" "free" "d1" Option.none [] [],
  .reject "c2" ⟨"s1", "c2", 0⟩ "alice", pr "free"]) (.ok (.denied .previouslyRejected) Option.none)

def granted : List EventBody :=
  [.grantCreate "g1" "alice" "gcall" (some "d1") .session 2 Option.none Option.none Option.none "rd", pr "gcall"]
#guard holds (go (granted ++ [pr "gcall"])) (.ok (.allowedByGrant "g1") Option.none)
#guard holds (go (granted ++ [.grantRevoke "g1", pr "gcall"])) (.ok (.denied .grantInvalid) Option.none)

-- escalation: theorem 11 covers repeated proposals
def escalated : List EventBody := [pr "free"] ++ fail
#guard holds (go (escalated ++ [pr "free"])) (.ok (.denied .escalated) Option.none)
#guard holds (go (escalated ++ [.escalationAck "alice" 1, pr "free"])) (.ok .allowed Option.none)
def toolScoped : Policy := { rp with limits := { maxConsecutiveFailures := some 1, escalationScope := .tool } }
#guard holds (go (escalated ++ [pr "free"]) toolScoped) (.ok (.denied .escalated) Option.none)
#guard holds (go ([pr "needsPerm"] ++ fail ++ [pr "needsPerm"]) toolScoped) (.ok .allowed Option.none)

#guard holds (go [pr "free", .kill, pr "free"]) (.ok (.denied .killed) Option.none)
#guard holds (go [pr "guarded", .kill, pr "guarded"]) (.ok (.denied .killed) Option.none)

-- guards are not compared on a repeat; a denied call keeps its denial
#guard holds (go [pr "guarded", pr "guarded" (g := [("g", true)])]) (.ok (.denied .guardFalse) Option.none)

#guard holds (go [pr "call", appr "alice", pr "call"]) (.ok .authorized Option.none)
#guard holds (go [pr "call", appr "alice", dis "c1", .result "c1" .succeeded Option.none false, pr "call"])
  (.ok (.existing .succeeded) Option.none)
#guard holds (go [pr "free", dis "c1", pr "free"]) (.ok (.existing .dispatched) Option.none)
#guard holds (go [pr "call", .cancel "c1", pr "call"]) (.ok (.existing .cancelled) Option.none)
#guard holds (go [pr "call", pr "call"]) (.ok (.needsApproval ⟨"s1", "c1", 0⟩) Option.none)

-- Review Focus 4: the edited digest matches and reports the current request id
def edited : List EventBody := [pr "q2", appr "bob" (e := some { newDigest := "d2" })]
#guard holds (go (edited ++ [pr "q2" (d := "d2")])) (.ok (.needsApproval ⟨"s1", "c1", 1⟩) Option.none)
#guard holds (go (edited ++ [pr "q2"])) (.ok (.needsApproval ⟨"s1", "c1", 1⟩) Option.none)
#guard holds (go (edited ++ [pr "q2" (d := "d9")])) (.rejected .duplicateCall)
#guard holds (go (edited ++ [.propose "c1" "call" "d2" Option.none [] []])) (.rejected .duplicateCall)

def repeated := go [pr "call", pr "call", pr "call"]
#guard repeated.1.proposalsThisTurn == 1 && repeated.1.approvalsThisTurn == 1

#guard holds (go [.permissionRevoke "perm", pr "shadow", pr "shadow"])
  (.ok .allowed (some (.wouldDeny .permissionMissing)))

-- section 6, Propose: an undefined tool leaves no record but counts toward the proposal limits
def nope : EventBody := .propose "c1" "nope" "d1" Option.none [] []
#guard ((go [nope]).1.calls.get? "c1").isNone
#guard holds (go [nope, pr "free"]) (.ok .allowed Option.none)
#guard (go [nope]).1.proposalsThisSession == 1 && (go [nope]).1.proposalsThisTurn == 1
#guard holds (go [nope, nope]) (.ok (.denied .unknownTool) Option.none)
#guard (go [nope, nope]).1.proposalsThisSession == 2
#guard holds (go [pr "free", nope]) (.rejected .duplicateCall)
#guard holds (go [.kill, nope]) (.ok (.denied .killed) Option.none)
#guard ((go [.kill, nope]).1.calls.get? "c1").isNone && (go [.kill, nope]).1.proposalsThisSession == 1
#guard holds (go [nope, dis "c1"]) (.rejected .unknownCall)

def declared : Policy := { rp with actions := rp.actions ++
  [("ge", { guards := ["g"], escalate := [("e", { consent := .perCall })] })] }
def undeclared := go [.propose "c1" "ge" "d1" Option.none [("g", true), ("junk", true)]
  [("e", false), ("other", true)]] declared
#guard holds undeclared (.ok .allowed Option.none)
#guard ((undeclared.1.calls.get? "c1").map (·.proposedGuards)) == some [("g", true)]
#guard ((undeclared.1.calls.get? "c1").map (·.proposedEscalators)) == some [("e", false)]

end Repeat

end WritTests.Propose
