import WritTests.Fixtures

open Writ

namespace WritTests.Witness

def wp : Policy where
  approverRoles := ["owner", "admin"]
  meters := [("m", { unit := .money "USD", cap := some 100, maxPerCall := some 80 })]
  actions :=
    [ ("free", {}), ("call", { consent := .perCall })
    , ("q2", { consent := .quorum 2 Option.none false false })
    , ("human", { consent := .quorum 1 Option.none true false })
    , ("metered", { meters := ["m"] })
    , ("mcall", { consent := .perCall, meters := ["m"] })
    , ("gcall", { consent := .perCall, grantable := some { scope := .session, maxUses := 3 } })
    , ("needsPerm", { permission := some "perm" })
    , ("guarded", { guards := ["g"] })
    , ("hidden", { exposed := false })
    , ("retry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 })
    , ("mretry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2
                   meters := ["m"] }) ]

#guard wp.check.isEmpty

def alice2 : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def apprs : List (String × ApproverInfo) :=
  [("alice", alice), ("alice2", alice2), ("bob", bob), ("bot", bot)]

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩
def rid (id : String) (g : Nat := 0) : RequestId := ⟨"s1", id, g⟩

def pr (id tool : String) (cost : Option Cost := Option.none) (g : List (String × Bool) := [])
    (d : String := "d1") : EventBody :=
  .propose id tool d cost g []

def appr (id who : String) (g : Nat := 0) (d : String := "d1") (c : Option Cost := Option.none)
    (e : Option Edit := Option.none) : EventBody :=
  .approve id (rid id g) who d c e

def dis (id : String) (n : Nat := 1) (d : String := "d1") (cost : Option Cost := Option.none)
    (key : String := "k1") : EventBody :=
  .dispatch id n d cost [] key

def gc (id tool : String) : EventBody :=
  .grantCreate id "alice" tool (some "d1") .session 3 Option.none Option.none Option.none "rd"

def ctx : List (Nat × EventBody) := [(0, start ["perm"] apprs), (1, .turnStart true)]

def w (steps : List (Nat × EventBody)) (p : Policy := wp) : State × List Verdict × Bool :=
  checkedScript p (ctx ++ steps)

def lim (l : Limits) : Policy := { wp with limits := l }

def raw (s : State) (seq time version : Nat) (b : EventBody) : State × Verdict :=
  step wp s ⟨seq, time, version, Option.none, b⟩

def opened : State := (w []).1
def ended : State := (w [(2, .sessionEnd)]).1

def rNotStarted := raw (State.initial "pd") 1 0 0 .turnEnd
def rAlreadyStarted := raw opened 3 2 2 (start [] [])
def rSessionEnded := raw ended 4 3 3 (.turnStart true)
def rStaleSeq := raw opened 2 2 2 .turnEnd
def rTimeDecreasing := raw opened 3 0 2 .turnEnd
def rStateVersion := raw opened 3 2 1 .turnEnd

def raws : List (State × Verdict) :=
  [rNotStarted, rAlreadyStarted, rSessionEnded, rStaleSeq, rTimeDecreasing, rStateVersion]

#guard rNotStarted.2 == .rejected .notStarted
#guard rAlreadyStarted.2 == .rejected .alreadyStarted
#guard rSessionEnded.2 == .rejected .sessionEnded
#guard rStaleSeq.2 == .rejected .staleSeq
#guard rTimeDecreasing.2 == .rejected .timeDecreasing
#guard rStateVersion.2 == .rejected .stateVersionMismatch
#guard raws.all fun (s, _) => Inv.check wp s
#guard rStaleSeq.1.version == opened.version && rStateVersion.1.version == opened.version

def wPolicyDigest := checkedScript wp [(0, start [] apprs)] "other"
def wDuplicateCall := w [(2, pr "c1" "free"), (3, pr "c1" "free" (d := "d2"))]
def wUnknownCall := w [(2, dis "nope")]
def wCallAwaiting := w [(2, pr "c1" "call"), (3, dis "c1")]
def wCallAuthorized := w [(2, pr "c1" "free"), (3, .result "c1" .succeeded Option.none false)]
def wCallDispatched := w [(2, pr "c1" "free"), (3, dis "c1"), (4, dis "c1")]
def wCallUnknown := w [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"),
  (5, .result "c1" .succeeded Option.none false)]
def wCallEnded := w [(2, pr "c1" "free"), (3, dis "c1"), (4, .result "c1" .succeeded Option.none false),
  (5, .result "c1" .succeeded Option.none false)]
def wRetryNotAllowed := w [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"), (5, dis "c1" 2)]
def wNotEscalated := w [(2, .escalationAck "alice" 0)]
def wApproverChanged := w [(2, .approverAttest "alice" ⟨"mallory", .human, ["owner"]⟩)]
def wStaleRequest := w [(2, pr "c1" "call"), (3, appr "c1" "alice" (g := 1))]
def wUnknownApprover := w [(2, pr "c1" "call"), (3, appr "c1" "zz")]
def wNotEligible := w [(2, pr "c1" "human"), (3, appr "c1" "bot")]
def wAlreadyApproved := w [(2, pr "c1" "q2"), (3, appr "c1" "alice"), (4, appr "c1" "alice2")]
def wDigestMismatch := w [(2, pr "c1" "call"), (3, appr "c1" "alice" (d := "d2"))]
def wCostMismatch := w [(2, pr "c1" "mcall" (usd 5)), (3, appr "c1" "alice" (c := usd 6))]
def wEditNotAllowed := w [(2, pr "c1" "call"), (3, appr "c1" "alice" (e := some { newDigest := "d2" }))]
  { wp with bindingMutable := false }
def wDuplicateGrant := w [(2, gc "g1" "gcall"), (3, gc "g1" "gcall")]
def wUnknownGrant := w [(2, .grantRevoke "nope")]
def wGrantNotAllowed := w [(2, gc "g1" "call")]
def wAttemptOrder := w [(2, pr "c1" "free"), (3, dis "c1" 2)]
def unknownRetry : List (Nat × EventBody) :=
  [(2, pr "c1" "retry"), (3, dis "c1"), (4, .outcomeUnknown "c1")]
def wKeyMismatch := w (unknownRetry ++ [(5, dis "c1" 2 (key := "k2"))])
def wAlreadyReconciled := w (unknownRetry ++ [(5, .reconcile "c1" .failed Option.none false), (6, dis "c1" 2)])
def wAttemptLimit := w (unknownRetry ++ [(5, dis "c1" 2), (6, .outcomeUnknown "c1"), (7, dis "c1" 3)])
def wTurnState := w [(2, .turnEnd), (3, .turnEnd)]
def wKilled := w [(2, .kill), (3, pr "c1" "free")]
def wEscalated := w [(2, pr "f" "free"), (3, dis "f"), (4, .result "f" .failed Option.none false),
  (5, pr "c1" "free")] (lim { maxConsecutiveFailures := some 1 })
def wUnknownTool := w [(2, pr "c1" "nope")]
def wNotExposed := w [(2, pr "c1" "hidden")]
def wProposalLimit := w [(2, pr "c1" "free"), (3, pr "c2" "free")] (lim { maxProposalsPerTurn := some 1 })
def wSessionProposalLimit := w [(2, pr "c1" "free"), (3, .turnEnd), (4, .turnStart true), (5, pr "c2" "free")]
  (lim { maxProposalsPerSession := some 1 })
def wStepLimit := w [(2, .stepStart), (3, .stepStart)] (lim { maxStepsPerTurn := some 1 })
def wPermissionMissing := w [(2, .permissionRevoke "perm"), (3, pr "c1" "needsPerm")]
def wGuardFalse := w [(2, pr "c1" "guarded")]
def wCostMissing := w [(2, pr "c1" "metered")]
def wCurrencyMismatch := w [(2, pr "c1" "metered" (some ⟨1, "EUR"⟩))]
def wCostAbovePerCall := w [(2, pr "c1" "metered" (usd 81))]
def wMeterExceeded := w [(2, pr "c1" "metered" (usd 80)), (3, dis "c1" (cost := usd 80)),
  (4, pr "c2" "metered" (usd 21))]
def wPreviouslyRejected := w [(2, pr "c1" "call"), (3, .reject "c1" (rid "c1") "alice"),
  (4, pr "c2" "call")]
def wApprovalBudget := w [(2, pr "c1" "call"), (3, pr "c2" "call")]
  (lim { maxApprovalRequestsPerTurn := some 1 })
def wSessionApprovalBudget := w [(2, pr "c1" "call"), (3, .turnEnd), (4, .turnStart true), (5, pr "c2" "call")]
  (lim { maxApprovalRequestsPerSession := some 1 })
def wApprovalExpired := w [(2, pr "c1" "call"), (13, appr "c1" "alice")]
  (lim { approvalTtlMs := some 10 })
def wAuthorizationExpired := w [(2, pr "c1" "free"), (13, dis "c1")]
  (lim { authorizedTtlMs := some 10 })
def wGrantInvalid := w [(2, gc "g1" "gcall"), (3, pr "c1" "gcall"), (4, .grantRevoke "g1"),
  (5, dis "c1")]
def wLedgerConflict := w [(2, pr "c1" "free"), (3, dis "c1"), (4, .ledgerSync {})]

#guard lastChecked wPolicyDigest == .rejected .policyDigestMismatch
#guard lastChecked wDuplicateCall == .rejected .duplicateCall
#guard lastChecked wUnknownCall == .rejected .unknownCall
#guard lastChecked wCallAwaiting == .rejected .callAwaiting
#guard lastChecked wCallAuthorized == .rejected .callAuthorized
#guard lastChecked wCallDispatched == .rejected .callDispatched
#guard lastChecked wCallUnknown == .rejected .callUnknown
#guard lastChecked wCallEnded == .rejected .callEnded
#guard lastChecked wRetryNotAllowed == .rejected .retryNotAllowed
#guard lastChecked wAlreadyReconciled == .rejected .alreadyReconciled
#guard lastChecked wNotEscalated == .rejected .notEscalated
#guard lastChecked wApproverChanged == .rejected .approverChanged
#guard lastChecked wStaleRequest == .rejected .staleRequest
#guard lastChecked wUnknownApprover == .rejected .unknownApprover
#guard lastChecked wNotEligible == .rejected .approverNotEligible
#guard lastChecked wAlreadyApproved == .rejected .alreadyApproved
#guard lastChecked wDigestMismatch == .rejected .digestMismatch
#guard lastChecked wCostMismatch == .rejected .costMismatch
#guard lastChecked wEditNotAllowed == .rejected .editNotAllowed
#guard lastChecked wDuplicateGrant == .rejected .duplicateGrant
#guard lastChecked wUnknownGrant == .rejected .unknownGrant
#guard lastChecked wGrantNotAllowed == .rejected .grantNotAllowed
#guard lastChecked wAttemptOrder == .rejected .attemptOrder
#guard lastChecked wKeyMismatch == .rejected .idempotencyKeyMismatch
#guard lastChecked wAttemptLimit == .rejected .attemptLimit
#guard lastChecked wTurnState == .rejected .turnState
#guard lastChecked wKilled == .ok (.denied .killed) Option.none
#guard lastChecked wEscalated == .ok (.denied .escalated) Option.none
#guard lastChecked wUnknownTool == .ok (.denied .unknownTool) Option.none
#guard lastChecked wNotExposed == .ok (.denied .notExposed) Option.none
#guard lastChecked wProposalLimit == .ok (.denied .proposalLimit) Option.none
#guard lastChecked wSessionProposalLimit == .ok (.denied .sessionProposalLimit) Option.none
#guard lastChecked wStepLimit == .rejected .stepLimit
#guard lastChecked wPermissionMissing == .ok (.denied .permissionMissing) Option.none
#guard lastChecked wGuardFalse == .ok (.denied .guardFalse) Option.none
#guard lastChecked wCostMissing == .ok (.denied .costMissing) Option.none
#guard lastChecked wCurrencyMismatch == .ok (.denied .currencyMismatch) Option.none
#guard lastChecked wCostAbovePerCall == .ok (.denied .costAbovePerCall) Option.none
#guard lastChecked wMeterExceeded == .ok (.denied .meterExceeded) Option.none
#guard lastChecked wPreviouslyRejected == .ok (.denied .previouslyRejected) Option.none
#guard lastChecked wApprovalBudget == .ok (.denied .approvalBudget) Option.none
#guard lastChecked wSessionApprovalBudget == .ok (.denied .sessionApprovalBudget) Option.none
#guard lastChecked wApprovalExpired == .rejected .approvalExpired
#guard lastChecked wAuthorizationExpired == .ok (.dispatchDenied .authorizationExpired) Option.none
#guard lastChecked wGrantInvalid == .ok (.dispatchDenied .grantInvalid) Option.none
#guard lastChecked wLedgerConflict == .rejected .ledgerConflict

def wNone := w [(2, .stepStart)]
def wPending := w [(2, pr "c1" "q2"), (3, appr "c1" "alice")]
def wAuthorized := w [(2, pr "c1" "call"), (3, appr "c1" "alice")]
def wAllowed := w [(2, pr "c1" "free")]
def wAllowedByGrant := w [(2, gc "g1" "gcall"), (3, pr "c1" "gcall")]
def wNeedsApproval := w [(2, pr "c1" "call")]
def wDispatchClaimed := w [(2, pr "c1" "free"), (3, dis "c1")]
def wExisting := w [(2, pr "c1" "free"), (3, dis "c1"), (4, pr "c1" "free")]
def wOverrun := w [(2, pr "c1" "metered" (usd 50)), (3, dis "c1" (cost := usd 50)),
  (4, .result "c1" .succeeded (some 60) false)]

#guard lastChecked wNone == .ok .none Option.none
#guard lastChecked wPending == .ok .pending Option.none
#guard lastChecked wAuthorized == .ok .authorized Option.none
#guard lastChecked wAllowed == .ok .allowed Option.none
#guard lastChecked wAllowedByGrant == .ok (.allowedByGrant "g1") Option.none
#guard lastChecked wNeedsApproval == .ok (.needsApproval (rid "c1")) Option.none
#guard lastChecked wDispatchClaimed == .ok .dispatchClaimed Option.none
#guard lastChecked wExisting == .ok (.existing .dispatched) Option.none
#guard lastChecked wOverrun == .ok (.overrun ["m"]) Option.none

def runs : List (State × List Verdict × Bool) :=
  [ wPolicyDigest, wDuplicateCall, wUnknownCall, wStaleRequest, wUnknownApprover
  , wCallAwaiting, wCallAuthorized, wCallDispatched, wCallUnknown, wCallEnded
  , wRetryNotAllowed, wAlreadyReconciled, wNotEscalated, wApproverChanged
  , wNotEligible, wAlreadyApproved, wDigestMismatch, wCostMismatch, wEditNotAllowed
  , wDuplicateGrant, wUnknownGrant, wGrantNotAllowed, wAttemptOrder, wKeyMismatch, wAttemptLimit
  , wTurnState, wKilled, wEscalated, wUnknownTool, wNotExposed, wProposalLimit, wStepLimit
  , wPermissionMissing, wGuardFalse, wCostMissing, wCurrencyMismatch, wCostAbovePerCall
  , wMeterExceeded, wPreviouslyRejected, wApprovalBudget, wApprovalExpired
  , wSessionProposalLimit, wSessionApprovalBudget
  , wAuthorizationExpired, wGrantInvalid, wLedgerConflict
  , wNone, wPending, wAuthorized, wAllowed, wAllowedByGrant, wNeedsApproval, wDispatchClaimed
  , wExisting, wOverrun ]

#guard runs.all (·.2.2)

def finals : List Verdict := runs.map lastChecked ++ raws.map (·.2)

def reasonOf : Verdict → Option Reason
  | .rejected r | .ok (.denied r) _ | .ok (.dispatchDenied r) _ => some r
  | _ => Option.none

def decisionTag : Decision → Nat
  | .none => 0 | .pending => 1 | .authorized => 2 | .allowed => 3 | .allowedByGrant _ => 4
  | .needsApproval _ => 5 | .denied _ => 6 | .dispatchClaimed => 7 | .dispatchDenied _ => 8
  | .existing _ => 9 | .overrun _ => 10

def witnessedReasons : List Reason := (finals.filterMap reasonOf).eraseDups
def witnessedDecisions : List Nat :=
  (finals.filterMap fun v => match v with | .ok d _ => some (decisionTag d) | _ => Option.none).eraseDups

#guard Reason.all.all (· ∈ witnessedReasons)
#guard Reason.all.eraseDups.length == Reason.all.length
#guard witnessedDecisions.length == 11

def grantUse := w [(2, gc "g1" "gcall"), (3, pr "c1" "gcall"), (4, dis "c1"),
  (5, .result "c1" .succeeded Option.none false), (6, pr "c2" "gcall"), (7, .cancel "c2"),
  (8, pr "c3" "gcall"), (9, dis "c3"), (10, .result "c3" .failed Option.none false),
  (11, pr "c4" "gcall"), (12, pr "c5" "gcall")]
#guard grantUse.2.2
#guard lastChecked grantUse == .ok (.needsApproval (rid "c5")) Option.none
#guard (grantUse.1.grants.get? "g1").map (fun g => (g.consumed, g.reserved)) == some (2, 1)

def quorumEdit := w [(2, pr "c1" "q2"), (3, appr "c1" "alice" (e := some { newDigest := "d2" })),
  (4, appr "c1" "bob" (g := 1) (d := "d2")), (5, dis "c1" (d := "d2")),
  (6, .result "c1" .succeeded Option.none false)]
#guard quorumEdit.2.2
#guard (quorumEdit.2.1.drop 2).all (fun v => v matches .ok _ _)

def meteredRetry := w [(2, pr "c1" "mretry" (usd 60)), (3, dis "c1" (cost := usd 60)),
  (4, .outcomeUnknown "c1"), (5, dis "c1" 2 (cost := usd 60)), (6, .outcomeUnknown "c1"),
  (7, .reconcile "c1" .succeeded (some 30) false), (8, pr "c2" "mretry" (usd 60)),
  (9, dis "c2" (cost := usd 60)), (10, .result "c2" .succeeded (some 70) false)]
#guard meteredRetry.2.2
#guard (meteredRetry.2.1.drop 2).all (fun v => v matches .ok _ _)
#guard meteredRetry.1.sessionMeters.map (fun e => e.amount + e.excess) == [30, 70]
#guard meteredRetry.1.sessionMeters.map (·.amount) == [30, 60]

def resetMidFlight := w [(2, pr "c1" "call"), (3, pr "c2" "metered" (usd 10)),
  (4, dis "c2" (cost := usd 10)), (5, gc "g1" "gcall"), (6, pr "c3" "gcall"),
  (7, pr "c4" "q2"), (8, appr "c4" "alice"), (9, .reset), (10, .reconcile "c2" .succeeded (some 10) false),
  (11, pr "c5" "call"), (12, appr "c5" "bob"), (13, dis "c5")]
#guard resetMidFlight.2.2
#guard lastChecked resetMidFlight == .ok .dispatchClaimed Option.none
#guard (resetMidFlight.1.calls.get? "c2").map (·.status) == some .unknown

def killMidFlight := w [(2, pr "c1" "mcall" (usd 5)), (3, appr "c1" "alice" (c := usd 5)),
  (4, pr "c2" "metered" (usd 20)), (5, dis "c2" (cost := usd 20)), (6, gc "g1" "gcall"),
  (7, pr "c3" "gcall"), (8, .kill), (9, .result "c2" .succeeded Option.none false),
  (10, dis "c1" (cost := usd 5)), (11, dis "c3")]
#guard killMidFlight.2.2
#guard lastChecked killMidFlight == .rejected .killed
#guard (killMidFlight.1.grants.get? "g1").map (·.reserved) == some 0

def modCall (s : State) (id : String) (f : CallRec → CallRec) : State :=
  match s.calls.get? id with
  | some c => { s with calls := s.calls.insert id (f c) }
  | Option.none => s

def authorizedCall : State := wAuthorized.1
def claimedCall : State := wDispatchClaimed.1
def grantedCall : State := wAllowedByGrant.1
def meteredCall : State := (w [(2, pr "c1" "metered" (usd 10)), (3, dis "c1" (cost := usd 10))]).1

#guard Inv.check wp authorizedCall && Inv.check wp claimedCall && Inv.check wp grantedCall
        && Inv.check wp meteredCall
#guard !Inv.check wp { authorizedCall with started := false }
#guard !Inv.check wp (modCall authorizedCall "c1" ({ · with epoch := 1 }))
#guard !Inv.check wp { claimedCall with epoch := 1 }
#guard !Inv.check wp (modCall authorizedCall "c1" ({ · with tally := [] }))
#guard !Inv.check wp (modCall authorizedCall "c1" ({ · with generations := [] }))
#guard !Inv.check wp (modCall authorizedCall "c1" ({ · with generation := 1 }))
#guard !Inv.check wp (modCall authorizedCall "c1" ({ · with digest := "d9" }))
#guard !Inv.check wp (modCall wPending.1 "c1" ({ · with tally := [("alice", "alice"), ("alice", "alice2")] }))
#guard !Inv.check wp (modCall wPending.1 "c1" ({ · with tally := [("mallory", "mallory")] }))
#guard !Inv.check wp (modCall wPending.1 "c1" ({ · with tally := [("mallory", "alice")] }))
#guard !Inv.check wp (modCall claimedCall "c1" ({ · with attempts := 0 }))
#guard !Inv.check wp (modCall claimedCall "c1" ({ · with attempts := 2 }))
#guard !Inv.check wp (modCall authorizedCall "c1" ({ · with attempts := 1 }))
#guard !Inv.check wp (modCall grantedCall "c1" ({ · with grant := Option.none }))
#guard !Inv.check wp (modCall meteredCall "c1" ({ · with status := .cancelled }))
#guard !Inv.check wp (modCall meteredCall "c1" ({ · with cost := usd 11 }))
#guard !Inv.check wp { meteredCall with sessionMeters := meteredCall.sessionMeters ++ meteredCall.sessionMeters }
#guard !Inv.check wp { meteredCall with sessionMeters := meteredCall.sessionMeters.map ({ · with call := "x" }) }

end WritTests.Witness
