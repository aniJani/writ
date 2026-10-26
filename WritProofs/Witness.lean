import WritProofs.Basic
import Writ.Author.Check

namespace Writ.Proofs.Witness

open Writ

/-- The policy of section 8's witness traces: for each reason code and each disposition, an
entry of `cases` below gives a trace whose last verdict carries it, and for each call status an
entry of `statusCases` a trace that leaves a call in it, checked by kernel evaluation. The traces are adapted from `WritTests/Witness.lean`. -/
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
    , ("retry", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 }) ]

example : wp.WF := by decide +kernel

def alice : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def alice2 : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def bob : ApproverInfo := ⟨"bob", .human, ["admin"]⟩
def bot : ApproverInfo := ⟨"reviewer-bot", .automated, ["admin"]⟩

def apprs : List (String × ApproverInfo) :=
  [("alice", alice), ("alice2", alice2), ("bob", bob), ("bot", bot)]

def start (perms : List String) : EventBody := .sessionStart "s1" "pd" "u1" perms apprs {}

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩
def rid (id : String) (g : Nat := 0) : RequestId := ⟨"s1", id, g⟩

def pr (id tool : String) (cost : Option Cost := Option.none) (d : String := "d1") : EventBody :=
  .propose id tool d cost [] []

def appr (id who : String) (g : Nat := 0) (d : String := "d1") (c : Option Cost := Option.none)
    (e : Option Edit := Option.none) : EventBody :=
  .approve id (rid id g) who d c e

def dis (id : String) (n : Nat := 1) (cost : Option Cost := Option.none) (key : String := "k1") :
    EventBody :=
  .dispatch id n "d1" cost [] key

def gc (id tool : String) : EventBody :=
  .grantCreate id "alice" tool (some "d1") .session 3 Option.none Option.none Option.none "rd"

/-- Event `i` of a trace has `seq` `i + 1` and `state_version` `i`, which is the version the
session holds when every earlier event was accepted. -/
def evs (steps : List (Nat × EventBody)) : List Event :=
  steps.zipIdx.map fun ((t, b), i) => ⟨i + 1, t, i, Option.none, b⟩

def ctx : List (Nat × EventBody) := [(0, start ["perm"]), (1, .turnStart true)]

/-- The last verdict of a trace whose earlier events were all accepted. -/
def lastOf (q : Policy) (es : List Event) : Option Verdict :=
  let vs := (run q (State.initial "pd") es).2
  if vs.dropLast.all (·.accepted) then vs.getLast? else Option.none

def w (steps : List (Nat × EventBody)) (q : Policy := wp) : Option Verdict :=
  lastOf q (evs (ctx ++ steps))

def lim (l : Limits) : Policy := { wp with limits := l }

def unknownRetry : List (Nat × EventBody) :=
  [(2, pr "c1" "retry"), (3, dis "c1"), (4, .outcomeUnknown "c1")]

/-- Each trace with the last verdict it must reach. -/
def cases : List (Option Verdict × Verdict) :=
  [ (lastOf wp [⟨1, 0, 0, Option.none, .turnEnd⟩],
      .rejected .notStarted)
  , (lastOf wp (evs ctx ++ [⟨3, 2, 2, Option.none, start []⟩]),
      .rejected .alreadyStarted)
  , (lastOf wp (evs (ctx ++ [(2, .sessionEnd)]) ++ [⟨4, 3, 3, Option.none, .turnStart true⟩]),
      .rejected .sessionEnded)
  , (lastOf wp (evs ctx ++ [⟨2, 2, 2, Option.none, .turnEnd⟩]),
      .rejected .staleSeq)
  , (lastOf wp (evs ctx ++ [⟨3, 0, 2, Option.none, .turnEnd⟩]),
      .rejected .timeDecreasing)
  , (lastOf wp (evs ctx ++ [⟨3, 2, 1, Option.none, .turnEnd⟩]),
      .rejected .stateVersionMismatch)
  , (lastOf wp (evs [(0, .sessionStart "s1" "other" "u1" [] apprs {})]),
      .rejected .policyDigestMismatch)
  , (w [(2, pr "c1" "free"), (3, pr "c1" "free" (d := "d2"))],
      .rejected .duplicateCall)
  , (w [(2, dis "nope")],
      .rejected .unknownCall)
  , (w [(2, pr "c1" "call"), (3, dis "c1")],
      .rejected .callAwaiting)
  , (w [(2, pr "c1" "free"), (3, .result "c1" .succeeded Option.none false)],
      .rejected .callAuthorized)
  , (w [(2, pr "c1" "free"), (3, dis "c1"), (4, dis "c1")],
      .rejected .callDispatched)
  , (w [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"),
      (5, .result "c1" .succeeded Option.none false)],
      .rejected .callUnknown)
  , (w [(2, pr "c1" "free"), (3, dis "c1"), (4, .result "c1" .succeeded Option.none false),
      (5, .result "c1" .succeeded Option.none false)],
      .rejected .callEnded)
  , (w [(2, pr "c1" "free"), (3, dis "c1"), (4, .outcomeUnknown "c1"), (5, dis "c1" 2)],
      .rejected .retryNotAllowed)
  , (w (unknownRetry ++ [(5, .reconcile "c1" .failed Option.none false), (6, dis "c1" 2)]),
      .rejected .alreadyReconciled)
  , (w [(2, .escalationAck "alice" 0)],
      .rejected .notEscalated)
  , (w [(2, .approverAttest "alice" ⟨"mallory", .human, ["owner"]⟩)],
      .rejected .approverChanged)
  , (w [(2, pr "c1" "call"), (3, appr "c1" "alice" (g := 1))],
      .rejected .staleRequest)
  , (w [(2, pr "c1" "call"), (3, appr "c1" "zz")],
      .rejected .unknownApprover)
  , (w [(2, pr "c1" "human"), (3, appr "c1" "bot")],
      .rejected .approverNotEligible)
  , (w [(2, pr "c1" "q2"), (3, appr "c1" "alice"), (4, appr "c1" "alice2")],
      .rejected .alreadyApproved)
  , (w [(2, pr "c1" "call"), (3, appr "c1" "alice" (d := "d2"))],
      .rejected .digestMismatch)
  , (w [(2, pr "c1" "mcall" (usd 5)), (3, appr "c1" "alice" (c := usd 6))],
      .rejected .costMismatch)
  , (w [(2, pr "c1" "call"), (3, appr "c1" "alice" (e := some { newDigest := "d2" }))]
      { wp with bindingMutable := false },
      .rejected .editNotAllowed)
  , (w [(2, gc "g1" "gcall"), (3, gc "g1" "gcall")],
      .rejected .duplicateGrant)
  , (w [(2, .grantRevoke "nope")],
      .rejected .unknownGrant)
  , (w [(2, gc "g1" "call")],
      .rejected .grantNotAllowed)
  , (w [(2, pr "c1" "free"), (3, dis "c1" 2)],
      .rejected .attemptOrder)
  , (w (unknownRetry ++ [(5, dis "c1" 2 (key := "k2"))]),
      .rejected .idempotencyKeyMismatch)
  , (w (unknownRetry ++ [(5, dis "c1" 2), (6, .outcomeUnknown "c1"), (7, dis "c1" 3)]),
      .rejected .attemptLimit)
  , (w [(2, .turnEnd), (3, .turnEnd)],
      .rejected .turnState)
  , (w [(2, .kill), (3, pr "c1" "free")],
      .ok (.denied .killed) Option.none)
  , (w [(2, pr "f" "free"), (3, dis "f"), (4, .result "f" .failed Option.none false),
      (5, pr "c1" "free")] (lim { maxConsecutiveFailures := some 1 }),
      .ok (.denied .escalated) Option.none)
  , (w [(2, pr "c1" "nope")],
      .ok (.denied .unknownTool) Option.none)
  , (w [(2, pr "c1" "hidden")],
      .ok (.denied .notExposed) Option.none)
  , (w [(2, pr "c1" "free"), (3, pr "c2" "free")] (lim { maxProposalsPerTurn := some 1 }),
      .ok (.denied .proposalLimit) Option.none)
  , (w [(2, pr "c1" "free"), (3, .turnEnd), (4, .turnStart true), (5, pr "c2" "free")]
      (lim { maxProposalsPerSession := some 1 }),
      .ok (.denied .sessionProposalLimit) Option.none)
  , (w [(2, .stepStart), (3, .stepStart)] (lim { maxStepsPerTurn := some 1 }),
      .rejected .stepLimit)
  , (w [(2, .permissionRevoke "perm"), (3, pr "c1" "needsPerm")],
      .ok (.denied .permissionMissing) Option.none)
  , (w [(2, pr "c1" "guarded")],
      .ok (.denied .guardFalse) Option.none)
  , (w [(2, pr "c1" "metered")],
      .ok (.denied .costMissing) Option.none)
  , (w [(2, pr "c1" "metered" (some ⟨1, "EUR"⟩))],
      .ok (.denied .currencyMismatch) Option.none)
  , (w [(2, pr "c1" "metered" (usd 81))],
      .ok (.denied .costAbovePerCall) Option.none)
  , (w [(2, pr "c1" "metered" (usd 80)), (3, dis "c1" (cost := usd 80)),
      (4, pr "c2" "metered" (usd 21))],
      .ok (.denied .meterExceeded) Option.none)
  , (w [(2, pr "c1" "call"), (3, .reject "c1" (rid "c1") "alice"), (4, pr "c2" "call")],
      .ok (.denied .previouslyRejected) Option.none)
  , (w [(2, pr "c1" "call"), (3, pr "c2" "call")]
      (lim { maxApprovalRequestsPerTurn := some 1 }),
      .ok (.denied .approvalBudget) Option.none)
  , (w [(2, pr "c1" "call"), (3, .turnEnd), (4, .turnStart true), (5, pr "c2" "call")]
      (lim { maxApprovalRequestsPerSession := some 1 }),
      .ok (.denied .sessionApprovalBudget) Option.none)
  , (w [(2, pr "c1" "call"), (13, appr "c1" "alice")] (lim { approvalTtlMs := some 10 }),
      .rejected .approvalExpired)
  , (w [(2, pr "c1" "free"), (13, dis "c1")] (lim { authorizedTtlMs := some 10 }),
      .ok (.dispatchDenied .authorizationExpired) Option.none)
  , (w [(2, gc "g1" "gcall"), (3, pr "c1" "gcall"), (4, .grantRevoke "g1"), (5, dis "c1")],
      .ok (.dispatchDenied .grantInvalid) Option.none)
  , (w [(2, pr "c1" "free"), (3, dis "c1"), (4, .ledgerSync {})],
      .rejected .ledgerConflict)
  , (w [(2, .stepStart)],
      .ok .none Option.none)
  , (w [(2, pr "c1" "q2"), (3, appr "c1" "alice")],
      .ok .pending Option.none)
  , (w [(2, pr "c1" "call"), (3, appr "c1" "alice")],
      .ok .authorized Option.none)
  , (w [(2, pr "c1" "free")],
      .ok .allowed Option.none)
  , (w [(2, gc "g1" "gcall"), (3, pr "c1" "gcall")],
      .ok (.allowedByGrant "g1") Option.none)
  , (w [(2, pr "c1" "call")],
      .ok (.needsApproval (rid "c1")) Option.none)
  , (w [(2, pr "c1" "free"), (3, dis "c1")],
      .ok .dispatchClaimed Option.none)
  , (w [(2, pr "c1" "free"), (3, dis "c1"), (4, pr "c1" "free")],
      .ok (.existing .dispatched) Option.none)
  , (w [(2, pr "c1" "metered" (usd 50)), (3, dis "c1" (cost := usd 50)),
      (4, .result "c1" .succeeded (some 60) false)],
      .ok (.overrun ["m"]) Option.none)
  , (w [(2, pr "c1" "guarded")] { wp with mode := .logOnly },
      .ok .allowed (some (.wouldDeny .guardFalse)))
  , (w [(2, pr "c1" "call")] { wp with mode := .logOnly },
      .ok .allowed (some .wouldNeedApproval))
  ]

example : cases.all (fun c => c.1 == some c.2) = true := by decide +kernel

def reasonOf : Verdict → Option Reason
  | .rejected r | .ok (.denied r) _ | .ok (.dispatchDenied r) _ => some r
  | _ => Option.none

/-- No wildcard, so a new `Decision` constructor breaks the build here. -/
def decisionTag : Decision → Nat
  | .none => 0 | .pending => 1 | .authorized => 2 | .allowed => 3 | .allowedByGrant _ => 4
  | .needsApproval _ => 5 | .denied _ => 6 | .dispatchClaimed => 7 | .dispatchDenied _ => 8
  | .existing _ => 9 | .overrun _ => 10

def shadowTag : Shadow → Nat
  | .wouldDeny _ => 0 | .wouldNeedApproval => 1

def reasons : List Reason := cases.filterMap (reasonOf ·.2)

def decisionTags : List Nat :=
  cases.filterMap fun c => match c.2 with | .ok d _ => some (decisionTag d) | _ => Option.none

def shadowTags : List Nat :=
  cases.filterMap fun c => match c.2 with | .ok _ (some x) => some (shadowTag x) | _ => Option.none

example : ∀ r : Reason, r ∈ reasons := by
  intro r; cases r <;> decide +kernel

example : ∀ d : Decision, decisionTag d ∈ decisionTags := by
  intro d; cases d <;> simp only [decisionTag] <;> decide +kernel

example : ∀ x : Shadow, shadowTag x ∈ shadowTags := by
  intro x; cases x <;> simp only [shadowTag] <;> decide +kernel

/-- The status call `k` holds after a trace whose events were all accepted. -/
def statusAfter (k : String) (steps : List (Nat × EventBody)) (q : Policy := wp) :
    Option CallStatus :=
  let r := run q (State.initial "pd") (evs (ctx ++ steps))
  if r.2.all (·.accepted) then r.1.calls[k]?.map (·.status) else Option.none

def finished (o : Outcome) : List (Nat × EventBody) :=
  [(2, pr "c1" "free"), (3, dis "c1"), (4, .result "c1" o Option.none false)]

/-- Section 6 also calls a call's terminal statuses dispositions: each status with a trace that
leaves call `c1` in it. -/
def statusCases : List (Option CallStatus × CallStatus) :=
  [ (statusAfter "c1" [(2, pr "c1" "guarded")], .denied .guardFalse)
  , (statusAfter "c1" [(2, pr "c1" "call")], .awaiting)
  , (statusAfter "c1" [(2, pr "c1" "free")], .authorized)
  , (statusAfter "c1" [(2, pr "c1" "free"), (3, dis "c1")], .dispatched)
  , (statusAfter "c1" (finished .succeeded), .succeeded)
  , (statusAfter "c1" (finished .failed), .failed)
  , (statusAfter "c1" (finished .declined), .declined)
  , (statusAfter "c1" unknownRetry, .unknown)
  , (statusAfter "c1" [(2, pr "c1" "call"), (3, .reject "c1" (rid "c1") "alice")], .rejected)
  , (statusAfter "c1" [(2, pr "c1" "call"), (3, .approvalExpire "c1" (rid "c1"))], .expired)
  , (statusAfter "c1"
      [(2, gc "g1" "gcall"), (3, pr "c1" "gcall"), (4, .grantRevoke "g1"), (5, dis "c1")],
      .deniedAtDispatch .grantInvalid)
  , (statusAfter "c1" [(2, pr "c1" "call"), (3, .cancel "c1")], .cancelled) ]

example : statusCases.all (fun c => c.1 == some c.2) = true := by decide +kernel

/-- No wildcard, so a new `CallStatus` constructor breaks the build here. -/
def statusTag : CallStatus → Nat
  | .denied _ => 0 | .awaiting => 1 | .authorized => 2 | .dispatched => 3 | .succeeded => 4
  | .failed => 5 | .declined => 6 | .unknown => 7 | .rejected => 8 | .expired => 9
  | .deniedAtDispatch _ => 10 | .cancelled => 11

def statusTags : List Nat := statusCases.map (statusTag ·.2)

example : ∀ st : CallStatus, statusTag st ∈ statusTags := by
  intro st; cases st <;> simp only [statusTag] <;> decide +kernel

end Writ.Proofs.Witness
