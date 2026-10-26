namespace Writ

inductive Reason where
  | notStarted | alreadyStarted | sessionEnded | staleSeq | timeDecreasing
  | stateVersionMismatch | policyDigestMismatch
  | duplicateCall | unknownCall | staleRequest | unknownApprover
  | callAwaiting | callAuthorized | callDispatched | callUnknown | callEnded
  | alreadyReconciled | retryNotAllowed | notEscalated | approverChanged
  | approverNotEligible | alreadyApproved | digestMismatch | costMismatch
  | editNotAllowed | duplicateGrant | unknownGrant | grantNotAllowed | attemptOrder
  | idempotencyKeyMismatch | attemptLimit | turnState
  | killed | escalated | unknownTool | notExposed | proposalLimit | stepLimit
  | permissionMissing | guardFalse | costMissing | currencyMismatch | costAbovePerCall
  | meterExceeded | previouslyRejected | approvalBudget | approvalExpired
  | authorizationExpired | grantInvalid
  | ledgerConflict | sessionProposalLimit | sessionApprovalBudget
  deriving DecidableEq, Repr, Inhabited

inductive RetryClass where
  | fixRequest | never | afterUserAction | nextTurn | afterEscalation
  deriving DecidableEq, Repr

def Reason.retry : Reason → RetryClass
  | .notStarted | .alreadyStarted | .sessionEnded | .staleSeq | .timeDecreasing
  | .stateVersionMismatch | .policyDigestMismatch
  | .duplicateCall | .unknownCall | .staleRequest | .unknownApprover
  | .callAwaiting | .callAuthorized | .callDispatched | .callUnknown | .notEscalated
  | .approverNotEligible | .alreadyApproved | .digestMismatch | .costMismatch
  | .editNotAllowed | .duplicateGrant | .unknownGrant | .grantNotAllowed | .attemptOrder
  | .idempotencyKeyMismatch | .attemptLimit | .turnState
  | .costMissing | .currencyMismatch => .fixRequest
  | .callEnded | .alreadyReconciled | .retryNotAllowed | .approverChanged
  | .killed | .unknownTool | .notExposed | .costAbovePerCall
  | .ledgerConflict | .sessionProposalLimit | .sessionApprovalBudget => .never
  | .escalated => .afterEscalation
  | .proposalLimit | .stepLimit | .approvalBudget => .nextTurn
  | .permissionMissing | .guardFalse | .meterExceeded | .previouslyRejected
  | .approvalExpired | .authorizationExpired | .grantInvalid => .afterUserAction

def Reason.all : List Reason :=
  [ .notStarted, .alreadyStarted, .sessionEnded, .staleSeq, .timeDecreasing
  , .stateVersionMismatch, .policyDigestMismatch
  , .duplicateCall, .unknownCall, .staleRequest, .unknownApprover
  , .callAwaiting, .callAuthorized, .callDispatched, .callUnknown, .callEnded
  , .alreadyReconciled, .retryNotAllowed, .notEscalated, .approverChanged
  , .approverNotEligible, .alreadyApproved, .digestMismatch, .costMismatch
  , .editNotAllowed, .duplicateGrant, .unknownGrant, .grantNotAllowed, .attemptOrder
  , .idempotencyKeyMismatch, .attemptLimit, .turnState
  , .killed, .escalated, .unknownTool, .notExposed, .proposalLimit, .stepLimit
  , .permissionMissing, .guardFalse, .costMissing, .currencyMismatch, .costAbovePerCall
  , .meterExceeded, .previouslyRejected, .approvalBudget, .approvalExpired
  , .authorizationExpired, .grantInvalid
  , .ledgerConflict, .sessionProposalLimit, .sessionApprovalBudget ]

def Reason.code : Reason → String
  | .notStarted => "not_started"
  | .alreadyStarted => "already_started"
  | .sessionEnded => "session_ended"
  | .staleSeq => "stale_seq"
  | .timeDecreasing => "time_decreasing"
  | .stateVersionMismatch => "state_version_mismatch"
  | .policyDigestMismatch => "policy_digest_mismatch"
  | .duplicateCall => "duplicate_call"
  | .unknownCall => "unknown_call"
  | .staleRequest => "stale_request"
  | .unknownApprover => "unknown_approver"
  | .callAwaiting => "call_awaiting"
  | .callAuthorized => "call_authorized"
  | .callDispatched => "call_dispatched"
  | .callUnknown => "call_unknown"
  | .callEnded => "call_ended"
  | .alreadyReconciled => "already_reconciled"
  | .retryNotAllowed => "retry_not_allowed"
  | .notEscalated => "not_escalated"
  | .approverChanged => "approver_changed"
  | .approverNotEligible => "approver_not_eligible"
  | .alreadyApproved => "already_approved"
  | .digestMismatch => "digest_mismatch"
  | .costMismatch => "cost_mismatch"
  | .editNotAllowed => "edit_not_allowed"
  | .duplicateGrant => "duplicate_grant"
  | .unknownGrant => "unknown_grant"
  | .grantNotAllowed => "grant_not_allowed"
  | .attemptOrder => "attempt_order"
  | .idempotencyKeyMismatch => "idempotency_key_mismatch"
  | .attemptLimit => "attempt_limit"
  | .turnState => "turn_state"
  | .killed => "killed"
  | .escalated => "escalated"
  | .unknownTool => "unknown_tool"
  | .notExposed => "not_exposed"
  | .proposalLimit => "proposal_limit"
  | .stepLimit => "step_limit"
  | .permissionMissing => "permission_missing"
  | .guardFalse => "guard_false"
  | .costMissing => "cost_missing"
  | .currencyMismatch => "currency_mismatch"
  | .costAbovePerCall => "cost_above_per_call"
  | .meterExceeded => "meter_exceeded"
  | .previouslyRejected => "previously_rejected"
  | .approvalBudget => "approval_budget"
  | .approvalExpired => "approval_expired"
  | .authorizationExpired => "authorization_expired"
  | .grantInvalid => "grant_invalid"
  | .ledgerConflict => "ledger_conflict"
  | .sessionProposalLimit => "session_proposal_limit"
  | .sessionApprovalBudget => "session_approval_budget"

def Reason.ofCode? (s : String) : Option Reason := Reason.all.find? (·.code == s)

def RetryClass.code : RetryClass → String
  | .fixRequest => "fix_request" | .never => "never" | .afterUserAction => "after_user_action"
  | .nextTurn => "next_turn" | .afterEscalation => "after_escalation"

end Writ
