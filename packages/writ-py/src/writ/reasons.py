from __future__ import annotations

from typing import Final

REASONS: Final[tuple[str, ...]] = (
    "not_started", "already_started", "session_ended", "stale_seq", "time_decreasing", "state_version_mismatch",
    "policy_digest_mismatch", "duplicate_call", "unknown_call", "stale_request", "unknown_approver",
    "call_awaiting", "call_authorized", "call_dispatched", "call_unknown", "call_ended", "already_reconciled",
    "retry_not_allowed", "not_escalated", "approver_changed", "approver_not_eligible", "already_approved",
    "digest_mismatch", "cost_mismatch", "edit_not_allowed", "duplicate_grant", "unknown_grant",
    "grant_not_allowed", "attempt_order", "idempotency_key_mismatch", "attempt_limit", "turn_state", "killed",
    "escalated", "unknown_tool", "not_exposed", "proposal_limit", "step_limit", "permission_missing",
    "guard_false", "cost_missing", "currency_mismatch", "cost_above_per_call", "meter_exceeded",
    "previously_rejected", "approval_budget", "approval_expired", "authorization_expired", "grant_invalid",
    "ledger_conflict", "session_proposal_limit", "session_approval_budget",
)

RETRY_CLASSES: Final[tuple[str, ...]] = ("fix_request", "never", "after_user_action", "next_turn", "after_escalation")
