import WritProofs.Basic
import WritProofs.Envelope
import WritProofs.Dispatch
import WritProofs.Calls
import WritProofs.DefaultDeny
import WritProofs.Kill
import WritProofs.ConsentMeaning
import WritProofs.Consent
import WritProofs.Approvals
import WritProofs.AtMostOnce
import WritProofs.Meters
import WritProofs.Accounting
import WritProofs.Limits
import WritProofs.Grants
import WritProofs.Origin
import WritProofs.ConsentClaim
import WritProofs.Permission
import WritProofs.Approvers
import WritProofs.Lifecycle
import WritProofs.Escalation
import WritProofs.Rejection
import WritProofs.Interleave
import WritProofs.Accept
import WritProofs.Support
import WritProofs.Times
import WritProofs.Reports
import WritProofs.Reuse
import WritProofs.Join
import WritProofs.Expand
import WritProofs.Profile

/-- info: 'Writ.Proofs.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.frame

/-- info: 'Writ.Proofs.claimed_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claimed_dispatch

/-- info: 'Writ.Proofs.no_claimed_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.no_claimed_decision

/-- info: 'Writ.Proofs.calls_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.calls_keep

/-- info: 'Writ.Proofs.calls_tool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.calls_tool

/-- info: 'Writ.Proofs.calls_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.calls_terminal

/-- info: 'Writ.Proofs.denyInv_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.denyInv_reachable

/-- info: 'Writ.Proofs.default_deny_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.default_deny_claim

/-- info: 'Writ.Proofs.default_deny_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.default_deny_propose

/-- info: 'Writ.Proofs.default_deny_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.default_deny_status

/-- info: 'Writ.Proofs.killed_stays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.killed_stays

/-- info: 'Writ.Proofs.kill_accepted_sets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.kill_accepted_sets

/-- info: 'Writ.Proofs.no_claim_tombstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.no_claim_tombstone

/-- info: 'Writ.Proofs.no_claim_killed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.no_claim_killed

/-- info: 'Writ.Proofs.kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.kill

/-- info: 'Writ.Proofs.eligibleFor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.eligibleFor_sound

/-- info: 'Writ.Proofs.satisfied_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.satisfied_sound

/-- info: 'Writ.Proofs.consentInv_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consentInv_reachable

/-- info: 'Writ.Proofs.consent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent

/-- info: 'Writ.Proofs.approvalInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approvalInv

/-- info: 'Writ.Proofs.approvals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approvals

/-- info: 'Writ.Proofs.no_reject_before_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.no_reject_before_claim

/-- info: 'Writ.Proofs.WF.maxAttempts_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.WF.maxAttempts_pos

/-- info: 'Writ.Proofs.traceInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.traceInv

/-- info: 'Writ.Proofs.claims_need_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claims_need_call

/-- info: 'Writ.Proofs.at_most_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.at_most_once

/-- info: 'Writ.Proofs.retry_after_unknown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.retry_after_unknown

/-- info: 'Writ.Proofs.WF.window_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.WF.window_pos

/-- info: 'Writ.Proofs.WF.meters_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.WF.meters_nodup

/-- info: 'Writ.Proofs.WF.perCall_money' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.WF.perCall_money

/-- info: 'Writ.Proofs.usageAt_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.usageAt_eq

/-- info: 'Writ.Proofs.meter_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_cap

/-- info: 'Writ.Proofs.meter_cap_retry_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_cap_retry_of

/-- info: 'Writ.Proofs.meter_cap_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_cap_retry

/-- info: 'Writ.Proofs.meter_per_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_per_call

/-- info: 'Writ.Proofs.envelope_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.envelope_iff

/-- info: 'Writ.Proofs.dispatch_accepted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.dispatch_accepted_iff

/-- info: 'Writ.Proofs.dispatch_claimed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.dispatch_claimed_iff

/-- info: 'Writ.Proofs.claim_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claim_post

/-- info: 'Writ.Proofs.accounting_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accounting_reachable

/-- info: 'Writ.Proofs.committed_stays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.committed_stays

/-- info: 'Writ.Proofs.reserved_per_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.reserved_per_call

/-- info: 'Writ.Proofs.settle_commits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.settle_commits

/-- info: 'Writ.Proofs.session_entries_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.session_entries_own

/-- info: 'Writ.Proofs.accounting_session' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accounting_session

/-- info: 'Writ.Proofs.meter_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_room

/-- info: 'Writ.Proofs.meter_room_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_room_retry

/-- info: 'Writ.Proofs.no_claim_over_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.no_claim_over_cap

/-- info: 'Writ.Proofs.meter_reuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.meter_reuse

/-- info: 'Writ.Proofs.over_cap_only_by' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.over_cap_only_by

/-- info: 'Writ.Proofs.overrun_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.overrun_fails

/-- info: 'Writ.Proofs.overrun_commits_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.overrun_commits_actual

/-- info: 'Writ.Proofs.overrun_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.overrun_verdict

/-- info: 'Writ.Proofs.report_commits_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.report_commits_actual

/-- info: 'Writ.Proofs.report_commits_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.report_commits_calls

/-- info: 'Writ.Proofs.proposals_per_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.proposals_per_turn

/-- info: 'Writ.Proofs.proposals_per_session' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.proposals_per_session

/-- info: 'Writ.Proofs.approvals_per_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approvals_per_turn

/-- info: 'Writ.Proofs.approvals_per_session' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approvals_per_session

/-- info: 'Writ.Proofs.steps_per_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.steps_per_turn

/-- info: 'Writ.Proofs.grantInv_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.grantInv_reachable

/-- info: 'Writ.Proofs.grant_uses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.grant_uses

/-- info: 'Writ.Proofs.grant_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.grant_cost

/-- info: 'Writ.Proofs.retry_no_use' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.retry_no_use

/-- info: 'Writ.Proofs.grant_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.grant_origin

/-- info: 'Writ.Proofs.grant_use_returned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.grant_use_returned

/-- info: 'Writ.Proofs.grant_released_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.grant_released_all

/-- info: 'Writ.Proofs.consent_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_claim

/-- info: 'Writ.Proofs.consent_claim_fired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_claim_fired

/-- info: 'Writ.Proofs.consent_recorded_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_recorded_propose

/-- info: 'Writ.Proofs.recorded_by_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.recorded_by_propose

/-- info: 'Writ.Proofs.consent_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_recorded

/-- info: 'Writ.Proofs.call_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.call_origin

/-- info: 'Writ.Proofs.generation_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.generation_recorded

/-- info: 'Writ.Proofs.permission_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.permission_propose

/-- info: 'Writ.Proofs.permission_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.permission_claim

/-- info: 'Writ.Proofs.permission_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.permission_origin

/-- info: 'Writ.Proofs.approver_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approver_origin

/-- info: 'Writ.Proofs.requester_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.requester_origin

/-- info: 'Writ.Proofs.terminal_absorbing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.terminal_absorbing

/-- info: 'Writ.Proofs.claim_epoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claim_epoch

/-- info: 'Writ.Proofs.approve_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approve_fresh

/-- info: 'Writ.Proofs.claim_authorized_ttl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claim_authorized_ttl

/-- info: 'Writ.Proofs.claim_keeps_authorizedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claim_keeps_authorizedAt

/-- info: 'Writ.Proofs.authorizedAt_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.authorizedAt_kept

/-- info: 'Writ.Proofs.call_times' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.call_times

/-- info: 'Writ.Proofs.approve_fresh_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.approve_fresh_event

/-- info: 'Writ.Proofs.claim_authorized_ttl_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claim_authorized_ttl_event

/-- info: 'Writ.Proofs.WF.failureLimit_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.WF.failureLimit_pos

/-- info: 'Writ.Proofs.WF.sessionFailureLimit_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.WF.sessionFailureLimit_pos

/-- info: 'Writ.Proofs.escalationInv_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.escalationInv_reachable

/-- info: 'Writ.Proofs.blocked_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.blocked_propose

/-- info: 'Writ.Proofs.blocked_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.blocked_claim

/-- info: 'Writ.Proofs.unblock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.unblock

/-- info: 'Writ.Proofs.failed_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.failed_fails

/-- info: 'Writ.Proofs.failure_total_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.failure_total_step

/-- info: 'Writ.Proofs.failure_tool_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.failure_tool_step

/-- info: 'Writ.Proofs.escalations_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.escalations_step

/-- info: 'Writ.Proofs.reject_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.reject_records

/-- info: 'Writ.Proofs.memory_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.memory_persists

/-- info: 'Writ.Proofs.rejected_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.rejected_propose

/-- info: 'Writ.Proofs.rejected_approve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.rejected_approve

/-- info: 'Writ.Proofs.rejected_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.rejected_claim

/-- info: 'Writ.Proofs.memory_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.memory_origin

/-- info: 'Writ.Proofs.rejected_until_user_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.rejected_until_user_turn

/-- info: 'Writ.Proofs.interleave_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.interleave_reachable

/-- info: 'Writ.Proofs.ledger_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.ledger_cap

/-- info: 'Writ.Proofs.ledger_kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.ledger_kill

/-- info: 'Writ.Proofs.ledger_kill_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.ledger_kill_event

/-- info: 'Writ.Proofs.ledger_kill_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.ledger_kill_stored

/-- info: 'Writ.Proofs.storeLedger_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.storeLedger_eq

/-- info: 'Writ.Proofs.interleave_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.interleave_eq

/-- info: 'Writ.Proofs.disciplined_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.disciplined_eq

/-- info: 'Writ.Proofs.multi_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_reachable

/-- info: 'Writ.Proofs.multi_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_cap

/-- info: 'Writ.Proofs.multi_kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_kill

/-- info: 'Writ.Proofs.multi_kill_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_kill_event

/-- info: 'Writ.Proofs.multi_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_window

/-- info: 'Writ.Proofs.multi_cleared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_cleared

/-- info: 'Writ.Proofs.claim_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.claim_stored

/-- info: 'Writ.Proofs.multi_window_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_window_ordered

/-- info: 'Writ.Proofs.multi_kill_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.multi_kill_after

/-- info: 'Writ.Proofs.accepted_iff_sessionStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_sessionStart

/-- info: 'Writ.Proofs.accepted_iff_sessionEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_sessionEnd

/-- info: 'Writ.Proofs.accepted_iff_turnStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_turnStart

/-- info: 'Writ.Proofs.accepted_iff_turnEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_turnEnd

/-- info: 'Writ.Proofs.accepted_iff_stepStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_stepStart

/-- info: 'Writ.Proofs.accepted_iff_propose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_propose

/-- info: 'Writ.Proofs.accepted_iff_approve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_approve

/-- info: 'Writ.Proofs.accepted_iff_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_reject

/-- info: 'Writ.Proofs.accepted_iff_approvalExpire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_approvalExpire

/-- info: 'Writ.Proofs.accepted_iff_grantCreate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_grantCreate

/-- info: 'Writ.Proofs.accepted_iff_grantRevoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_grantRevoke

/-- info: 'Writ.Proofs.accepted_iff_approverAttest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_approverAttest

/-- info: 'Writ.Proofs.accepted_iff_permissionAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_permissionAdd

/-- info: 'Writ.Proofs.accepted_iff_permissionRevoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_permissionRevoke

/-- info: 'Writ.Proofs.accepted_iff_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_result

/-- info: 'Writ.Proofs.accepted_iff_outcomeUnknown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_outcomeUnknown

/-- info: 'Writ.Proofs.accepted_iff_reconcile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_reconcile

/-- info: 'Writ.Proofs.accepted_iff_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_cancel

/-- info: 'Writ.Proofs.accepted_iff_escalationAck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_escalationAck

/-- info: 'Writ.Proofs.accepted_iff_ledgerSync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_ledgerSync

/-- info: 'Writ.Proofs.accepted_iff_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_reset

/-- info: 'Writ.Proofs.accepted_iff_kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_iff_kill

/-- info: 'Writ.Proofs.Policy.WF.facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.Policy.WF.facts

/-- info: 'Writ.Proofs.origin_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.origin_independent

/-- info: 'Writ.Proofs.accepted_seq_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.accepted_seq_time

/-- info: 'Writ.Proofs.trace_seq_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.trace_seq_time

/-- info: 'Writ.Proofs.wellFormed_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.wellFormed_reachable

/-- info: 'Writ.Proofs.consent_le_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_le_refl

/-- info: 'Writ.Proofs.consent_le_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_le_trans

/-- info: 'Writ.Proofs.consent_none_le' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.consent_none_le

/-- info: 'Writ.Proofs.consent_join_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_join_nodup

/-- info: 'Writ.Proofs.consent_mem_join' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_mem_join

/-- info: 'Writ.Proofs.consent_le_join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_le_join_left

/-- info: 'Writ.Proofs.consent_le_join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_le_join_right

/-- info: 'Writ.Proofs.consent_join_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_join_le

/-- info: 'Writ.Proofs.consent_join_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_join_comm

/-- info: 'Writ.Proofs.consent_join_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.consent_join_assoc

/-- info: 'Writ.Proofs.consent_join_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.consent_join_idem

/-- info: 'Writ.Proofs.grant_le_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.grant_le_refl

/-- info: 'Writ.Proofs.grant_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.grant_le_trans

/-- info: 'Writ.Proofs.grant_le_join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_le_join_left

/-- info: 'Writ.Proofs.grant_le_join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_le_join_right

/-- info: 'Writ.Proofs.grant_join_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_join_le

/-- info: 'Writ.Proofs.grant_join_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_join_comm

/-- info: 'Writ.Proofs.grant_join_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_join_assoc

/-- info: 'Writ.Proofs.grant_join_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_join_idem

/-- info: 'Writ.Proofs.grant_le_apply' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.grant_le_apply

/-- info: 'Writ.Proofs.cap_le_apply' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cap_le_apply

/-- info: 'Writ.Proofs.cap_apply_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cap_apply_le

/-- info: 'Writ.Proofs.cap_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.cap_le_trans

/-- info: 'Writ.Proofs.bool_le_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_le_refl

/-- info: 'Writ.Proofs.bool_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_le_trans

/-- info: 'Writ.Proofs.bool_le_join_left' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_le_join_left

/-- info: 'Writ.Proofs.bool_le_join_right' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_le_join_right

/-- info: 'Writ.Proofs.bool_join_le' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_join_le

/-- info: 'Writ.Proofs.bool_join_comm' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_join_comm

/-- info: 'Writ.Proofs.bool_join_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_join_assoc

/-- info: 'Writ.Proofs.bool_join_idem' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.bool_join_idem

/-- info: 'Writ.Proofs.mode_le_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.mode_le_refl

/-- info: 'Writ.Proofs.mode_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.mode_le_trans

/-- info: 'Writ.Proofs.mode_le_join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.mode_le_join_left

/-- info: 'Writ.Proofs.mode_le_join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.mode_le_join_right

/-- info: 'Writ.Proofs.mode_join_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.mode_join_le

/-- info: 'Writ.Proofs.mode_join_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.mode_join_comm

/-- info: 'Writ.Proofs.mode_join_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.mode_join_assoc

/-- info: 'Writ.Proofs.mode_join_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.mode_join_idem

/-- info: 'Writ.Proofs.list_le_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.list_le_refl

/-- info: 'Writ.Proofs.list_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.list_le_trans

/-- info: 'Writ.Proofs.guard_le_join_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_le_join_left

/-- info: 'Writ.Proofs.guard_le_join_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_le_join_right

/-- info: 'Writ.Proofs.guard_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_join_le

/-- info: 'Writ.Proofs.guard_join_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_join_nodup

/-- info: 'Writ.Proofs.guard_join_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_join_comm

/-- info: 'Writ.Proofs.guard_join_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_join_assoc

/-- info: 'Writ.Proofs.guard_join_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.guard_join_idem

/-- info: 'Writ.Proofs.flag_le_join_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_le_join_left

/-- info: 'Writ.Proofs.flag_le_join_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_le_join_right

/-- info: 'Writ.Proofs.flag_join_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_join_le

/-- info: 'Writ.Proofs.flag_join_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_join_nodup

/-- info: 'Writ.Proofs.flag_join_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_join_comm

/-- info: 'Writ.Proofs.flag_join_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_join_assoc

/-- info: 'Writ.Proofs.flag_join_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.flag_join_idem

/-- info: 'Writ.Proofs.escLe_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.escLe_iff

/-- info: 'Writ.Proofs.esc_le_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.esc_le_refl

/-- info: 'Writ.Proofs.esc_le_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_le_trans

/-- info: 'Writ.Proofs.esc_le_join_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_le_join_left

/-- info: 'Writ.Proofs.esc_le_join_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_le_join_right

/-- info: 'Writ.Proofs.esc_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_join_le

/-- info: 'Writ.Proofs.esc_join_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_join_comm

/-- info: 'Writ.Proofs.esc_join_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_join_assoc

/-- info: 'Writ.Proofs.esc_join_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.esc_join_idem

/-- info: 'Writ.Proofs.cost_le_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.cost_le_refl

/-- info: 'Writ.Proofs.cost_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.cost_le_trans

/-- info: 'Writ.Proofs.cost_le_join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cost_le_join_left

/-- info: 'Writ.Proofs.cost_le_join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cost_le_join_right

/-- info: 'Writ.Proofs.cost_join_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cost_join_le

/-- info: 'Writ.Proofs.cost_join_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cost_join_comm

/-- info: 'Writ.Proofs.cost_join_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cost_join_assoc

/-- info: 'Writ.Proofs.cost_join_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.cost_join_idem

/-- info: 'Writ.Proofs.attempts_le_join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.attempts_le_join_left

/-- info: 'Writ.Proofs.attempts_le_join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.attempts_le_join_right

/-- info: 'Writ.Proofs.attempts_join_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.attempts_join_le

/-- info: 'Writ.Proofs.attempts_join_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.attempts_join_comm

/-- info: 'Writ.Proofs.attempts_join_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.attempts_join_assoc

/-- info: 'Writ.Proofs.attempts_join_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.attempts_join_idem

/-- info: 'Writ.Proofs.ttl_le_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.ttl_le_refl

/-- info: 'Writ.Proofs.ttl_le_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Writ.Proofs.ttl_le_trans

/-- info: 'Writ.Proofs.ttl_le_join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.ttl_le_join_left

/-- info: 'Writ.Proofs.ttl_le_join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.ttl_le_join_right

/-- info: 'Writ.Proofs.ttl_join_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.ttl_join_le

/-- info: 'Writ.Proofs.ttl_join_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.ttl_join_comm

/-- info: 'Writ.Proofs.ttl_join_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.ttl_join_assoc

/-- info: 'Writ.Proofs.ttl_join_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.ttl_join_idem

/-- info: 'Writ.Proofs.req_le_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Writ.Proofs.req_le_refl

/-- info: 'Writ.Proofs.req_le_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.req_le_trans

/-- info: 'Writ.Proofs.req_le_joinStrict_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.req_le_joinStrict_left

/-- info: 'Writ.Proofs.req_le_joinStrict_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.req_le_joinStrict_right

/-- info: 'Writ.Proofs.joinStrict_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinStrict_le

/-- info: 'Writ.Proofs.joinStrict_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinStrict_comm

/-- info: 'Writ.Proofs.joinStrict_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinStrict_assoc

/-- info: 'Writ.Proofs.joinStrict_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinStrict_idem

/-- info: 'Writ.Proofs.joinStrict_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinStrict_mono

/-- info: 'Writ.Proofs.require_le_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.require_le_trans

/-- info: 'Writ.Proofs.req_le_joinReq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.req_le_joinReq

/-- info: 'Writ.Proofs.require_le_joinReq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.require_le_joinReq

/-- info: 'Writ.Proofs.joinReq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinReq_le

/-- info: 'Writ.Proofs.joinReq_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinReq_mono

/-- info: 'Writ.Proofs.joinReq_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinReq_swap

/-- info: 'Writ.Proofs.joinReq_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.joinReq_idem

/-- info: 'Writ.Proofs.expand_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_check

/-- info: 'Writ.Proofs.expand_actions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_actions

/-- info: 'Writ.Proofs.expand_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_explicit

/-- info: 'Writ.Proofs.expand_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_rule

/-- info: 'Writ.Proofs.expand_rule_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_rule_resolved

/-- info: 'Writ.Proofs.expand_rule_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_rule_checked

/-- info: 'Writ.Proofs.expand_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_mono

/-- info: 'Writ.Proofs.expand_mono_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_mono_resolved

/-- info: 'Writ.Proofs.expand_mono_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_mono_checked

/-- info: 'Writ.Proofs.expand_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_parent

/-- info: 'Writ.Proofs.expand_parent_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.expand_parent_checked

/-- info: 'Writ.Proofs.profile_unknown_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Writ.Proofs.profile_unknown_final
