import Writ.Codec.Verdict

/-! The MCP SEP-2848 profile: SEP-2848 dispositions for call statuses, SEP-2643 denial envelopes
for verdicts, and the policy settings that break SEP-2848's rules. Only `Writ.Api` and the CLI
import it, so SEP terms stay out of the kernel while the drafts change. -/

namespace Writ.Profile.McpToolApproval

open Writ

def id : String := "mcp-tool-approval"

/-- The SEP-2848 string for a terminal status (`docs/design.md`, section 6), none while the call
can still move. `cancelled` is SEP-2663's task status, which SEP-2848 uses for a cancelled task. -/
def disposition : CallStatus → Option String
  | .succeeded => some "approved-executed"
  | .denied _ | .rejected | .expired | .deniedAtDispatch _ | .declined => some "denied-not-executed"
  | .failed => some "execution-error"
  | .unknown => some "outcome-unknown"
  | .cancelled => some "cancelled"
  | .awaiting | .authorized | .dispatched => none

/-- SEP-2643's `reason`; the draft defines this one value. -/
def denialReason : String := "insufficient_authorization"

/-- A denial discloses its code, its retry class and its reviewed model message, nothing else. -/
def denial (r : Reason) : Json :=
  .obj #[("reason", .str denialReason), ("remediation", .str "unavailable"),
    ("code", .str r.code), ("retry", .str r.retry.code), ("message", .str r.modelMessage)]

def pending (rid : RequestId) : Json :=
  .obj #[("reason", .str denialReason), ("remediation", .str "available"),
    ("remediationHints", .arr #[.obj #[("type", .str "task")]]), ("requestId", toJson rid)]

def envelope : Verdict → Option Json
  | .ok (.needsApproval rid) _ => some (pending rid)
  | .ok (.denied r) _ | .ok (.dispatchDenied r) _ | .rejected r => some (denial r)
  | .ok _ _ => none

inductive Problem where
  | retryAfterUnknown (action : String)
  | maxAttempts (action : String)
  deriving DecidableEq, Repr

def Problem.isError : Problem → Bool
  | .retryAfterUnknown _ => true
  | .maxAttempts _ => false

def Problem.code : Problem → String
  | .retryAfterUnknown _ => "profile_retry_after_unknown"
  | .maxAttempts _ => "profile_max_attempts"

def Problem.action? : Problem → Option String
  | .retryAfterUnknown a | .maxAttempts a => some a

def Problem.message : Problem → String
  | .retryAfterUnknown _ =>
    "retry_after_unknown is true, but under SEP-2848 outcome-unknown is final: a call whose outcome is unknown must never run again"
  | .maxAttempts _ =>
    "max_attempts is above 1 without retry_after_unknown, so it has no effect: under SEP-2848 a call runs at most once"

def problems (p : Policy) : List Problem :=
  p.actions.flatMap fun (name, r) =>
    if r.retryAfterUnknown then [.retryAfterUnknown name]
    else if r.maxAttempts > 1 then [.maxAttempts name]
    else []

def errors (p : Policy) : List Problem := (problems p).filter (·.isError)

end Writ.Profile.McpToolApproval
