import Writ.Kernel.Step.Propose

namespace Writ

def dispatchProtocol (s : State) (r : Requirements) (rec : CallRec) (retry : Bool) (attempt : Nat)
    (digest : String) (cost : Option Cost) (key : String) : Option Reason :=
  if retry && rec.reconciled.isSome then some .alreadyReconciled
  else if retry && !r.retryAfterUnknown then some .retryNotAllowed
  else if retry && rec.epoch != s.epoch then some .staleRequest
  else if retry && decide (rec.attempts ≥ r.maxAttempts) then some .attemptLimit
  else if attempt ≠ rec.attempts + 1 then some .attemptOrder
  else if digest ≠ rec.digest then some .digestMismatch
  else if cost ≠ rec.cost then some .costMismatch
  else if rec.idempotencyKey.any (· ≠ key) then some .idempotencyKeyMismatch
  else Option.none

/-- The status is the terminal status a first attempt moves to; `none` means a transient
rejection that leaves the call as it is. -/
def dispatchDenial (p : Policy) (s : State) (time : Nat) (callId : String) (r : Requirements)
    (rec : CallRec) (retry : Bool) (guards : List (String × Bool)) : Option (Reason × Option CallStatus) :=
  match authorizedDenial p s time r rec retry with
  | some (x, status) => some (x, some status)
  | Option.none =>
    if s.blocked rec.tool then some (.escalated, Option.none)
    else if r.guards.any (lookupFlag guards · ≠ some true) then some (.guardFalse, Option.none)
    else
      let meters := if retry then s.staleMeters p time r.meters callId else r.meters
      (metersDenial p s time meters rec.cost).map (·, Option.none)

def claim (p : Policy) (s : State) (time : Nat) (callId : String) (rec : CallRec)
    (r : Requirements) (retry : Bool) (key : String) : State :=
  let s := if retry then
      (s.staleMeters p time r.meters callId).foldl (fun s m => s.retime p m callId time) s
    else
      r.meters.foldl (fun s m => s.reserve p m callId (p.callAmount m rec.cost) time)
        (s.consumeGrant callId)
  let rec' := { rec with status := .dispatched, attempts := rec.attempts + 1, idempotencyKey := some key }
  -- Two live sessions of one principal that claim from the same ledger version must not both
  -- commit (theorem 9), so a claim changes the ledger version even when it touches no principal meter.
  { s with
      calls := s.calls.insert callId rec'
      ledger := { s.ledger with version := s.ledger.version + 1 } }

def handleDispatch (p : Policy) (s : State) (time : Nat) (callId : String) (attempt : Nat)
    (digest : String) (cost : Option Cost) (guards : List (String × Bool)) (key : String) :
    State × Verdict :=
  match s.calls.get? callId with
  | Option.none => (s, .rejected .unknownCall)
  | some rec =>
    let retry := rec.status == .unknown
    let r := (p.action? rec.tool).getD {}
    if rec.status ≠ .authorized ∧ !retry then (s, .rejected rec.status.stageReason)
    else match dispatchProtocol s r rec retry attempt digest cost key with
    | some x => (s, .rejected x)
    | Option.none =>
      let terminal (x : Reason) (status : CallStatus) : State × Verdict :=
        if retry then (s, .rejected x)
        else (s.endCall callId status, .ok (.dispatchDenied x) Option.none)
      let denial := dispatchDenial p s time callId r rec retry guards
      match p.modeOf rec.tool, denial with
      | .enforce, some (x, some status) => terminal x status
      | .enforce, some (x, Option.none) => (s, .rejected x)
      | _, _ =>
        (claim p s time callId rec r retry key,
         .ok .dispatchClaimed (denial.map fun (x, _) => .wouldDeny x))

def callMeters (p : Policy) (rec : CallRec) : List String :=
  ((p.action? rec.tool).map (·.meters)).getD []

def withStatus (s : State) (callId : String) (rec : CallRec) (status : CallStatus) : State :=
  { s with calls := s.calls.insert callId { rec with status } }

def Outcome.status : Outcome → CallStatus
  | .succeeded => .succeeded
  | .failed => .failed
  | .declined => .declined

def Decision.ofOverrun (meters : List String) : Decision :=
  if meters.isEmpty then .none else .overrun meters

def handleResult (p : Policy) (s : State) (time : Nat) (callId : String) (outcome : Outcome)
    (actual : Option Nat) (noEffect : Bool) : State × Verdict :=
  match s.calls.get? callId with
  | Option.none => (s, .rejected .unknownCall)
  | some rec =>
    if rec.status ≠ .dispatched then (s, .rejected rec.status.stageReason)
    else
      let (s', over) := (withStatus s callId rec outcome.status).settle p (callMeters p rec) callId
        outcome actual noEffect time
      let s' := match outcome, over.isEmpty with
        | .failed, _ | _, false => s'.recordFailure p rec.tool
        | .succeeded, true => s'.recordSuccess rec.tool
        | .declined, true => s'
      (s', .ok (.ofOverrun over) Option.none)

def handleOutcomeUnknown (p : Policy) (s : State) (callId : String) : State × Verdict :=
  match s.calls.get? callId with
  | Option.none => (s, .rejected .unknownCall)
  | some rec =>
    if rec.status ≠ .dispatched then (s, .rejected rec.status.stageReason)
    else ((withStatus s callId rec .unknown).recordFailure p rec.tool, .ok .none Option.none)

def handleReconcile (p : Policy) (s : State) (time : Nat) (callId : String) (outcome : Outcome)
    (actual : Option Nat) (noEffect : Bool) : State × Verdict :=
  match s.calls.get? callId with
  | Option.none => (s, .rejected .unknownCall)
  | some rec =>
    if rec.status ≠ .unknown then (s, .rejected rec.status.stageReason)
    else if rec.reconciled.isSome then (s, .rejected .alreadyReconciled)
    else
      let s' := { s with calls := s.calls.insert callId { rec with reconciled := some outcome } }
      let (s', over) := s'.settle p (callMeters p rec) callId outcome actual noEffect time
      (if over.isEmpty then s' else s'.recordFailure p rec.tool, .ok (.ofOverrun over) Option.none)

def handleCancel (s : State) (callId : String) : State × Verdict :=
  match s.calls.get? callId with
  | Option.none => (s, .rejected .unknownCall)
  | some rec =>
    match rec.status with
    | .awaiting | .authorized => (s.endCall callId .cancelled, .ok .none Option.none)
    | _ => (s, .rejected rec.status.stageReason)

end Writ
