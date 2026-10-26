import Writ.Kernel.Step.Propose
import Writ.Kernel.Eligibility

namespace Writ

def callCheck (s : State) (callId : String) (rid : RequestId) : Except Reason CallRec :=
  match s.calls.get? callId with
  | Option.none => .error .unknownCall
  | some rec =>
    if rec.status ≠ .awaiting then .error rec.status.stageReason
    else if rid ≠ ⟨s.sessionId, callId, rec.generation⟩ ∨ rec.epoch ≠ s.epoch then
      .error .staleRequest
    else .ok rec

def awaitingCheck (p : Policy) (s : State) (callId : String) (rid : RequestId) (approver : String) :
    Except Reason CallRec := do
  let rec ← callCheck s callId rid
  match s.eligibleAny p rec.consent approver with
  | some r => .error r
  | Option.none => pure rec

def editCostDenial (p : Policy) (tool : String) (newCost : Option Cost) : Option Reason :=
  (((p.action? tool).map (·.meters)).getD []).findSome? (meterShapeDenial p · newCost)

def applyApprove (p : Policy) (s : State) (time : Nat) (callId : String) (rec : CallRec)
    (approver principal : String) (reviewedDigest : String) (reviewedCost : Option Cost)
    (edit : Option Edit) : Except Reason (State × Verdict) :=
  let rejected (digest : String) : Bool := (rec.tool, digest) ∈ s.rejectedMemory
  if rejected rec.digest || edit.any (rejected ·.newDigest) then .error .previouslyRejected
  else if (p.approvalTtl ((p.action? rec.tool).getD {})).any (time ≥ rec.requestedAt + ·) then
    .error .approvalExpired
  else if reviewedDigest ≠ rec.digest then .error .digestMismatch
  else if reviewedCost ≠ rec.cost then .error .costMismatch
  else if edit.isNone && rec.tally.any (·.1 == principal) then .error .alreadyApproved
  else
    let next : Except Reason CallRec :=
      match edit with
      | some e =>
        if !p.bindingMutable then .error .editNotAllowed
        else
          match editCostDenial p rec.tool e.newCost with
          | some r => .error r
          | Option.none =>
            let r := (p.action? rec.tool).getD {}
            let cost := e.newCost <|> rec.cost
            let consent := rec.consent.join (r.effectiveConsent cost e.escalators)
            -- The editor's approval counts toward the raised consent, so it must be eligible for it.
            match s.eligibleAny p consent approver with
            | some r => .error r
            | Option.none =>
              .ok { rec with
                generation := rec.generation + 1, digest := e.newDigest, cost, consent
                generations := rec.generations ++ [(e.newDigest, cost)]
                tally := [(principal, approver)], requestedAt := time }
      | Option.none => .ok { rec with tally := rec.tally ++ [(principal, approver)] }
    match next with
    | .error r => .error r
    | .ok rec' =>
      if s.satisfied p rec'.consent rec'.tally then
        let done := { rec' with status := .authorized, authorizedAt := some time }
        .ok ({ s with calls := s.calls.insert callId done }, .ok .authorized Option.none)
      else .ok ({ s with calls := s.calls.insert callId rec' }, .ok .pending Option.none)

def handleApprove (p : Policy) (s : State) (time : Nat) (callId : String) (rid : RequestId)
    (approver reviewedDigest : String) (reviewedCost : Option Cost) (edit : Option Edit) :
    State × Verdict :=
  match awaitingCheck p s callId rid approver with
  | .error r => (s, .rejected r)
  | .ok rec =>
    let principal := ((s.approvers.get? approver).map (·.principal)).getD approver
    match applyApprove p s time callId rec approver principal reviewedDigest reviewedCost edit with
    | .error r => (s, .rejected r)
    | .ok r => r

/-- A veto may echo any generation up to the current one and still stop a call that is
authorized but not dispatched, so a slow "no" is not lost to an edit or a quorum. -/
def vetoCheck (p : Policy) (s : State) (callId : String) (rid : RequestId) (approver : String) :
    Except Reason CallRec :=
  match s.calls.get? callId with
  | Option.none => .error .unknownCall
  | some rec =>
    if !(rec.status = .awaiting ∨ (rec.status = .authorized ∧ rec.attempts = 0)) then
      .error rec.status.stageReason
    else if rid.session ≠ s.sessionId ∨ rid.call ≠ callId ∨ rid.generation > rec.generation
        ∨ rec.epoch ≠ s.epoch then .error .staleRequest
    else match s.eligibleAny p rec.consent approver with
      | some r => .error r
      | Option.none => .ok rec

def handleReject (p : Policy) (s : State) (callId : String) (rid : RequestId) (approver : String) :
    State × Verdict :=
  match vetoCheck p s callId rid approver with
  | .error r => (s, .rejected r)
  | .ok rec =>
    let add (m : List (String × String)) (d : String) :=
      if (rec.tool, d) ∈ m then m else m ++ [(rec.tool, d)]
    let echoed := (rec.generations[rid.generation]?).map (·.1)
    let memory := add (add s.rejectedMemory rec.proposedDigest) rec.digest
    ({ s.endCall callId .rejected with rejectedMemory := echoed.elim memory (add memory) },
     .ok .none Option.none)

def handleApprovalExpire (s : State) (callId : String) (rid : RequestId) : State × Verdict :=
  match callCheck s callId rid with
  | .error r => (s, .rejected r)
  | .ok _ => (s.endCall callId .expired, .ok .none Option.none)

end Writ
