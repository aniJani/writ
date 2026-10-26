import Writ.Kernel.Grants

namespace Writ

def CallStatus.stageReason : CallStatus → Reason
  | .awaiting => .callAwaiting
  | .authorized => .callAuthorized
  | .dispatched => .callDispatched
  | .unknown => .callUnknown
  | .denied _ | .succeeded | .failed | .declined | .rejected | .expired | .deniedAtDispatch _
  | .cancelled => .callEnded

def State.endCall (s : State) (callId : String) (status : CallStatus) : State :=
  let s := s.releaseGrant callId
  { s with calls := s.calls.modify callId ({ · with status }) }

def cancelPending (s : State) : State :=
  s.calls.foldl (init := s) fun acc k c =>
    match c.status with
    | .awaiting | .authorized => acc.endCall k .cancelled
    | _ => acc

end Writ
