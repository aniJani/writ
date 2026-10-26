import Writ.Kernel.Step.Session
import Writ.Kernel.Step.Propose
import Writ.Kernel.Step.Approve
import Writ.Kernel.Step.Grant
import Writ.Kernel.Step.Dispatch
import Writ.Kernel.Step.Control

namespace Writ

def stepEnvelope (s : State) (e : Event) : Option Reason :=
  let isStart := match e.body with | .sessionStart .. => true | _ => false
  let settles := match e.body with | .reconcile .. | .ledgerSync _ => true | _ => false
  let openWhenKilled := match e.body with
    | .propose .. | .kill | .sessionEnd | .result .. | .outcomeUnknown _ | .reconcile ..
    | .ledgerSync _ => true
    | _ => false
  if !s.started && !isStart then some .notStarted
  else if s.ended && !settles then some .sessionEnded
  else if s.started && isStart then some .alreadyStarted
  else if e.seq ≤ s.lastSeq then some .staleSeq
  else if e.time < s.lastTime then some .timeDecreasing
  else if e.stateVersion ≠ s.version then some .stateVersionMismatch
  else if (s.killed || s.ledger.tombstone) && !openWhenKilled then some .killed
  else Option.none

def stepHandle (p : Policy) (s : State) (e : Event) : State × Verdict :=
  match e.body with
  | .sessionStart id pd req perms apprs led => handleSessionStart s id pd req perms apprs led
  | .sessionEnd => handleSessionEnd s
  | .turnStart u => handleTurnStart s u
  | .turnEnd => handleTurnEnd s
  | .stepStart => handleStepStart p s
  | .approverAttest a i => handleApproverAttest s a i
  | .permissionRevoke perm => handlePermissionRevoke s perm
  | .propose id tool digest cost guards escalators =>
    handlePropose p s e.time id tool digest cost guards escalators
  | .approve id rid who d c edit => handleApprove p s e.time id rid who d c edit
  | .reject id rid who => handleReject p s id rid who
  | .approvalExpire id rid => handleApprovalExpire s id rid
  | .grantCreate gid who tool digest scope n mc nb exp rev =>
    handleGrantCreate p s e.time gid who tool digest scope n mc nb exp rev
  | .grantRevoke gid => handleGrantRevoke s gid
  | .dispatch id n digest cost guards key => handleDispatch p s e.time id n digest cost guards key
  | .result id o actual noEffect => handleResult p s e.time id o actual noEffect
  | .outcomeUnknown id => handleOutcomeUnknown p s id
  | .reconcile id o actual noEffect => handleReconcile p s e.time id o actual noEffect
  | .cancel id => handleCancel s id
  | .reset => handleReset s
  | .kill => handleKill p s
  | .permissionAdd perm who => handlePermissionAdd p s perm who
  | .escalationAck who n => handleEscalationAck p s who n
  | .ledgerSync l => handleLedgerSync s l

def step (p : Policy) (s : State) (e : Event) : State × Verdict :=
  match stepEnvelope s e with
  | some r => (s, .rejected r)
  | Option.none =>
    match stepHandle p s e with
    | (s', v@(.ok _ _)) =>
      ({ s' with lastSeq := e.seq, lastTime := e.time, version := s.version + 1 }, v)
    | (_, v) => (s, v)

end Writ
