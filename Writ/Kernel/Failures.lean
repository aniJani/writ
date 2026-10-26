import Writ.Core.State

namespace Writ

def State.blocked (s : State) (tool : String) : Bool := s.escalated || tool ∈ s.blockedTools

def State.anyBlocked (s : State) : Bool := s.escalated || !s.blockedTools.isEmpty

def State.recordFailure (p : Policy) (s : State) (tool : String) : State :=
  let n := (s.failures.getD tool 0) + 1
  let total := s.failuresThisSession + 1
  let toolHit := p.limits.maxConsecutiveFailures.any (n ≥ ·)
  let (sessionHit, blockTool) := match p.limits.escalationScope with
    | .session => (toolHit, false)
    | .tool => (false, toolHit && tool ∉ s.blockedTools)
  let s := { s with
      failures := s.failures.insert tool n
      failuresThisSession := total
      escalated := s.escalated || sessionHit || p.limits.maxFailuresPerSession.any (total ≥ ·)
      blockedTools := if blockTool then s.blockedTools ++ [tool] else s.blockedTools }
  if s.anyBlocked then { s with escalations := s.escalations + 1 } else s

def State.recordSuccess (s : State) (tool : String) : State :=
  { s with failures := s.failures.insert tool 0 }

end Writ
