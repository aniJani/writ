import Writ.Core.State
import Writ.Core.Consent

namespace Writ

def State.eligibleFor (p : Policy) (s : State) (cl : Clause) (approverId : String) : Bool :=
  match s.approvers.get? approverId with
  | Option.none => false
  | some info =>
    info.principal != "agent" && info.roles.any (· ∈ p.approverRoles)
      && cl.roles.all (fun rs => info.roles.any (· ∈ rs))
      && (!cl.humanOnly || info.kind == .human)
      && (!cl.excludeRequester || info.principal != s.requester)

-- With no clauses there is nothing to be eligible for, so eligibility falls back to an attested
-- non-agent approver holding an approver role rather than admitting anyone.
private def eligibilityClauses (c : Consent) : List Clause :=
  if c.clauses.isEmpty then [{ k := 1, humanOnly := false }] else c.clauses

def State.eligibleAny (p : Policy) (s : State) (c : Consent) (approverId : String) : Option Reason :=
  if !s.approvers.contains approverId then some .unknownApprover
  else if (eligibilityClauses c).any (s.eligibleFor p · approverId) then Option.none
  else some .approverNotEligible

def State.eligibleAll (p : Policy) (s : State) (c : Consent) (approverId : String) : Option Reason :=
  if !s.approvers.contains approverId then some .unknownApprover
  else if (eligibilityClauses c).all (s.eligibleFor p · approverId) then Option.none
  else some .approverNotEligible

/-- Assigns each slot a distinct tally principal eligible for it, backtracking over the tally.
Each node first fails when the slots outnumber the available principals, or when some clause has
more slots left than principals eligible for it; neither can be matched, and without these checks
an unmatchable group costs a factorial number of branches. -/
private def State.assign (p : Policy) (s : State) : List Clause → List (String × String) → Bool
  | [], _ => true
  | slots@(cl :: rest), avail =>
    let principals := (avail.map (·.1)).eraseDups
    let room (c : Clause) := ((avail.filter (s.eligibleFor p c ·.2)).map (·.1)).eraseDups.length ≥ slots.count c
    slots.length ≤ principals.length && slots.all room &&
      principals.any fun who =>
        avail.any (fun (w, a) => w == who && s.eligibleFor p cl a) && s.assign p rest (avail.filter (·.1 != who))

/-- `tally` holds (principal, approver id) pairs. -/
def State.satisfied (p : Policy) (s : State) (c : Consent) (tally : List (String × String)) : Bool :=
  c.groups.all fun g =>
    if g.distinct then s.assign p (g.clauses.flatMap fun cl => List.replicate cl.k cl) tally
    else g.clauses.all fun cl =>
      ((tally.filter (s.eligibleFor p cl ·.2)).map (·.1)).eraseDups.length ≥ cl.k

end Writ
