import Writ.Core.Policy

namespace Writ

def Consent.join (a b : Consent) : Consent :=
  ⟨(a.groups ++ b.groups).foldl (fun acc g => if g ∈ acc then acc else acc ++ [g]) []⟩

/-- A missing escalator counts as fired. -/
def Requirements.fired (r : Requirements) (escalators : List (String × Bool)) : List Escalator :=
  (r.escalate.filter fun (name, _) => escalators.lookup name != some false).map (·.2)

def Requirements.effectiveConsent (r : Requirements) (cost : Option Cost)
    (escalators : List (String × Bool)) : Consent :=
  let base : Consent :=
    match r.consentIfCostOver, cost with
    | some t, some c => if c.currency = t.currency ∧ c.amount < t.amount then .none else r.consent
    | _, _ => r.consent
  (r.fired escalators).foldl (fun acc e => acc.join e.consent) base

def Requirements.firedGrantable (r : Requirements) (escalators : List (String × Bool)) : Bool :=
  (r.fired escalators).all (·.grantable)

/-- Everything a grant may stand in for: the base consent and every grantable escalator. -/
def Requirements.grantConsent (r : Requirements) : Consent :=
  (r.escalate.filter (·.2.grantable)).foldl (fun acc (_, e) => acc.join e.consent) r.consent

end Writ
