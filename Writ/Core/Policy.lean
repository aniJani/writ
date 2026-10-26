namespace Writ

structure Cost where
  amount : Nat
  currency : String
  deriving DecidableEq, Repr

structure Clause where
  k : Nat
  -- `none` admits any approver role; `some []` admits nobody, so it must not collapse to `none`
  roles : Option (List String) := none
  humanOnly : Bool := true
  excludeRequester : Bool := false
  deriving DecidableEq, Repr

structure Group where
  clauses : List Clause
  distinct : Bool := false
  deriving DecidableEq, Repr

structure Consent where
  groups : List Group := []
  deriving DecidableEq, Repr

def Consent.none : Consent := {}

def Consent.quorum (k : Nat) (roles : Option (List String)) (humanOnly excludeRequester : Bool) :
    Consent :=
  ⟨[⟨[⟨k, roles, humanOnly, excludeRequester⟩], false⟩]⟩

def Consent.perCall : Consent := .quorum 1 Option.none true false

def Consent.allOf (clauses : List Clause) (distinct : Bool := false) : Consent := ⟨[⟨clauses, distinct⟩]⟩

def Consent.clauses (c : Consent) : List Clause := c.groups.flatMap (·.clauses)

/-- What a single approval (or a grant) can satisfy. -/
def Consent.single (c : Consent) : Bool :=
  c.clauses.all (·.k ≤ 1) && c.groups.all fun g => !g.distinct || g.clauses.length ≤ 1

structure Escalator where
  consent : Consent
  grantable : Bool := false
  deriving DecidableEq, Repr

inductive GrantScope where | turn | session deriving DecidableEq, Repr

def GrantScope.le : GrantScope → GrantScope → Bool
  | .turn, _ => true
  | .session, .session => true
  | .session, .turn => false

structure Grantable where
  scope : GrantScope
  maxUses : Nat
  maxDurationMs : Option Nat := none
  anyArgs : Bool := false
  allowAnyArgsMetered : Bool := false
  deriving DecidableEq, Repr

inductive Mode where | enforce | logOnly deriving DecidableEq, Repr
inductive Flag where | readsPrivate | ingestsUntrusted | sendsExternal deriving DecidableEq, Repr

structure Requirements where
  permission : Option String := none
  consent : Consent := .none
  consentIfCostOver : Option Cost := none
  escalate : List (String × Escalator) := []
  grantable : Option Grantable := none
  idempotent : Bool := false
  retryAfterUnknown : Bool := false
  maxAttempts : Nat := 1
  guards : List String := []
  meters : List String := []
  approvalTtlMs : Option Nat := none
  authorizedTtlMs : Option Nat := none
  exposed : Bool := true
  mode : Option Mode := none
  flags : List Flag := []
  deriving Repr, BEq

inductive MeterScope where | session | principal deriving DecidableEq, Repr
inductive MeterUnit where | money (currency : String) | calls deriving DecidableEq, Repr

structure MeterSpec where
  unit : MeterUnit
  cap : Option Nat := none
  scope : MeterScope := .session
  windowMs : Option Nat := none
  maxPerCall : Option Nat := none
  deriving Repr, BEq

inductive EscalationScope where | session | tool deriving DecidableEq, Repr

structure Limits where
  maxStepsPerTurn : Option Nat := none
  maxProposalsPerTurn : Option Nat := none
  maxApprovalRequestsPerTurn : Option Nat := none
  maxProposalsPerSession : Option Nat := none
  maxApprovalRequestsPerSession : Option Nat := none
  maxConsecutiveFailures : Option Nat := none
  maxFailuresPerSession : Option Nat := none
  escalationScope : EscalationScope := .session
  approvalTtlMs : Option Nat := none
  authorizedTtlMs : Option Nat := none
  deriving Repr, BEq

structure Policy where
  mode : Mode := .enforce
  approverRoles : List String := []
  escalationRoles : Option (List String) := none
  meters : List (String × MeterSpec) := []
  limits : Limits := {}
  actions : List (String × Requirements) := []
  bindingMutable : Bool := true
  killSetsTombstone : Bool := false
  deriving Repr, BEq

def Policy.action? (p : Policy) (tool : String) : Option Requirements :=
  (p.actions.find? (·.1 == tool)).map (·.2)

def Policy.meter? (p : Policy) (name : String) : Option MeterSpec :=
  (p.meters.find? (·.1 == name)).map (·.2)

def Policy.modeFor (p : Policy) (r : Requirements) : Mode := r.mode.getD p.mode

def Policy.modeOf (p : Policy) (tool : String) : Mode :=
  match p.action? tool with
  | some r => if r.exposed then p.modeFor r else .enforce
  | Option.none => .enforce

def Policy.approvalTtl (p : Policy) (r : Requirements) : Option Nat :=
  r.approvalTtlMs <|> p.limits.approvalTtlMs

def Policy.authorizedTtl (p : Policy) (r : Requirements) : Option Nat :=
  r.authorizedTtlMs <|> p.limits.authorizedTtlMs

end Writ
