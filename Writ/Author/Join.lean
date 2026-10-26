import Writ.Author.Layer2
import Writ.Core.Consent

/-!
The strictness orders and joins of layer 2. Every order `le a b` reads "`b` is at least as strict
as `a`", and every join is the least strict value at least as strict as both arguments.
-/

namespace Writ

/-- `none` admits every approver role, so it is the least strict role set. -/
def RolesLe : Option (List String) → Option (List String) → Prop
  | none, _ => True
  | some _, none => False
  | some xs, some ys => ∀ r ∈ ys, r ∈ xs

instance : (a b : Option (List String)) → Decidable (RolesLe a b)
  | none, _ => isTrue trivial
  | some _, none => isFalse id
  | some xs, some ys => inferInstanceAs (Decidable (∀ r ∈ ys, r ∈ xs))

def Clause.le (x y : Clause) : Prop :=
  x.k ≤ y.k ∧ RolesLe x.roles y.roles ∧ (x.humanOnly = true → y.humanOnly = true) ∧
    (x.excludeRequester = true → y.excludeRequester = true)

instance (x y : Clause) : Decidable (x.le y) := by unfold Clause.le; infer_instance

/-- Each clause of `xs` is implied by a different clause of `ys`. -/
def Clause.Matches : List Clause → List Clause → Prop
  | [], _ => True
  | x :: xs, ys => ∃ y ∈ ys, x.le y ∧ Clause.Matches xs (ys.erase y)

instance Clause.decMatches : (xs ys : List Clause) → Decidable (Clause.Matches xs ys)
  | [], _ => isTrue trivial
  | x :: xs, ys =>
    have := fun y => Clause.decMatches xs (ys.erase y)
    inferInstanceAs (Decidable (∃ y ∈ ys, x.le y ∧ Clause.Matches xs (ys.erase y)))

/-- A `distinct` group needs distinct principals for its clauses, so its clauses must be implied
by different clauses of the stricter group; otherwise one clause may imply several. -/
def Group.le (g h : Group) : Prop :=
  (g.distinct = true → h.distinct = true) ∧
    (g.distinct = true → Clause.Matches g.clauses h.clauses) ∧
    ∀ x ∈ g.clauses, ∃ y ∈ h.clauses, x.le y

instance (g h : Group) : Decidable (g.le h) := by unfold Group.le; infer_instance

/-- Every group of `c` is implied by some group of `d`; `Consent.none` is the bottom. The join is
the existing `Consent.join`: the union of groups, equal groups kept once. -/
def Consent.le (c d : Consent) : Prop := ∀ g ∈ c.groups, ∃ h ∈ d.groups, g.le h

instance (c d : Consent) : Decidable (c.le d) := by unfold Consent.le; infer_instance

/-- `false` is stricter. The join is `&&`. -/
abbrev BoolLe (a b : Bool) : Prop := b = true → a = true

abbrev ListLe (a b : List α) : Prop := ∀ x ∈ a, x ∈ b

/-- The union of `a` and `b` in first-occurrence order, equal elements kept once. -/
def listJoin [DecidableEq α] (a b : List α) : List α :=
  (a ++ b).foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

def guardJoin (a b : List String) : List String :=
  (listJoin a b).mergeSort fun x y => decide (x ≤ y)

/-- Alphabetical by the JSON spelling. -/
def Flag.rank : Flag → Nat
  | .ingestsUntrusted => 0
  | .readsPrivate => 1
  | .sendsExternal => 2

def flagJoin (a b : List Flag) : List Flag :=
  (listJoin a b).mergeSort fun x y => decide (x.rank ≤ y.rank)

/-- An action's `none` mode takes the policy's mode, so it sits between `log_only` and `enforce`
whatever that mode is. -/
def modeRank : Option Mode → Nat
  | some .logOnly => 0
  | none => 1
  | some .enforce => 2

abbrev ModeLe (a b : Option Mode) : Prop := modeRank a ≤ modeRank b

def modeJoin : Option Mode → Option Mode → Option Mode
  | some .enforce, _ | _, some .enforce => some .enforce
  | none, _ | _, none => none
  | some .logOnly, some .logOnly => some .logOnly

/-- A duration or count limit, `none` meaning unlimited: `b` is at most `a`. -/
def DurLe : Option Nat → Option Nat → Prop
  | none, _ => True
  | some _, none => False
  | some m, some n => n ≤ m

instance : (a b : Option Nat) → Decidable (DurLe a b)
  | none, _ => isTrue trivial
  | some _, none => isFalse id
  | some m, some n => inferInstanceAs (Decidable (n ≤ m))

def durMeet : Option Nat → Option Nat → Option Nat
  | none, d => d
  | some m, none => some m
  | some m, some n => some (min m n)

def scopeMeet : GrantScope → GrantScope → GrantScope
  | .session, .session => .session
  | _, _ => .turn

/-- `turn` is stricter than `session`, smaller limits are stricter, `false` flags are stricter. -/
def Grantable.le (a b : Grantable) : Prop :=
  GrantScope.le b.scope a.scope = true ∧ b.maxUses ≤ a.maxUses ∧
    DurLe a.maxDurationMs b.maxDurationMs ∧ BoolLe a.anyArgs b.anyArgs ∧
    BoolLe a.allowAnyArgsMetered b.allowAnyArgsMetered

instance (a b : Grantable) : Decidable (a.le b) := by unfold Grantable.le; infer_instance

def Grantable.meet (a b : Grantable) : Grantable where
  scope := scopeMeet a.scope b.scope
  maxUses := min a.maxUses b.maxUses
  maxDurationMs := durMeet a.maxDurationMs b.maxDurationMs
  anyArgs := a.anyArgs && b.anyArgs
  allowAnyArgsMetered := a.allowAnyArgsMetered && b.allowAnyArgsMetered

/-- An absent `grantable` is the strictest. -/
def GrantLe : Option Grantable → Option Grantable → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a.le b

instance : (a b : Option Grantable) → Decidable (GrantLe a b)
  | _, none => isTrue trivial
  | none, some _ => isFalse id
  | some a, some b => inferInstanceAs (Decidable (a.le b))

def grantJoin : Option Grantable → Option Grantable → Option Grantable
  | some a, some b => some (a.meet b)
  | _, _ => none

def Grantable.capBy (x : Grantable) (scope : Option GrantScope) (maxUses maxDurationMs : Option Nat)
    (anyArgs : Option Bool) : Grantable :=
  { x with
    scope := match scope with
      | none => x.scope
      | some s => scopeMeet x.scope s
    maxUses := match maxUses with
      | none => x.maxUses
      | some n => min x.maxUses n
    maxDurationMs := durMeet x.maxDurationMs maxDurationMs
    anyArgs := x.anyArgs && anyArgs.getD true }

def GrantCap.apply : GrantCap → Option Grantable → Option Grantable
  | .forbid, _ => none
  | .cap s u d a, g => g.map (·.capBy s u d a)

/-- `g` is within the cap. -/
def GrantCap.le : GrantCap → Option Grantable → Prop
  | .forbid, g => g = none
  | .cap .., none => True
  | .cap s u d a, some x =>
    (s.all fun t => GrantScope.le x.scope t) = true ∧ DurLe u (some x.maxUses) ∧
      DurLe d x.maxDurationMs ∧ BoolLe (a.getD true) x.anyArgs

instance : (c : GrantCap) → (g : Option Grantable) → Decidable (c.le g)
  | .forbid, g => inferInstanceAs (Decidable (g = none))
  | .cap .., none => isTrue trivial
  | .cap s u d a, some x => inferInstanceAs (Decidable
      ((s.all fun t => GrantScope.le x.scope t) = true ∧ DurLe u (some x.maxUses) ∧
        DurLe d x.maxDurationMs ∧ BoolLe (a.getD true) x.anyArgs))

/-- A missing `consent_if_cost_over` always asks for consent, so it is the strictest; a lower
threshold in the same currency is stricter, and thresholds in different currencies are unordered. -/
def CostLe : Option Cost → Option Cost → Prop
  | _, none => True
  | none, some _ => False
  | some x, some y => x.currency = y.currency ∧ y.amount ≤ x.amount

instance : (a b : Option Cost) → Decidable (CostLe a b)
  | _, none => isTrue trivial
  | none, some _ => isFalse id
  | some x, some y => inferInstanceAs (Decidable (x.currency = y.currency ∧ y.amount ≤ x.amount))

def costJoin : Option Cost → Option Cost → Option Cost
  | some x, some y => if x.currency = y.currency then some ⟨min x.amount y.amount, x.currency⟩ else none
  | _, _ => none

/-- A fired escalator joins its consent in, and a grant stands in only if it is grantable, so more
consent and `grantable` false are stricter. -/
def Escalator.le (e f : Escalator) : Prop := e.consent.le f.consent ∧ BoolLe e.grantable f.grantable

instance (e f : Escalator) : Decidable (e.le f) := by unfold Escalator.le; infer_instance

def Escalator.join (e f : Escalator) : Escalator := ⟨e.consent.join f.consent, e.grantable && f.grantable⟩

/-- What every escalator of `l` named `n` adds when it fires: nothing, and grantable, when none
is named `n`. -/
def escAt (l : List (String × Escalator)) (n : String) : Escalator :=
  (l.filter (·.1 == n)).foldl (fun acc p => acc.join p.2) ⟨.none, true⟩

/-- Every reason of `a` adds at most what it adds in `b`; a reason only in `b` adds more, so
more escalators are stricter (spec: escalators only raise strictness). Stated over `a`'s reasons
to be decidable; `escLe_iff` in the proofs gives the reading over every reason. -/
def EscLe (a b : List (String × Escalator)) : Prop :=
  ∀ n ∈ a.map (·.1), (escAt a n).le (escAt b n)

instance (a b : List (String × Escalator)) : Decidable (EscLe a b) := by
  unfold EscLe; infer_instance

/-- The union by reason; a reason in both gets both consents and is grantable only if both are. -/
def escJoin (a b : List (String × Escalator)) : List (String × Escalator) :=
  (listJoin (a.map (·.1)) (b.map (·.1))).map fun n => (n, (escAt a n).join (escAt b n))

/-- Compares every field but `permission` and `meters` (spec theorem 13) and the display-only
`review` and `messages`, which `Requirements` does not hold. Rules set only the fields up to `mode`;
`consent_if_cost_over`, `escalate`, `max_attempts` and the TTLs join only across the files that
name an action. The TTL join is the min over the TTLs files write: a file that writes none
expresses no opinion, and the action then defers to the leaf's policy-level limit, which the leaf
owns. -/
def Requirements.le (a b : Requirements) : Prop :=
  a.consent.le b.consent ∧ GrantLe a.grantable b.grantable ∧ BoolLe a.exposed b.exposed ∧
    BoolLe a.idempotent b.idempotent ∧ BoolLe a.retryAfterUnknown b.retryAfterUnknown ∧
    ListLe a.guards b.guards ∧ ListLe a.flags b.flags ∧ ModeLe a.mode b.mode ∧
    CostLe a.consentIfCostOver b.consentIfCostOver ∧ EscLe a.escalate b.escalate ∧
    b.maxAttempts ≤ a.maxAttempts ∧ DurLe a.approvalTtlMs b.approvalTtlMs ∧
    DurLe a.authorizedTtlMs b.authorizedTtlMs

instance (a b : Requirements) : Decidable (a.le b) := by unfold Requirements.le; infer_instance

/-- The join of every field `Requirements.le` compares; `permission` and `meters` are `a`'s. -/
def Requirements.joinStrict (a b : Requirements) : Requirements :=
  { a with
    consent := a.consent.join b.consent
    grantable := grantJoin a.grantable b.grantable
    exposed := a.exposed && b.exposed
    idempotent := a.idempotent && b.idempotent
    retryAfterUnknown := a.retryAfterUnknown && b.retryAfterUnknown
    guards := guardJoin a.guards b.guards
    flags := flagJoin a.flags b.flags
    mode := modeJoin a.mode b.mode
    consentIfCostOver := costJoin a.consentIfCostOver b.consentIfCostOver
    escalate := escJoin a.escalate b.escalate
    maxAttempts := min a.maxAttempts b.maxAttempts
    approvalTtlMs := durMeet a.approvalTtlMs b.approvalTtlMs
    authorizedTtlMs := durMeet a.authorizedTtlMs b.authorizedTtlMs }

/-- `a` joined with a rule's requirements. A field the rule leaves unset is unconstrained:
consent and `grantable` stay `a`'s, a Bool joins with `true`, a mode with `log_only`. -/
def Requirements.joinReq (a : Requirements) (r : Require) : Requirements :=
  { a with
    consent := match r.consent with
      | none => a.consent
      | some c => a.consent.join c
    grantable := match r.grantable with
      | none => a.grantable
      | some c => c.apply a.grantable
    exposed := a.exposed && r.exposed.getD true
    idempotent := a.idempotent && r.idempotent.getD true
    retryAfterUnknown := a.retryAfterUnknown && r.retryAfterUnknown.getD true
    guards := guardJoin a.guards r.guards
    flags := flagJoin a.flags r.flags
    mode := modeJoin a.mode (some (r.mode.getD .logOnly)) }

def CapLe : Option GrantCap → Option Grantable → Prop
  | none, _ => True
  | some c, g => c.le g

instance : (c : Option GrantCap) → (g : Option Grantable) → Decidable (CapLe c g)
  | none, _ => isTrue trivial
  | some c, g => inferInstanceAs (Decidable (c.le g))

/-- `b` is at least as strict as everything `r` requires. -/
def Require.le (r : Require) (b : Requirements) : Prop :=
  (r.consent.getD .none).le b.consent ∧ CapLe r.grantable b.grantable ∧
    BoolLe (r.exposed.getD true) b.exposed ∧ BoolLe (r.idempotent.getD true) b.idempotent ∧
    BoolLe (r.retryAfterUnknown.getD true) b.retryAfterUnknown ∧ ListLe r.guards b.guards ∧
    ListLe r.flags b.flags ∧ ModeLe (some (r.mode.getD .logOnly)) b.mode

instance (r : Require) (b : Requirements) : Decidable (r.le b) := by
  unfold Require.le; infer_instance

end Writ
