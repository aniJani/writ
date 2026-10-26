import Writ.Core.Policy

namespace Writ

/-- A label dimension's values, least to most risky. -/
structure LabelDim where
  order : List String
  deriving DecidableEq, Repr

/-- A rule's `grantable`: `forbid` is JSON null, `cap` an object whose absent fields leave that
field of the action's own `grantable` unconstrained. A cap never makes an action grantable. -/
inductive GrantCap where
  | forbid
  | cap (scope : Option GrantScope) (maxUses : Option Nat) (maxDurationMs : Option Nat)
      (anyArgs : Option Bool)
  deriving DecidableEq, Repr

/-- The strictness-ordered fields a rule may set; `none` and `[]` leave a field unconstrained. -/
structure Require where
  consent : Option Consent := none
  grantable : Option GrantCap := none
  exposed : Option Bool := none
  idempotent : Option Bool := none
  retryAfterUnknown : Option Bool := none
  guards : List String := []
  flags : List Flag := []
  mode : Option Mode := none
  deriving DecidableEq, Repr

/-- `when` maps a dimension to the minimum value it must resolve to. -/
structure Rule where
  when : List (String × String)
  require : Require
  deriving DecidableEq, Repr

structure Action2 where
  req : Requirements
  labels : List (String × String) := []
  deriving Repr, BEq

structure Policy2 where
  /-- Policy-level fields; `base.actions` is unused, `actions` holds them. -/
  base : Policy := {}
  «extends» : List String := []
  labels : List (String × LabelDim) := []
  rules : List Rule := []
  actions : List (String × Action2) := []
  deriving Repr, BEq

/-- What a document wrote, which `Policy2` cannot say: its top-level keys, and per action each
field it wrote that files must agree on (the codec's `agreeFields`), with that field's canonical
JSON text. -/
structure DocFacts where
  policyKeys : List String := []
  actionFields : List (String × List (String × String)) := []
  deriving DecidableEq, Repr

/-- One layer-2 document; `name` (its path, for messages) may be empty. `inherited` is every
dimension declared by the files this one extends, directly or not: an extended file's labels and
rules are checked against its own declarations and these, not the extending policy's, so a policy
cannot reorder a dimension under a parent that never declared it. The leaf's is unused, since its
labels and rules see every file's. -/
structure File2 where
  policy : Policy2
  facts : DocFacts := {}
  name : String := ""
  inherited : List (String × LabelDim) := []
  deriving Repr, BEq

end Writ
