import Writ.Author.Join
import Writ.Author.Check

/-!
Expansion of a layer-2 policy to the layer-1 policy the kernel runs, and the layer-2 check.
`parents` is every policy the leaf extends, already resolved and flattened depth-first.
-/

namespace Writ

/-- The index of `dim`'s value in its order, `none` when `p` does not declare `dim`. A missing or
undeclared value takes the last, strictest, index. -/
def Policy2.resolvedLabel (p : Policy2) (labels : List (String × String)) (dim : String) :
    Option Nat :=
  (p.labels.lookup dim).map fun d =>
    match labels.lookup dim with
    | some v => if v ∈ d.order then d.order.idxOf v else d.order.length - 1
    | none => d.order.length - 1

/-- A condition on an undeclared dimension or value never holds; the layer-2 check reports it. -/
def Rule.matches (p : Policy2) (r : Rule) (a : Action2) : Bool :=
  r.when.all fun (dim, v) =>
    match p.labels.lookup dim, p.resolvedLabel a.labels dim with
    | some d, some i => v ∈ d.order && d.order.idxOf v ≤ i
    | _, _ => false

/-- Each dimension's first declaration, leaf first; a differing redeclaration is a check problem. -/
def mergedDims (files : List Policy2) : List (String × LabelDim) :=
  (files.flatMap (·.labels)).foldl
    (fun acc (d, o) => if acc.any (·.1 == d) then acc else acc ++ [(d, o)]) []

/-- Per declared dimension, the highest value over every file that names the action, where a file
that leaves the dimension unlabeled contributes its strictest (last) value: the spec's default
applied per file, then joined, so an extending policy can never resolve an action below any file's
view of it. An unknown value counts as the strictest, and so does every dimension when no file
names the action. -/
def mergedActionLabels (dims : List (String × LabelDim)) (labelSets : List (List (String × String))) :
    List (String × String) :=
  dims.filterMap fun (dim, d) =>
    let last := d.order.length - 1
    let rank (labels : List (String × String)) : Nat :=
      match labels.lookup dim with
      | some v => if v ∈ d.order then d.order.idxOf v else last
      | none => last
    let best := match labelSets.map rank with
      | [] => last
      | r :: rs => rs.foldl max r
    (d.order[best]?).map (dim, ·)

/-- Every field `Requirements.le` compares joins; `permission` and `meters` are the first
non-default value, which is the agreed value whenever the layer-2 check passes. -/
def explicitReq : List Requirements → Requirements
  | [] => {}
  | r :: rest =>
    let rs := r :: rest
    { rest.foldl Requirements.joinStrict r with
      permission := rs.findSome? (·.permission)
      meters := ((rs.map (·.meters)).find? (!·.isEmpty)).getD [] }

/-- A grant stands in for one approval, so consent that needs more drops `grantable` (spec). -/
def dropMultiGrant (r : Requirements) : Requirements :=
  if r.consent.single then r else { r with grantable := none }

/-- An action without `grantable` has no grantable escalators: a grantable escalator needs a
`grantable` action. Applied whatever the files wrote, so expansion stays monotone; a file that
writes a grantable escalator without `grantable` is a layer-2 problem instead. Escalators with no
consent groups that are grantable are dropped first: under `EscLe` they are equivalent to absent
ones, so dropping them keeps `expand` monotone. -/
def settleGrant (r : Requirements) : Requirements :=
  if r.grantable.isNone then
    let kept := r.escalate.filter fun (_, e) => !(e.consent.groups.isEmpty && e.grantable)
    { r with escalate := kept.map fun (n, e) => (n, { e with grantable := false }) }
  else r

def expandAction (dims : List (String × LabelDim)) (rules : List Rule) (files : List Policy2)
    (n : String) : Requirements :=
  let entries := files.flatMap fun f => (f.actions.filter (·.1 == n)).map (·.2)
  let a : Action2 := ⟨explicitReq (entries.map (·.req)), mergedActionLabels dims (entries.map (·.labels))⟩
  let ctx : Policy2 := { labels := dims }
  settleGrant <| dropMultiGrant <| rules.foldl
    (fun acc rule => if rule.matches ctx a then acc.joinReq rule.require else acc) a.req

/-- Policy-level fields are the leaf's. Guards and flags come out sorted and deduplicated only when
a join touched the action (a second file naming it, or a matching rule); otherwise they are as
written, so a layer-1 policy read as layer 2 expands to itself. -/
def expand (parents : List Policy2) (p : Policy2) : Policy :=
  let files := p :: parents
  let dims := mergedDims files
  let rules := files.flatMap (·.rules)
  { p.base with
    actions := ((files.flatMap (·.actions.map (·.1))).eraseDups).map fun n =>
      (n, expandAction dims rules files n) }

inductive Problem2 where
  | conflictingDimension (dim : String)
  | duplicateLabelValue (file dim value : String)
  | parentPolicyField (file key : String)
  | unknownLabelDimension (file action dim : String)
  | unknownLabelValue (file action dim value : String)
  | unknownRuleDimension (file : String) (rule : Nat) (dim : String)
  | unknownRuleValue (file : String) (rule : Nat) (dim value : String)
  | ruleEmptyRoles (file : String) (rule : Nat)
  | ruleZeroQuorum (file : String) (rule : Nat)
  | ruleUnknownRole (file : String) (rule : Nat) (role : String)
  | conflictingField (action field : String)
  | grantableEscalatorWithoutGrantable (file action escalator : String)
  | conflictingCurrency (action : String) (sources : List (String × String))
  | extendsLogOnly
  deriving DecidableEq, Repr

def Problem2.code : Problem2 → String
  | .conflictingDimension _ => "conflicting_dimension"
  | .duplicateLabelValue .. => "duplicate_label_value"
  | .parentPolicyField .. => "parent_policy_field"
  | .unknownLabelDimension .. => "unknown_label_dimension"
  | .unknownLabelValue .. => "unknown_label_value"
  | .unknownRuleDimension .. => "unknown_rule_dimension"
  | .unknownRuleValue .. => "unknown_rule_value"
  | .ruleEmptyRoles .. => "rule_empty_roles"
  | .ruleUnknownRole .. => "rule_unknown_role"
  | .ruleZeroQuorum .. => "rule_zero_quorum"
  | .conflictingField .. => "conflicting_field"
  | .conflictingCurrency .. => "conflicting_currency"
  | .grantableEscalatorWithoutGrantable .. => "grantable_escalator_without_grantable"
  | .extendsLogOnly => "extends_log_only"

def Problem2.action? : Problem2 → Option String
  | .unknownLabelDimension _ a _ | .unknownLabelValue _ a _ _ | .conflictingField a _
  | .conflictingCurrency a _ | .grantableEscalatorWithoutGrantable _ a _ => some a
  | .conflictingDimension _ | .duplicateLabelValue .. | .parentPolicyField ..
  | .unknownRuleDimension .. | .unknownRuleValue .. | .ruleEmptyRoles .. | .ruleZeroQuorum ..
  | .ruleUnknownRole .. | .extendsLogOnly => none

private def inFile (file : String) : String := if file.isEmpty then "" else s!" (in {file})"

def Problem2.message : Problem2 → String
  | .conflictingDimension d => s!"label dimension \"{d}\" is declared with two different orders"
  | .duplicateLabelValue f d v =>
    s!"label dimension \"{d}\" lists value \"{v}\" twice in its order{inFile f}"
  | .parentPolicyField f k =>
    s!"an extended policy{inFile f} sets policy-level field \"{k}\"; only the extending policy may"
  | .unknownLabelDimension f _ d => s!"it is labeled on dimension \"{d}\", which is not declared{inFile f}"
  | .unknownLabelValue f _ d v => s!"its \"{d}\" label \"{v}\" is not in that dimension's order{inFile f}"
  | .unknownRuleDimension f i d => s!"rules[{i}]{inFile f}: when names dimension \"{d}\", which is not declared"
  | .unknownRuleValue f i d v => s!"rules[{i}]{inFile f}: \"{v}\" is not in the order of dimension \"{d}\""
  | .ruleEmptyRoles f i =>
    s!"rules[{i}]{inFile f}: a consent clause has an empty role list, so nobody can approve"
  | .ruleUnknownRole f i r =>
    s!"rules[{i}]{inFile f}: a consent clause names role \"{r}\", which is not an approver role"
  | .ruleZeroQuorum f i => s!"rules[{i}]{inFile f}: a consent clause has a quorum of 0"
  | .conflictingField _ k => s!"the policy and the policies it extends set \"{k}\" to different values"
  | .grantableEscalatorWithoutGrantable f _ e =>
    s!"escalator \"{e}\" is grantable but the action has no grantable{inFile f}"
  | .conflictingCurrency _ srcs =>
    let at' (fc : String × String) := s!"{fc.2} in {if fc.1.isEmpty then "this policy" else fc.1}"
    s!"consent_if_cost_over uses different currencies ({", ".intercalate (srcs.map at')}), so it never lowers consent"
  | .extendsLogOnly =>
    "the policy extends other policies and sets \"mode\": \"log_only\", so every action they require would only be logged; set \"mode\": \"log_only\" on this policy's own actions instead"

def Problem2.render (p : Problem2) : String :=
  match p.action? with
  | some a => s!"{a}: {p.message}"
  | none => p.message

def Problem.render (p : Problem) : String :=
  match p.action? with
  | some a => s!"{a}: {p.message}"
  | none => p.message

/-- The first value that occurs again later in `l`. -/
def firstDupValue : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDupValue xs

/-- The keys an extended policy may write; everything else is policy-level. -/
def parentKeys : List String := ["writ", "$schema", "extends", "labels", "rules", "actions"]

private def ruleProblems (dims : List (String × LabelDim)) (roles : List String) (file : String)
    (r : Rule) (i : Nat) : List Problem2 :=
  (r.when.filterMap fun (d, v) =>
    match dims.lookup d with
    | none => some (.unknownRuleDimension file i d)
    | some o => if v ∈ o.order then none else some (.unknownRuleValue file i d v)) ++
  ((r.require.consent.map (·.clauses)).getD []).flatMap fun cl =>
    (if cl.roles = some [] then [.ruleEmptyRoles file i] else []) ++
    (if cl.k = 0 then [.ruleZeroQuorum file i] else []) ++
    ((cl.roles.getD []).filter (· ∉ roles)).map (.ruleUnknownRole file i)

private def grantProblems (file action : String) (r : Requirements) : List Problem2 :=
  if r.grantable.isNone then
    (r.escalate.filter (·.2.grantable)).map fun (e, _) => .grantableEscalatorWithoutGrantable file action e
  else []

private def labelProblems (dims : List (String × LabelDim)) (file action : String)
    (labels : List (String × String)) : List Problem2 :=
  labels.filterMap fun (d, v) =>
    match dims.lookup d with
    | none => some (.unknownLabelDimension file action d)
    | some o => if v ∈ o.order then none else some (.unknownLabelValue file action d v)

/-- Each must-agree field that two files write for the same action with different text. -/
private def conflicts (files : List File2) : List Problem2 :=
  let written := files.flatMap (·.facts.actionFields)
  (written.map (·.1)).eraseDups.flatMap fun n =>
    let fields := written.filter (·.1 == n) |>.flatMap (·.2)
    (fields.map (·.1)).eraseDups.filterMap fun k =>
      if ((fields.filter (·.1 == k)).map (·.2)).eraseDups.length > 1
      then some (.conflictingField n k) else none

/-- Each action whose files set `consent_if_cost_over` in more than one currency. -/
private def currencyConflicts (files : List File2) : List Problem2 :=
  let sources := files.flatMap fun f => f.policy.actions.filterMap fun (n, a) =>
    a.req.consentIfCostOver.map fun c => (n, f.name, c.currency)
  (sources.map (·.1)).eraseDups.filterMap fun n =>
    let mine := (sources.filter (·.1 == n) |>.map fun (_, f, c) => (f, c)).eraseDups
    if (mine.map (·.2)).eraseDups.length > 1 then some (.conflictingCurrency n mine) else none

/-- The layer-2 problems only; `Policy2.check` adds the expanded policy's. -/
def Policy2.problems (parents : List File2) (leaf : File2) : List Problem2 :=
  let files := leaf :: parents
  let dims := mergedDims (files.map (·.policy))
  let decls := files.flatMap (·.policy.labels)
  -- The leaf's labels and rules may use every file's dimensions, an extended file's only its own
  -- and those of the files it extends.
  let visible := (leaf, dims) :: parents.map fun f => (f, f.policy.labels ++ f.inherited)
  List.eraseDups <|
  (dims.filterMap fun (d, o) =>
    if decls.any fun (d', o') => d' == d && o' != o then some (.conflictingDimension d) else none) ++
  files.flatMap (fun f => f.policy.labels.filterMap fun (d, o) =>
    (firstDupValue o.order).map (.duplicateLabelValue f.name d)) ++
  parents.flatMap (fun f =>
    (f.facts.policyKeys.filter (· ∉ parentKeys)).map (.parentPolicyField f.name)) ++
  visible.flatMap (fun (f, ds) => f.policy.actions.flatMap fun (n, a) =>
    labelProblems ds f.name n a.labels ++ grantProblems f.name n a.req) ++
  visible.flatMap (fun (f, ds) => f.policy.rules.zipIdx.flatMap fun (r, i) =>
    ruleProblems ds leaf.policy.base.approverRoles f.name r i) ++
  conflicts files ++
  currencyConflicts files ++
  (if !parents.isEmpty && leaf.policy.base.mode == .logOnly then [.extendsLogOnly] else [])

/-- Layer-2 problems, then the expanded policy's layer-1 problems, so an empty result means the
expanded policy passes `Policy.check`. -/
def Policy2.check (parents : List File2) (leaf : File2) : List String :=
  (Policy2.problems parents leaf).map Problem2.render ++
    (expand (parents.map (·.policy)) leaf.policy).check.map Problem.render

end Writ
