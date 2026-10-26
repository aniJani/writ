import WritTests.Fuzz.Gen

open Writ

namespace WritTests.Fuzz

def fails (stepF : StepFn) (name : String) (g : GTrace) : Bool :=
  g.policy.check.isEmpty && (Checks.firstViolation name (replayWith stepF g)).isSome

/-- Greedy chunk deletion: try to drop `size` steps at `i`, staying at `i` after a success. Each
round either deletes or advances, so `2 * length + 2` rounds suffice. -/
def deleteChunks (ok : GTrace → Bool) (g : GTrace) (size : Nat) : GTrace :=
  let rec go : Nat → GTrace → Nat → GTrace
    | 0, g, _ => g
    | fuel + 1, g, i =>
      if i ≥ g.steps.length then g
      else
        let cand := { g with steps := g.steps.take i ++ g.steps.drop (i + size) }
        if ok cand then go fuel cand i else go fuel g (i + size)
  go (2 * g.steps.length + 2) g 0

def deletePass (ok : GTrace → Bool) (g : GTrace) : GTrace :=
  let g := [32, 16, 8, 4, 2, 1].foldl (init := g) fun g size => deleteChunks ok g size
  let oneLane := { g with lanes := 1, steps := g.steps.map ({ · with lane := 0 }) }
  let g := if g.lanes > 1 && ok oneLane then oneLane else g
  let g := if !g.strict && ok { g with strict := true } then { g with strict := true } else g
  if g.skew > 0 && ok { g with skew := 0 } then { g with skew := 0 } else g

def simplerBodies : EventBody → List EventBody
  | .propose id tool d cost guards esc =>
    (if guards.isEmpty then [] else [.propose id tool d cost [] esc])
      ++ (if esc.isEmpty then [] else [.propose id tool d cost guards []])
      ++ (if cost.isNone then [] else [.propose id tool d none guards esc])
  | .approve id rid who d c (some e) =>
    [.approve id rid who d c none]
      ++ (if e.escalators.isEmpty then [] else [.approve id rid who d c (some { e with escalators := [] })])
      ++ (if e.newCost.isNone then [] else [.approve id rid who d c (some { e with newCost := none })])
  | .grantCreate gid who tool d scope n mc nb exp rs =>
    (if nb.isNone then [] else [.grantCreate gid who tool d scope n mc none exp rs])
      ++ (if exp.isNone then [] else [.grantCreate gid who tool d scope n mc nb none rs])
      ++ (if mc.isNone then [] else [.grantCreate gid who tool d scope n none nb exp rs])
  | .result id o actual ne =>
    (if actual.isNone then [] else [.result id o none ne]) ++ (if ne then [.result id o actual false] else [])
  | .reconcile id o actual ne =>
    (if actual.isNone then [] else [.reconcile id o none ne]) ++ (if ne then [.reconcile id o actual false] else [])
  | .dispatch id n d c guards key => if guards.isEmpty then [] else [.dispatch id n d c [] key]
  | .sessionStart sid pd req perms apprs led =>
    (List.range perms.length).map (fun i => .sessionStart sid pd req (perms.eraseIdx i) apprs led)
      ++ (List.range apprs.length).map (fun i => .sessionStart sid pd req perms (apprs.eraseIdx i) led)
  | _ => []

def simplerSteps (g : GStep) : List GStep :=
  (if g.intent == .valid then [] else [{ g with intent := .valid }])
    ++ (if g.dt > 1 then [{ g with dt := 1 }] else [])
    ++ (if g.dt > 0 then [{ g with dt := 0 }] else [])
    ++ (if g.sync == .store then [] else [{ g with sync := .store }])
    ++ (simplerBodies g.body).map ({ g with body := · })

def simplifyStepsPass (ok : GTrace → Bool) (g : GTrace) : GTrace :=
  (List.range g.steps.length).foldl (init := g) fun g i =>
    -- Several rounds per step, since each simplification may enable another.
    (List.range 4).foldl (init := g) fun g _ =>
      match g.steps[i]? with
      | none => g
      | some st =>
        match (simplerSteps st).find? (fun st' => ok { g with steps := g.steps.set i st' }) with
        | some st' => { g with steps := g.steps.set i st' }
        | none => g

def simplerClause (c : Clause) : List Clause :=
  (if c.k > 1 then [{ c with k := 1 }] else [])
    ++ (if c.roles.isSome then [{ c with roles := none }] else [])
    ++ (if c.humanOnly then [{ c with humanOnly := false }] else [])
    ++ (if c.excludeRequester then [{ c with excludeRequester := false }] else [])

def simplerConsent (c : Consent) : List Consent :=
  (List.range c.groups.length).map (fun i => ⟨c.groups.eraseIdx i⟩)
    ++ (List.range c.groups.length).flatMap fun i =>
      match c.groups[i]? with
      | none => []
      | some g =>
        (if g.distinct then [⟨c.groups.set i { g with distinct := false }⟩] else [])
          ++ (if g.clauses.length > 1 then
              (List.range g.clauses.length).map fun j => ⟨c.groups.set i { g with clauses := g.clauses.eraseIdx j }⟩
            else [])
          ++ (List.range g.clauses.length).flatMap fun j =>
            match g.clauses[j]? with
            | none => []
            | some cl => (simplerClause cl).map fun cl => ⟨c.groups.set i { g with clauses := g.clauses.set j cl }⟩

def simplerReqs (r : Requirements) : List Requirements :=
  (if r.permission.isSome then [{ r with permission := none }] else [])
    ++ (if r.consentIfCostOver.isSome then [{ r with consentIfCostOver := none }] else [])
    ++ (List.range r.escalate.length).map (fun i => { r with escalate := r.escalate.eraseIdx i })
    ++ (if r.grantable.isSome then [{ r with grantable := none }] else [])
    ++ (if r.guards.isEmpty then [] else [{ r with guards := [] }])
    ++ (List.range r.meters.length).map (fun i => { r with meters := r.meters.eraseIdx i })
    ++ (if r.mode.isSome then [{ r with mode := none }] else [])
    ++ (if r.exposed then [] else [{ r with exposed := true }])
    ++ (if r.retryAfterUnknown then [{ r with retryAfterUnknown := false }] else [])
    ++ (if r.idempotent && !r.retryAfterUnknown then [{ r with idempotent := false }] else [])
    ++ (if r.maxAttempts != 1 then [{ r with maxAttempts := 1 }] else [])
    ++ (if r.approvalTtlMs.isSome then [{ r with approvalTtlMs := none }] else [])
    ++ (if r.authorizedTtlMs.isSome then [{ r with authorizedTtlMs := none }] else [])
    ++ (simplerConsent r.consent).map ({ r with consent := · })

def simplerLimits (l : Limits) : List Limits :=
  (if l.maxStepsPerTurn.isSome then [{ l with maxStepsPerTurn := none }] else [])
    ++ (if l.maxProposalsPerTurn.isSome then [{ l with maxProposalsPerTurn := none }] else [])
    ++ (if l.maxApprovalRequestsPerTurn.isSome then [{ l with maxApprovalRequestsPerTurn := none }] else [])
    ++ (if l.maxProposalsPerSession.isSome then [{ l with maxProposalsPerSession := none }] else [])
    ++ (if l.maxApprovalRequestsPerSession.isSome then [{ l with maxApprovalRequestsPerSession := none }] else [])
    ++ (if l.maxConsecutiveFailures.isSome then [{ l with maxConsecutiveFailures := none }] else [])
    ++ (if l.maxFailuresPerSession.isSome then [{ l with maxFailuresPerSession := none }] else [])
    ++ (if l.escalationScope == .session then [] else [{ l with escalationScope := .session }])
    ++ (if l.approvalTtlMs.isSome then [{ l with approvalTtlMs := none }] else [])
    ++ (if l.authorizedTtlMs.isSome then [{ l with authorizedTtlMs := none }] else [])

def simplerMeter (m : MeterSpec) : List MeterSpec :=
  (if m.windowMs.isSome then [{ m with windowMs := none }] else [])
    ++ (if m.maxPerCall.isSome then [{ m with maxPerCall := none }] else [])
    ++ (if m.scope == .principal then [{ m with scope := .session }] else [])

def simplerPolicies (p : Policy) : List Policy :=
  (List.range p.actions.length).map (fun i => { p with actions := p.actions.eraseIdx i })
    ++ (List.range p.meters.length).map (fun i => { p with meters := p.meters.eraseIdx i })
    ++ (simplerLimits p.limits).map ({ p with limits := · })
    ++ (List.range p.meters.length).flatMap (fun i =>
      match p.meters[i]? with
      | some (n, m) => (simplerMeter m).map fun m => { p with meters := p.meters.set i (n, m) }
      | none => [])
    ++ (List.range p.actions.length).flatMap (fun i =>
      match p.actions[i]? with
      | some (n, r) => (simplerReqs r).map fun r => { p with actions := p.actions.set i (n, r) }
      | none => [])
    ++ (if p.mode == .enforce then [] else [{ p with mode := .enforce }])
    ++ (if p.escalationRoles.isSome then [{ p with escalationRoles := none }] else [])
    ++ (if p.bindingMutable then [] else [{ p with bindingMutable := true }])
    ++ (if p.killSetsTombstone then [{ p with killSetsTombstone := false }] else [])

def simplifyPolicyPass (ok : GTrace → Bool) (g : GTrace) : GTrace :=
  let rec go : Nat → GTrace → GTrace
    | 0, g => g
    | fuel + 1, g =>
      match (simplerPolicies g.policy).find? (fun p => ok { g with policy := p }) with
      | some p => go fuel { g with policy := p }
      | none => g
  let g := go 300 g
  if g.initLedger != {} && ok { g with initLedger := {} } then { g with initLedger := {} } else g

def shrink (stepF : StepFn) (name : String) (g : GTrace) : GTrace :=
  let ok := fails stepF name
  let rec go : Nat → GTrace → GTrace
    | 0, g => g
    | fuel + 1, g =>
      let g' := simplifyPolicyPass ok (simplifyStepsPass ok (deletePass ok g))
      if g'.length == g.length && reprStr g' == reprStr g then g else go fuel g'
  go 8 g

def fmt [Repr α] (x : α) : String := (Std.Format.pretty (repr x) 10000).replace "Writ." ""

def showReqs (r : Requirements) : String :=
  let d : Requirements := {}
  let fields : List (Option String) :=
    [ if r.permission != d.permission then some s!"permission := {fmt r.permission}" else none
    , if r.consent != d.consent then some s!"consent := {fmt r.consent}" else none
    , if r.consentIfCostOver != d.consentIfCostOver then some s!"consentIfCostOver := {fmt r.consentIfCostOver}" else none
    , if r.escalate != d.escalate then some s!"escalate := {fmt r.escalate}" else none
    , if r.grantable != d.grantable then some s!"grantable := {fmt r.grantable}" else none
    , if r.idempotent then some "idempotent := true" else none
    , if r.retryAfterUnknown then some "retryAfterUnknown := true" else none
    , if r.maxAttempts != 1 then some s!"maxAttempts := {r.maxAttempts}" else none
    , if r.guards.isEmpty then none else some s!"guards := {fmt r.guards}"
    , if r.meters.isEmpty then none else some s!"meters := {fmt r.meters}"
    , r.approvalTtlMs.map (s!"approvalTtlMs := some {·}")
    , r.authorizedTtlMs.map (s!"authorizedTtlMs := some {·}")
    , if r.exposed then none else some "exposed := false"
    , if r.mode.isSome then some s!"mode := {fmt r.mode}" else none ]
  "{ " ++ ", ".intercalate fields.reduceOption ++ " }"

def showLimits (l : Limits) : String :=
  let f (n : String) (v : Option Nat) : Option String := v.map (s!"{n} := some {·}")
  let fields :=
    [ f "maxStepsPerTurn" l.maxStepsPerTurn, f "maxProposalsPerTurn" l.maxProposalsPerTurn
    , f "maxApprovalRequestsPerTurn" l.maxApprovalRequestsPerTurn
    , f "maxProposalsPerSession" l.maxProposalsPerSession
    , f "maxApprovalRequestsPerSession" l.maxApprovalRequestsPerSession
    , f "maxConsecutiveFailures" l.maxConsecutiveFailures, f "maxFailuresPerSession" l.maxFailuresPerSession
    , if l.escalationScope == .tool then some "escalationScope := .tool" else none
    , f "approvalTtlMs" l.approvalTtlMs, f "authorizedTtlMs" l.authorizedTtlMs ]
  "{ " ++ ", ".intercalate fields.reduceOption ++ " }"

def showPolicy (p : Policy) : String :=
  let actions := ", ".intercalate (p.actions.map fun (n, r) => s!"(\"{n}\", {showReqs r})")
  let meters := ", ".intercalate (p.meters.map fun (n, m) => s!"(\"{n}\", {fmt m})")
  let lines : List (Option String) :=
    [ if p.mode == .enforce then none else some s!"  mode := {fmt p.mode}"
    , some s!"  approverRoles := {fmt p.approverRoles}"
    , p.escalationRoles.map (s!"  escalationRoles := some {fmt ·}")
    , if p.meters.isEmpty then none else some s!"  meters := [{meters}]"
    , if showLimits p.limits == "{  }" then none else some s!"  limits := {showLimits p.limits}"
    , some s!"  actions := [{actions}]"
    , if p.bindingMutable then none else some "  bindingMutable := false"
    , if p.killSetsTombstone then some "  killSetsTombstone := true" else none ]
  "def fuzzPolicy : Policy where\n" ++ "\n".intercalate lines.reduceOption

def showBody (b : EventBody) : String :=
  let s := fmt b
  if s.startsWith "EventBody." then "." ++ (s.drop 10).toString else s

/-- Prints the shrunk trace as one `checkedScript` per session plus the interleaving, or as raw
events when an envelope (stale seq, wrong version) cannot be expressed by `checkedScript`. -/
def showTrace (stepF : StepFn) (name : String) (g : GTrace) : String :=
  let t := replayWith stepF g
  let steps := t.items.filterMap fun | .step s => some s | .storeClear => none
  let insts := (steps.map (·.inst)).eraseDups
  let idxOf (i : Nat) : Nat := (insts.findIdx? (· == i)).getD 0
  let order := t.items.map fun | .step s => some (idxOf s.inst) | .storeClear => none
  let per := insts.map fun i => steps.filter (·.inst == i)
  let scriptable := per.all fun ss =>
    (ss.zip (List.range ss.length)).all fun (s, k) => s.event.seq == k + 1 && s.event.stateVersion == s.pre.version
  let names := (List.range insts.length).map (s!"fuzzS{·}")
  let defs := (per.zip names).map fun (ss, n) =>
    if scriptable then
      s!"def {n} : List (Nat × EventBody) := [\n" ++ ",\n".intercalate (ss.map fun s => s!"  ({s.event.time}, {showBody s.event.body})") ++ "]"
    else
      s!"def {n} : List Event := [\n" ++ ",\n".intercalate (ss.map fun s =>
        s!"  ⟨{s.event.seq}, {s.event.time}, {s.event.stateVersion}, none, {showBody s.event.body}⟩") ++ "]"
  let ledger := s!"def fuzzLedger : Ledger := {fmt g.initLedger}"
  let builder := if scriptable then "Checks.scripted" else "Checks.rawScripted"
  let trace := s!"{builder} fuzzPolicy fuzzLedger [{", ".intercalate names}] {fmt order}"
  let evals := if scriptable then names.map (s!"#eval (checkedScript fuzzPolicy {·}).2.1") else []
  "\n".intercalate ([showPolicy g.policy, ledger] ++ defs ++ evals ++
    [s!"#guard (Checks.firstViolation \"{name}\" ({trace})).isNone"])

end WritTests.Fuzz
