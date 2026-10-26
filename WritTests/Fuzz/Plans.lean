import WritTests.Fuzz.Base

open Writ

namespace WritTests.Fuzz

inductive Plan where
  | propose (cid gid : String)
  | dispatch (cid : String)
  | unknown (cid : String)
  | cancel (cid : String)
  | metered (cid tool : String)
  | result (cid : String)
  | sync
  | unknownTool (cid : String)
  /-- A call-scoped event on `cid`, whether or not the call has a record. -/
  | onCall (cid : String) (kind : Nat)
  /-- A fresh proposal of a defined tool, carrying guard and escalator names the action does not declare. -/
  | reuse (cid : String)
  | overrun (cid : String)
  /-- `overrun` reported through `reconcile`, for a call that went Unknown. -/
  | lateOverrun (cid : String)
  | kill
  | reset
  | finish
  /-- Clear the stored tombstone out of band. -/
  | clearStore
  | settle (cid : String)
  | sized (cid tool : String) (amount : Nat)
  /-- A `result` with these fields, or a `reconcile` when `late`. -/
  | report (cid : String) (o : Outcome) (actual : Option Nat) (noEffect late : Bool)
  | syncWith (m : SyncMode)
  /-- Approve with a fresh eligible approver while the call awaits, dispatch it once authorized. -/
  | drive (cid : String)
  /-- `drive` without the dispatch. -/
  | approveOnly (cid : String)
  | ack (stale : Bool)
  | again (cid : String)
  /-- A reject from an eligible approver, echoing the current generation or an earlier one. -/
  | veto (cid : String) (older : Bool)
  /-- An edit to a digest rejected earlier for the call's tool, or a plain approval if there is none. -/
  | editToRejected (cid : String)
  | revoke (perm : String)
  /-- A dispatch of `cid` with a digest no call has. -/
  | dispatchOff (cid : String)
  /-- A fresh proposal with the tool, digest and cost `src` was proposed with. -/
  | twin (cid src : String)
  | turnOver
  | turnBegin
  /-- A grant created by an approver eligible for every clause it must cover. -/
  | grantNew (gid tool : String) (digest : Option String) (scope : GrantScope) (maxCost : Option Cost)
      (expiresAt : Option Nat)
  /-- An approver edit to `digest`, or to a random one. -/
  | edit (cid : String) (digest : Option String)
  /-- A repeat with the digest and cost as current after edits. -/
  | againCurrent (cid : String)
  /-- A fresh proposal built to fail two propose checks in a row: by `kind`, 0 permission and guard,
  1 guard and cost shape, 2 a rejected pair with a bad cost, 3 a rejected pair needing approval. -/
  | stack (cid : String) (kind : Nat)
  /-- An approver edit firing every escalator of the call's tool, from one of `raisingEditors`. -/
  | raise (cid : String)
  /-- An approval from one of `machinesFor`. -/
  | machine (cid : String)

def Plan.isOob : Plan → Bool
  | .clearStore => true
  | _ => false

def Plan.syncMode : Plan → SyncMode
  | .syncWith m => m
  | _ => .store

structure PlanStep where
  lane : Nat
  jump : Option Nat := none
  /-- The step still runs once the lane's session has ended. -/
  ended : Bool := false
  /-- When the step does not apply, the plan goes on with the next one instead of stopping. -/
  optional : Bool := false
  step : Plan

structure GS where
  w : World
  steps : Array GStep := #[]
  nextCall : Nat := 0
  nextGrant : Nat := 0
  lanes : Nat
  seenEsc : List Nat := []
  usedSids : List String := []
  tpl : Nat := 0
  plan : List PlanStep := []
  otherScopeRan : Bool := false

def GS.lane (g : GS) (i : Nat) : Lane := g.w.lane i

/-- How a plan loses a dispatched call before retrying it: 0 `outcome_unknown`, else a `reset`, which
also starts a new epoch. Plans draw `how` in the same `weighted` as their other choice, so it costs
no extra draw. -/
def lostAs (how : Nat) (cid : String) : Plan := if how == 0 then .unknown cid else .reset

/-- Short scripted scenarios for paths the random walk rarely completes: a grant-backed call that
goes Unknown and is retried, and a grant use returned by cancel and then reused. -/
def startPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let live := liveGrants s
  if live.isEmpty then return g
  let usable := s.grants.toList.filter fun (_, x) => live.any (·.tool == x.tool) && live.any (·.digest == x.digest)
  let retrying := usable.filter fun (_, x) => (reqOf p x.tool).retryAfterUnknown && (reqOf p x.tool).maxAttempts ≥ 2
  let (gid, gr) ← pick (if retrying.isEmpty then usable else retrying)
  let c1 := s!"c{g.nextCall}"
  let c2 := s!"c{g.nextCall + 1}"
  let how ← weighted [(60, 0), (15, 1), (25, 2)]
  let plan := if (reqOf p gr.tool).retryAfterUnknown && how < 2 then
      [Plan.propose c1 gid, .dispatch c1, lostAs how c1, .dispatch c1]
    else [.propose c1 gid, .cancel c1, .propose c2 gid, .dispatch c2]
  pure { g with nextCall := g.nextCall + 2, plan := plan.map ({ lane, step := · }) }

/-- Actions a plan can propose and get authorized: exposed, needing no permission; a plan approves
them as far as the session's approvers allow. -/
def runnable (r : Requirements) : Bool := r.exposed && r.permission.isNone

/-- Propose `cid` and approve it while it awaits; `jump` is the dt of the proposal, `later` of each
approval. -/
def authorizeSteps (lane : Nat) (cid tool : String) (jump later : Option Nat := none) : List PlanStep :=
  { lane, jump, step := .metered cid tool } :: List.replicate 4 { lane, jump := later, optional := true, step := .approveOnly cid }

def windowedPrincipal (p : Policy) (r : Requirements) : List Nat :=
  (Checks.metersOf p r).filterMap fun (_, m) => if m.scope == .principal then m.windowMs else none

/-- Lane `a` commits on a windowed principal meter; once the window has passed, lane `b` reserves on
the principal ledger, which prunes `a`'s entry from it, and then `a` syncs. -/
def startPrunePlan (p : Policy) (g : GS) : Gen GS := do
  let tools := p.actions.filter fun (_, r) => runnable r && !(windowedPrincipal p r).isEmpty
  if tools.isEmpty then return g
  let tool ← pick (tools.map (·.1))
  let r := reqOf p tool
  let jump := (windowedPrincipal p r).foldl max 0 + 1
  let a ← below g.lanes
  let b := (a + 1 + (← below (g.lanes - 1))) % g.lanes
  let c1 := s!"c{g.nextCall}"
  let c2 := s!"c{g.nextCall + 1}"
  let plan : List PlanStep :=
    authorizeSteps a c1 tool ++ [{ lane := a, step := .dispatch c1 }, { lane := a, step := .result c1 }]
    ++ authorizeSteps b c2 tool (some jump) ++ [{ lane := b, step := .dispatch c2 }, { lane := a, step := .sync }]
  pure { g with nextCall := g.nextCall + 2, plan }

def sessionWindow (p : Policy) (name : String) : Option Nat :=
  (Checks.meterOf p name).bind fun m => if m.scope == .session then m.windowMs else none

def principalTools (p : Policy) : List String :=
  (p.actions.filter fun (_, r) => runnable r && (Checks.metersOf p r).any (·.2.scope == .principal)).map (·.1)

/-- The stored ledger holds an entry under the name of a windowed session meter, which a claim on
the principal ledger must not prune. -/
def otherScopeDue (p : Policy) (g : GS) : Bool :=
  g.w.store.entries.any (fun e => (sessionWindow p e.meter).isSome) && !(principalTools p).isEmpty

/-- Once that window has passed, a live lane claims on a principal meter, which changes the
principal list. -/
def startOtherScopePlan (p : Policy) (g : GS) : Gen GS := do
  let lane ← below (max g.lanes 1)
  let s := (g.lane lane).s
  if !s.started || s.ended then return g
  let tool ← pick (principalTools p)
  let jump := (g.w.store.entries.filterMap (sessionWindow p ·.meter)).foldl max 0 + 1
  let c := s!"c{g.nextCall}"
  let plan := authorizeSteps lane c tool (some jump) ++ [{ lane, step := .dispatch c }]
  pure { g with nextCall := g.nextCall + 1, plan, otherScopeRan := true }

/-- Lane 0 claims on a principal meter, then lagging lane 1 claims on it at once, so lane 1 counts an
entry dated ahead of its own clock. -/
def startSkewPlan (p : Policy) (g : GS) : Gen GS := do
  let tools := principalTools p
  if tools.isEmpty then return g
  let tool ← pick tools
  let c1 := s!"c{g.nextCall}"
  let c2 := s!"c{g.nextCall + 1}"
  let plan : List PlanStep :=
    authorizeSteps 0 c1 tool ++ [{ lane := 0, step := .dispatch c1 }]
    ++ authorizeSteps 1 c2 tool (some 0) (some 0) ++ [{ lane := 1, jump := some 0, step := .dispatch c2 }]
  pure { g with nextCall := g.nextCall + 2, plan }

/-- An unknown-tool proposal leaves no record, so later events on its id, a repeat of it and a
fresh proposal reusing it are all judged as for an unused id. The last two steps record a call and
then propose an unknown tool on its id. -/
def startUnknownToolPlan (g : GS) (lane : Nat) : Gen GS := do
  let c1 := s!"c{g.nextCall}"
  let c2 := s!"c{g.nextCall + 1}"
  let second ← if ← chance 30 then pure (Plan.unknownTool c1) else do pure (.onCall c1 (← below 8))
  let third ← pick [5, 6, 7]
  let fourth ← pick [1, 2, 3]
  let plan := [.unknownTool c1, second, .onCall c1 third, .onCall c1 fourth, .reuse c1, .reuse c2, .unknownTool c2]
  pure { g with nextCall := g.nextCall + 2, plan := plan.map ({ lane, step := · }) }

def moneyMeters (p : Policy) (r : Requirements) : Nat :=
  ((Checks.metersOf p r).filter fun (_, m) => (currencyOf m.unit).isSome).length

/-- Commit an actual cost above the reservation on an action with two money meters, sometimes
through `reconcile` after the call went Unknown. -/
def startOverrunPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let tools := p.actions.filter fun (_, r) => runnable r && moneyMeters p r ≥ 2
  if tools.isEmpty then return g
  let tool ← pick (tools.map (·.1))
  let c := s!"c{g.nextCall}"
  let report := if ← chance 50 then [Plan.overrun c] else [.unknown c, .lateOverrun c]
  let plan := authorizeSteps lane c tool ++ (Plan.dispatch c :: report).map ({ lane, step := · })
  pure { g with nextCall := g.nextCall + 1, plan }

/-- The tool's meter windows a retry can wait out before its authorization expires. -/
def retryWindows (p : Policy) (r : Requirements) : List Nat :=
  (Checks.metersOf p r).filterMap fun (_, m) => m.windowMs.filter fun w => (Checks.authorizedTtlOf p r).all (w + 4 < ·)

/-- A claim that goes Unknown and is retried, sometimes after its reservation has left the window,
sometimes after a reset made it Unknown. -/
def startRetryPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let tools := p.actions.filter fun (_, r) => runnable r && r.retryAfterUnknown && r.maxAttempts ≥ 2
  if tools.isEmpty then return g
  let windowed := tools.filter fun (_, r) => !(retryWindows p r).isEmpty
  let (tool, r) ← pick (if windowed.isEmpty then tools else windowed)
  let c := s!"c{g.nextCall}"
  let how ← weighted [(65, 0), (20, 1), (15, 2)]
  let jump := if how == 0 then some ((retryWindows p r).min?.getD (retryJump p)) else none
  let plan := authorizeSteps lane c tool ++ [Plan.dispatch c, lostAs (if how == 2 then 1 else 0) c].map ({ lane, step := · })
    ++ [{ lane, jump, step := .dispatch c }]
  pure { g with nextCall := g.nextCall + 1, plan }

/-- A principal kill ends a session holding a dispatched call; once the stored tombstone is cleared
out of band, the ended session syncs and reconciles the call. -/
def startKillClearPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let tools := p.actions.filter fun (_, r) => runnable r
  if tools.isEmpty then return g
  let tool ← pick (tools.map (·.1))
  let c := s!"c{g.nextCall}"
  let live := authorizeSteps lane c tool ++ [Plan.dispatch c, .kill, .finish].map ({ lane, step := · })
  let late := [Plan.clearStore, .sync, .settle c].map ({ lane, ended := true, step := · })
  pure { g with nextCall := g.nextCall + 1, plan := live ++ late }

def runnableTools (p : Policy) : List String := (p.actions.filter (runnable ·.2)).map (·.1)

/-- What is left of a capped meter's cap at `now`. -/
def roomLeft (g : GS) (s : State) (now : Nat) (n : String) (m : MeterSpec) : Option Nat :=
  m.cap.map (· - Checks.usageOf (match m.scope with | .session => s.sessionMeters | .principal => g.w.store.entries) n m.windowMs now)

/-- Two calls that each fit a capped money meter but not both. The first settles by an overrun past
the cap (sometimes late, through reconcile), a release with excess, a partial capture, or not at
all, before the second is dispatched. -/
def startCapPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let now := g.w.clock
  let fit (r : Requirements) : Option (Nat × Nat) := do
    let ms := Checks.metersOf p r
    let room ← ((ms.filter fun (_, m) => (currencyOf m.unit).isSome).filterMap fun (n, m) => roomLeft g s now n m).min?
    let x := room / 2 + 1
    if room == 0 || !(ms.all fun (n, m) => m.maxPerCall.all (x ≤ ·) && (roomLeft g s now n m).all (1 ≤ ·)) then none
    else some (x, room)
  let tools := p.actions.filterMap fun (t, r) => if runnable r then (fit r).map (t, ·) else none
  if tools.isEmpty then return g
  let (tool, x, room) ← pick tools
  let c1 := s!"c{g.nextCall}"
  let c2 := s!"c{g.nextCall + 1}"
  let settle : List Plan ← match ← weighted [(1, 0), (2, 1), (3, 2), (2, 3), (1, 4)] with
    | 0 => pure [.report c1 .succeeded (some (room + 1)) false false]
    | 1 => pure [.unknown c1, .report c1 .succeeded (some (room + 1)) false true]
    | 2 => do
      let declined ← chance 70
      pure [.report c1 (if declined then .declined else .succeeded) (some (x + 2)) (!declined) false]
    | 3 => pure [.report c1 .succeeded (some (x - 1)) false false]
    | _ => pure []
  let approve (c : String) := List.replicate 4 ({ lane, optional := true, step := .approveOnly c } : PlanStep)
  let plan : List PlanStep := [{ lane, step := .sized c1 tool x }, { lane, step := .sized c2 tool x }] ++ approve c1
    ++ approve c2 ++ ([Plan.dispatch c1] ++ settle ++ [Plan.dispatch c2]).map ({ lane, step := · })
  pure { g with nextCall := g.nextCall + 2, plan }

/-- Fail one tool until it or the session is blocked and propose it again, with a call of an
unexposed tool (when the policy has one) proposed and dispatched before the block and repeated and
proposed afresh after it, then acknowledge with a stale and sometimes the current escalation count. -/
def startEscalationPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let tools := runnableTools p
  if tools.isEmpty then return g
  let tool ← pick tools
  let l := p.limits
  let byTool := l.maxConsecutiveFailures.map (· - (s.failures.get? tool).getD 0)
  let bySession := l.maxFailuresPerSession.map (· - s.failuresThisSession)
  let hidden := (p.actions.filter (!·.2.exposed)).map (·.1)
  let hide ← if hidden.isEmpty then pure none else some <$> pick hidden
  -- With an unexposed tool to propose, fail until the session itself is blocked when that differs.
  let need := match byTool, bySession with
    | some a, some b => if hide.isSome && l.escalationScope == .tool then b else min a b
    | some a, none => a
    | none, some b => b
    | none, none => 0
  if need == 0 then return g
  let base := g.nextCall
  let cid (i : Nat) := s!"c{base + i}"
  let fails := (List.range need).flatMap fun i =>
    authorizeSteps lane (cid i) tool ++ [Plan.dispatch (cid i), .report (cid i) .failed none false false].map ({ lane, step := · })
  let (before, after) := match hide with
    | some u => ([Plan.metered (cid need) u, .dispatch (cid need)], [Plan.again (cid need), .metered (cid (need + 2)) u])
    | none => ([], [])
  -- More proposals of the blocked tool until a proposal limit is reached as well.
  let count := need + 1 + (if hide.isSome then 2 else 0)
  let room := match l.maxProposalsPerTurn with
    | some m => some (m - s.proposalsThisTurn)
    | none => l.maxProposalsPerSession.map (· - s.proposalsThisSession)
  let extra := match room with
    | some k => if k < count then 1 else if k - count ≤ 3 then k - count + 1 else 0
    | none => 0
  let blocked := (List.range (extra + 1)).map fun i => Plan.metered (cid (need + 3 + i)) tool
  let steps (ps : List Plan) : List PlanStep := ps.map ({ lane, step := · })
  -- Without the current acknowledgment the block outlasts the plan.
  let acks := if ← chance 50 then [Plan.ack true, .ack false] else [.ack true]
  let plan := steps before ++ fails ++ steps (blocked ++ after ++ acks)
  pure { g with nextCall := base + need + 4 + extra, plan }

/-- A claim on a principal meter, then a sync whose ledger drops that reservation, repeats it, or
carries an own entry the session never wrote. -/
def startSyncPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let tools := principalTools p
  if tools.isEmpty then return g
  let tool ← pick tools
  let c := s!"c{g.nextCall}"
  let m ← weighted [(6, SyncMode.dropReservation), (4, .foreignEntry), (4, .duplicateReservation)]
  let plan := authorizeSteps lane c tool ++ [Plan.dispatch c, .syncWith m].map ({ lane, step := · })
  pure { g with nextCall := g.nextCall + 1, plan }

/-- Lane `b` holds an authorized call when lane `a` kills under a principal kill scope; `b`
dispatches before syncing, first with another digest and on an unknown call. A claim there would
fail the ledger compare-and-swap, so only refused dispatches are recorded against the other lane's
tombstone. -/
def startForeignKillPlan (p : Policy) (g : GS) : Gen GS := do
  let tools := runnableTools p
  if !p.killSetsTombstone || g.lanes < 2 || tools.isEmpty then return g
  let tool ← pick tools
  let a ← below g.lanes
  let b := (a + 1 + (← below (g.lanes - 1))) % g.lanes
  let c := s!"c{g.nextCall}"
  let plan : List PlanStep := authorizeSteps b c tool ++
    [ { lane := a, step := .kill }, { lane := b, step := .dispatchOff c }, { lane := b, step := .onCall "c99" 0 }
    , { lane := b, step := .dispatch c } ]
  pure { g with nextCall := g.nextCall + 1, plan }

/-- Turns of at most `turnB` events, the last a full one, spending `left` in all. -/
def turnChunks (left turnB : Nat) : List Nat :=
  let early := left - turnB
  (if early % turnB > 0 then [early % turnB] else []) ++ List.replicate (early / turnB) turnB ++ [turnB]

/-- Spend the approval budgets so that the session's and the turn's run out on the same proposal:
turns of at most the turn budget, the last a full one. -/
def startBudgetPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let some sessB := p.limits.maxApprovalRequestsPerSession | return g
  let some turnB := p.limits.maxApprovalRequestsPerTurn | return g
  let left := sessB - s.approvalsThisSession
  if turnB == 0 || left < turnB || left > 8 then return g
  let tools := p.actions.filter fun (_, r) => runnable r && r.meters.isEmpty
    && !Checks.trivialC r.consent && r.mode.getD p.mode == .enforce
  if tools.isEmpty then return g
  let tool ← pick (tools.map (·.1))
  let (plan, n) := (turnChunks left turnB).foldl (init := (([] : List Plan), g.nextCall)) fun (acc, n) k =>
    (acc ++ [.turnOver, .turnBegin] ++ (List.range k).map fun i => .metered s!"c{n + i}" tool, n + k)
  let plan := plan ++ [.veto s!"c{g.nextCall}" false, .metered s!"c{n}" tool, .metered s!"c{n + 1}" tool, .stack s!"c{n + 2}" 3]
  pure { g with nextCall := n + 3, plan := plan.map ({ lane, step := · }) }

/-- Create a grant, then use it on a call that goes Unknown and is retried, or on a call that is
cancelled before a second call reuses the returned use. -/
def startGrantPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let l := g.lane lane
  let tools := p.actions.filter fun (_, r) => runnable r && r.grantable.isSome
  if tools.isEmpty then return g
  let retrying := tools.filter fun (_, r) => r.retryAfterUnknown && r.maxAttempts ≥ 2
  let (tool, r) ← pick (if retrying.isEmpty then tools else retrying)
  let some gr := r.grantable | return g
  let digest ← if gr.anyArgs && (← chance 50) then pure none else some <$> pick digests
  let maxCost ← if ← chance 50 then pure (some ⟨6, (moneyCurrency p r).getD "USD"⟩) else pure none
  let lag := if (lane % g.w.lanes.size) % 2 == 1 then g.w.skew else 0
  -- No later than the creation time plus max_duration_ms, whatever dt the step draws.
  let exp := gr.maxDurationMs.map (max l.s.lastTime (g.w.clock - lag) + ·)
  let gid := s!"g{g.nextGrant}"
  let c1 := s!"c{g.nextCall}"
  let c2 := s!"c{g.nextCall + 1}"
  let how ← weighted [(70, 0), (15, 1), (15, 2)]
  let use := if r.retryAfterUnknown && r.maxAttempts ≥ 2 && how < 2 then
      [Plan.propose c1 gid, .dispatch c1, lostAs how c1, .dispatch c1]
    else [.propose c1 gid, .cancel c1, .propose c2 gid, .dispatch c2]
  let plan := (if gr.scope == .turn then [Plan.turnBegin] else []) ++ [.grantNew gid tool digest gr.scope maxCost exp] ++ use
  pure { g with nextCall := g.nextCall + 2, nextGrant := g.nextGrant + 1, plan := plan.map ({ lane, step := · }) }

/-- Attested automated approvers outside the call's tally that would be eligible for some clause of
its consent if human, and only for `human_only` clauses, so their approval must be refused. -/
def machinesFor (p : Policy) (s : State) (c : CallRec) : List String :=
  (s.approvers.toList.filter fun (_, i) =>
    let cls := (Checks.clausesOf c.consent).filter (Checks.eligibleFor p s.requester { i with kind := .human } ·)
    i.kind == .automated && !c.tally.any (·.1 == i.principal) && !cls.isEmpty && cls.all (·.humanOnly)).map (·.1)

/-- Approvers whose approval alone would authorize the call after an edit that fires none of its
tool's escalators, but not after one that fires them all. -/
def raisingEditors (p : Policy) (s : State) (c : CallRec) : List String :=
  let r := reqOf p c.tool
  let alone (fire : Bool) (i : ApproverInfo) :=
    Checks.satisfiedBy (fun cl i => Checks.eligibleFor p s.requester i cl)
      (Checks.joinC c.consent (Checks.consentAt r c.cost (r.escalate.map (·.1, fire)))) [(i.principal, i)]
  (s.approvers.toList.filter fun (_, i) => rawEligible p s c.consent i && alone false i && !alone true i).map (·.1)

def enforced (p : Policy) (c : CallRec) : Bool := (reqOf p c.tool).mode.getD p.mode == .enforce

def stackKinds (p : Policy) (s : State) : List Nat :=
  let avail := p.actions.filter fun (t, r) => r.exposed && !s.blockedTools.contains t
  let held (r : Requirements) := r.permission.all s.permissions.contains
  let money (r : Requirements) := (moneyCurrency p r).isSome
  (if avail.any fun (_, r) => r.permission.isSome && !r.guards.isEmpty then [0] else [])
    ++ (if avail.any fun (_, r) => held r && !r.guards.isEmpty && money r then [1] else [])
    ++ (if s.rejectedMemory.any fun (t, _) => (Checks.reqOf p t).any fun r => r.exposed && held r && money r then [2] else [])

/-- One fresh proposal that fails two propose checks in a row; for the permission and guard pair,
the permission is revoked first when the session holds it. -/
def startStackPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let kinds := stackKinds p s
  if kinds.isEmpty then return g
  let kind ← pick kinds
  let c := s!"c{g.nextCall}"
  let revoke ← if kind != 0 then pure [] else do
    let perms := (p.actions.filterMap fun (_, r) => if r.exposed && !r.guards.isEmpty then r.permission else none).eraseDups
    let perm ← pick perms
    pure (if s.permissions.contains perm then [Plan.revoke perm] else [])
  pure { g with nextCall := g.nextCall + 1, plan := (revoke ++ [Plan.stack c kind]).map ({ lane, step := · }) }

/-- A call is vetoed after a twin of it was approved; the twin is then dispatched, an approver edits
a third call of the tool to the vetoed digest, a fresh proposal repeats the vetoed pair with a bad
cost, and the third call is driven to dispatch. -/
def startRejectionPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let tools := p.actions.filter fun (t, r) => r.exposed && r.permission.all s.permissions.contains
    && !Checks.trivialC r.consent && !s.blockedTools.contains t
  if tools.isEmpty then return g
  let money := tools.filter fun (_, r) => (moneyCurrency p r).isSome
  let (tool, _) ← pick (if !money.isEmpty && (← chance 60) then money else tools)
  let c0 := s!"c{g.nextCall}"
  let c1 := s!"c{g.nextCall + 1}"
  let c2 := s!"c{g.nextCall + 2}"
  let c3 := s!"c{g.nextCall + 3}"
  let steps (ps : List Plan) : List PlanStep := ps.map ({ lane, step := · })
  let plan := steps [.metered c0 tool, .twin c1 c0, .metered c2 tool]
    ++ List.replicate 4 { lane, optional := true, step := .approveOnly c1 }
    ++ steps [.veto c0 false, .editToRejected c2, .dispatch c1, .stack c3 2, .drive c2, .drive c2]
  pure { g with nextCall := g.nextCall + 4, plan }

/-- Reach the session's and the turn's proposal limits on the same proposal, as `startBudgetPlan`
does for the approval budgets. Undefined tools fill the turns, since they count toward the limits. -/
def startLimitPlan (p : Policy) (g : GS) (lane : Nat) : Gen GS := do
  let s := (g.lane lane).s
  let some sessL := p.limits.maxProposalsPerSession | return g
  let some turnL := p.limits.maxProposalsPerTurn | return g
  let left := sessL - s.proposalsThisSession
  let tools := runnableTools p
  if turnL == 0 || left < turnL || left > 12 || tools.isEmpty then return g
  let tool ← pick tools
  let (plan, n) := (turnChunks left turnL).foldl (init := (([] : List Plan), g.nextCall)) fun (acc, n) k =>
    (acc ++ [.turnOver, .turnBegin] ++ (List.range k).map fun i => .unknownTool s!"c{n + i}", n + k)
  let plan := plan ++ [.metered s!"c{n}" tool, .metered s!"c{n + 1}" tool]
  pure { g with nextCall := n + 2, plan := plan.map ({ lane, step := · }) }

def quorumCalls (s : State) : List String :=
  (callsWhere s (· == .awaiting)).filterMap fun (id, c) =>
    if (Checks.clausesOf c.consent).any (·.k ≥ 2) || Checks.hasDistinctPair c.consent then some id else none

def editedCalls (s : State) : List String :=
  (s.calls.toList.filter fun (_, c) => c.generation > 0 && (c.status == .awaiting || c.status == .authorized)).map (·.1)

/-- Follow-ups the random walk reaches the start of but rarely completes (a call that needs several
approvals, an edited call, a vetoed digest, an edit whose escalators raise the consent, an automated
approver on `human_only` consent), and plans for policy shapes few traces have. Each
draws only in its situation, so other traces keep their random stream. -/
def startTargetPlan (p : Policy) (g : GS) : Gen GS := do
  let live := (List.range (max g.lanes 1)).filter fun i =>
    let l := g.lane i
    l.s.started && !l.s.ended && !l.dead
  if let some (lane, cid) := live.findSome? fun i => ((quorumCalls (g.lane i).s).head?).map (i, ·) then
    if ← chance 20 then return { g with plan := (List.replicate 5 (Plan.drive cid)).map ({ lane, step := · }) }
  if let some (lane, cid) := live.findSome? fun i => ((editedCalls (g.lane i).s).head?).map (i, ·) then
    if ← chance 20 then return { g with plan := [{ lane, step := .veto cid true }] }
  let toRejected := live.findSome? fun i =>
    let s := (g.lane i).s
    (callsWhere s (· == .awaiting)).findSome? fun (id, c) =>
      ((s.rejectedMemory.filter fun (t, d) => t == c.tool && d != c.digest).head?).map fun (_, d) => (i, id, d)
  if let some (lane, cid, d) := toRejected then
    if ← chance 30 then return { g with plan := [{ lane, step := .edit cid (some d) }] }
  let awaitingWhere (f : State → CallRec → Bool) := live.findSome? fun i =>
    let s := (g.lane i).s
    ((callsWhere s (· == .awaiting)).find? fun (_, c) => enforced p c && f s c).map (i, ·.1)
  if p.bindingMutable then
    if let some (lane, cid) := awaitingWhere fun s c => !(raisingEditors p s c).isEmpty then
      if ← chance 10 then return { g with plan := [{ lane, step := .raise cid }] }
  if let some (lane, cid) := awaitingWhere fun s c => !(machinesFor p s c).isEmpty then
    if ← chance 10 then return { g with plan := [{ lane, step := .machine cid }] }
  if let some (lane, cid) := live.findSome? fun i => ((callsWhere (g.lane i).s (· == .awaiting)).head?).map (i, ·.1) then
    if ← chance 6 then
      let pre ← if ← chance 50 then pure [Plan.edit cid none, .againCurrent cid] else pure []
      return { g with plan := (pre ++ List.replicate 5 (Plan.drive cid)).map ({ lane, step := · }) }
  let some lane := live.head? | return g
  let retrying (r : Requirements) := runnable r && r.retryAfterUnknown && r.maxAttempts ≥ 2
  if p.actions.any fun (_, r) => retrying r && !(retryWindows p r).isEmpty then
    if ← chance 8 then return ← startRetryPlan p g lane
  if p.actions.any fun (_, r) => retrying r && r.grantable.isSome then
    if ← chance 4 then return ← startGrantPlan p g lane
  if p.actions.any (!·.2.exposed) && (p.limits.maxFailuresPerSession.isSome || p.limits.maxConsecutiveFailures.isSome) then
    if ← chance 5 then return ← startEscalationPlan p g lane
  if !(stackKinds p (g.lane lane).s).isEmpty then
    if ← chance 3 then return ← startStackPlan p g lane
  if p.actions.any fun (_, r) => runnable r && moneyMeters p r ≥ 2 then
    if ← chance 4 then return ← startOverrunPlan p g lane
  if p.killSetsTombstone && g.lanes > 1 then
    if ← chance 3 then return ← startForeignKillPlan p g
  if g.lanes > 1 && p.actions.any fun (_, r) => runnable r && !(windowedPrincipal p r).isEmpty then
    if ← chance 4 then return ← startPrunePlan p g
  if p.limits.maxApprovalRequestsPerSession.isSome && p.limits.maxApprovalRequestsPerTurn.isSome then
    if ← chance 25 then return ← startBudgetPlan p g lane
  if p.limits.maxProposalsPerSession.isSome && p.limits.maxProposalsPerTurn.isSome then
    if ← chance 25 then return ← startLimitPlan p g lane
  return g

def startSidePlan (p : Policy) (g : GS) : Gen GS := do
  let lane ← below (max g.lanes 1)
  let s := (g.lane lane).s
  if !s.started || s.ended then return g
  match ← weighted [(2, 0), (1, 1), (2, 2), (4, 3), (2, 4), (3, 5), (3, 6), (3, 7), (2, 8), (2, 9), (2, 10)] with
  | 0 => startOverrunPlan p g lane
  | 1 => startRetryPlan p g lane
  | 2 => startUnknownToolPlan g lane
  | 10 => if p.killSetsTombstone then startKillClearPlan p g lane else startUnknownToolPlan g lane
  | 3 => startCapPlan p g lane
  | 4 => startEscalationPlan p g lane
  | 5 => startSyncPlan p g lane
  | 6 => startForeignKillPlan p g
  | 7 => startStackPlan p g lane
  | 8 => startGrantPlan p g lane
  | _ => startRejectionPlan p g lane

def onCallBody (s : State) (cid : String) : Nat → EventBody
  | 0 => .dispatch cid 1 "d1" none [] s!"k:{cid}"
  | 1 => .result cid .succeeded none false
  | 2 => .outcomeUnknown cid
  | 3 => .reconcile cid .failed none false
  | 4 => .cancel cid
  | 5 => .approve cid ⟨s.sessionId, cid, 0⟩ "alice" "d1" none none
  | 6 => .reject cid ⟨s.sessionId, cid, 0⟩ "alice"
  | _ => .approvalExpire cid ⟨s.sessionId, cid, 0⟩

partial def planBody (p : Policy) (s : State) : Plan → Gen (Option EventBody)
  | .propose cid gid => do
    match s.grants.get? gid with
    | none => pure none
    | some gr =>
      let r := reqOf p gr.tool
      let digest ← match gr.digest with | some d => pure d | none => pick digests
      let cost ← match gr.maxCost with
        | some mc => pure (some ⟨← below 3, mc.currency⟩)
        | none => genCost p r
      let esc := r.escalate.map fun (n, e) => (n, Checks.trivialC r.consent && e.grantable)
      pure (some (.propose cid gr.tool digest cost (r.guards.map (·, true)) esc))
  | .dispatch cid =>
    pure ((s.calls.get? cid).map fun c => .dispatch cid (c.attempts + 1) c.digest c.cost c.proposedGuards s!"k:{cid}")
  | .unknown cid => pure (if s.calls.contains cid then some (.outcomeUnknown cid) else none)
  | .cancel cid => pure (if s.calls.contains cid then some (.cancel cid) else none)
  | .metered cid tool => do
    let r := reqOf p tool
    let cost ← match moneyCurrency p r with
      | some cur => pure (some ⟨← below 3, cur⟩)
      | none => pure none
    pure (some (.propose cid tool (← pick digests) cost (r.guards.map (·, true)) (r.escalate.map (·.1, false))))
  | .result cid => pure (if s.calls.contains cid then some (.result cid .succeeded none false) else none)
  | .sync => pure (some (.ledgerSync {}))
  | .unknownTool cid => pure (some (.propose cid "zz" "d1" none [] []))
  | .onCall cid k => pure (some (onCallBody s cid k))
  | .reuse cid => do
    let tool ← pick (toolsOf p)
    let r := reqOf p tool
    let guards := r.guards.map (·, true) ++ [("gx", true)]
    let esc := r.escalate.map (·.1, false) ++ [("ex", true)]
    pure (some (.propose cid tool (← pick digests) (← genCost p r) guards esc))
  | .overrun cid =>
    pure ((s.calls.get? cid).map fun c => .result cid .succeeded (some ((c.cost.map (·.amount)).getD 0 + 2)) false)
  | .lateOverrun cid =>
    pure ((s.calls.get? cid).map fun c => .reconcile cid .succeeded (some ((c.cost.map (·.amount)).getD 0 + 2)) false)
  | .kill => pure (some .kill)
  | .reset => pure (some .reset)
  | .finish => pure (some .sessionEnd)
  | .clearStore => pure (some .turnEnd)
  | .settle cid => do
    let ne ← chance 50
    pure (if s.calls.contains cid then some (.reconcile cid .succeeded none ne) else none)
  | .sized cid tool amount => do
    let r := reqOf p tool
    let cost := (moneyCurrency p r).map (⟨amount, ·⟩)
    pure (some (.propose cid tool (← pick digests) cost (r.guards.map (·, true)) (r.escalate.map (·.1, false))))
  | .report cid o actual ne late =>
    pure (if s.calls.contains cid then some (if late then .reconcile cid o actual ne else .result cid o actual ne) else none)
  | .syncWith _ => pure (some (.ledgerSync {}))
  | .drive cid => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      if c.status == .authorized then
        pure (some (.dispatch cid (c.attempts + 1) c.digest c.cost c.proposedGuards s!"k:{cid}"))
      else planBody p s (.approveOnly cid)
  | .approveOnly cid => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      if c.status != .awaiting then pure none
      else
        let fresh := s.approvers.toList.filter fun (_, i) => !c.tally.any (·.1 == i.principal) && rawEligible p s c.consent i
        let short := (Checks.clausesOf c.consent).filter fun cl =>
          (c.tally.filter fun (_, id) => (s.approvers.get? id).any (Checks.eligibleFor p s.requester · cl)).length < cl.k
        let useful := fresh.filter fun (_, i) => short.any (Checks.eligibleFor p s.requester i ·)
        let pool := if useful.isEmpty then fresh else useful
        if pool.isEmpty then pure none
        else pure (some (.approve cid ⟨s.sessionId, cid, c.generation⟩ (← pick (pool.map (·.1))) c.digest c.cost none))
  | .ack stale => do
    let elig := s.approvers.toList.filter fun (_, i) => Checks.escalationEligible p i
    let who ← if elig.isEmpty then pickApprover s else pick (elig.map (·.1))
    pure (some (.escalationAck who (if stale then s.escalations + 1 else s.escalations)))
  | .again cid =>
    pure ((s.calls.get? cid).map fun c => .propose cid c.tool c.proposedDigest c.proposedCost c.proposedGuards c.proposedEscalators)
  | .veto cid older => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      if (older && c.generation == 0) || !(c.status == .awaiting || c.status == .authorized) then pure none
      else
        let elig := s.approvers.toList.filter fun (_, i) =>
          if Checks.trivialC c.consent then i.principal != "agent" && i.roles.any p.approverRoles.contains
          else rawEligible p s c.consent i
        let gen ← if older then pure (c.generation - 1 - (← below c.generation)) else pure c.generation
        if elig.isEmpty then pure none
        else pure (some (.reject cid ⟨s.sessionId, cid, gen⟩ (← pick (elig.map (·.1)))))
  | .editToRejected cid => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      let ds := (s.rejectedMemory.filter fun (t, d) => t == c.tool && d != c.digest).map (·.2)
      if ds.isEmpty then planBody p s (.drive cid) else planBody p s (.edit cid (some (← pick ds)))
  | .revoke perm => pure (some (.permissionRevoke perm))
  | .twin cid src =>
    pure ((s.calls.get? src).map fun c =>
      let r := reqOf p c.tool
      .propose cid c.tool c.proposedDigest c.proposedCost (r.guards.map (·, true)) (r.escalate.map (·.1, false)))
  | .dispatchOff cid =>
    pure ((s.calls.get? cid).map fun c => .dispatch cid (c.attempts + 1) "dx" c.cost c.proposedGuards s!"k:{cid}")
  | .turnOver => pure (some .turnEnd)
  | .turnBegin => pure (some (.turnStart false))
  | .grantNew gid tool digest scope maxCost exp => do
    let r := reqOf p tool
    let consents := r.consent :: (r.escalate.filter (·.2.grantable)).map (·.2.consent)
    let creators := s.approvers.toList.filter fun (_, i) =>
      consents.all fun c => (Checks.clausesOf c).all (Checks.eligibleFor p s.requester i ·)
    let some gr := r.grantable | pure none
    if creators.isEmpty then pure none
    else pure (some (.grantCreate gid (← pick (creators.map (·.1))) tool digest scope gr.maxUses maxCost none exp "rs"))
  | .edit cid digest => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      let r := reqOf p c.tool
      let editors := s.approvers.toList.filter fun (_, i) => rawEligible p s c.consent i
      if c.status != .awaiting || editors.isEmpty then pure none
      else
        let nd ← match digest with | some d => pure d | none => pick (digests.filter (· != c.digest))
        let nc ← if ← chance 30 then pure none else pure c.cost
        let ed : Edit := { newDigest := nd, newCost := nc, escalators := r.escalate.map (·.1, false) }
        pure (some (.approve cid ⟨s.sessionId, cid, c.generation⟩ (← pick (editors.map (·.1))) c.digest c.cost (some ed)))
  | .againCurrent cid =>
    pure ((s.calls.get? cid).map fun c => .propose cid c.tool c.digest c.cost c.proposedGuards c.proposedEscalators)
  | .stack cid kind => do
    let avail := p.actions.filter fun (t, r) => r.exposed && !s.blockedTools.contains t
    let held (r : Requirements) := r.permission.all s.permissions.contains
    let money (r : Requirements) := (moneyCurrency p r).isSome
    match kind with
    | 0 =>
      let cands := avail.filter fun (_, r) => !held r && !r.guards.isEmpty
      if cands.isEmpty then pure none
      else
        let (tool, r) ← pick cands
        pure (some (.propose cid tool (← pick digests) (← genCost p r) (r.guards.map (·, false)) (r.escalate.map (·.1, false))))
    | 1 =>
      let cands := avail.filter fun (_, r) => held r && !r.guards.isEmpty && money r
      if cands.isEmpty then pure none
      else
        let (tool, r) ← pick cands
        pure (some (.propose cid tool (← pick digests) none (r.guards.map (·, false)) (r.escalate.map (·.1, false))))
    | _ =>
      let cands := s.rejectedMemory.filter fun (t, _) => (Checks.reqOf p t).any fun r =>
        r.exposed && held r && (kind == 2 || !Checks.trivialC r.consent)
      if cands.isEmpty then pure none
      else
        let (tool, digest) ← pick cands
        let r := reqOf p tool
        let floor := (r.consentIfCostOver.map (·.amount)).getD 1
        let cost ← if money r && kind == 2 then badCost p r else pure ((moneyCurrency p r).map (⟨floor, ·⟩))
        pure (some (.propose cid tool digest cost (r.guards.map (·, true)) (r.escalate.map (·.1, false))))
  | .raise cid => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      let editors := raisingEditors p s c
      let fresh := digests.filter fun d => d != c.digest && !s.rejectedMemory.contains (c.tool, d)
      if c.status != .awaiting || editors.isEmpty || fresh.isEmpty then pure none
      else
        -- A missing escalator fires as a true one does.
        let fired ← (reqOf p c.tool).escalate.filterMapM fun (n, _) => do pure (if ← chance 30 then none else some (n, true))
        let ed : Edit := { newDigest := ← pick fresh, newCost := c.cost, escalators := fired }
        pure (some (.approve cid ⟨s.sessionId, cid, c.generation⟩ (← pick editors) c.digest c.cost (some ed)))
  | .machine cid => do
    match s.calls.get? cid with
    | none => pure none
    | some c =>
      let ms := machinesFor p s c
      if c.status != .awaiting || ms.isEmpty then pure none
      else pure (some (.approve cid ⟨s.sessionId, cid, c.generation⟩ (← pick ms) c.digest c.cost none))

/-- The next planned event and the steps after it; a plan stops at a step that does not apply unless
the step is optional. -/
def nextPlanned (p : Policy) (g : GS) : List PlanStep → Gen (Option (PlanStep × EventBody) × List PlanStep)
  | [] => pure (none, [])
  | ps :: rest => do
    let l := g.lane ps.lane
    if l.dead || (l.s.ended && !ps.ended) then return (none, [])
    match ← planBody p l.s ps.step with
    | some b => pure (some (ps, b), rest)
    | none => if ps.optional then nextPlanned p g rest else pure (none, [])

end WritTests.Fuzz
