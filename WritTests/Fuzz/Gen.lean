import WritTests.Fuzz.Plans

open Writ

namespace WritTests.Fuzz

abbrev StepFn := Policy → State → Event → State × Verdict

/-- Altered ledgers only where the session's own state lets the kernel see the alteration, so an
accepted sync never breaks theorem 9's premise; the binding otherwise sends the stored ledger. -/
def syncLedger (w : World) (s : State) : SyncMode → Ledger
  | .store => w.store
  | .older => if s.ledger.version > 0 then { w.store with version := s.ledger.version - 1 } else w.store
  | .clearTomb => if s.ledger.tombstone && !s.ended then { w.store with tombstone := false } else w.store
  | .foreignEntry => { w.store with entries := w.store.entries ++ [⟨"usd", s.sessionId, "zz", 0, 1, true, 0, 0⟩] }
  | .reorder =>
    let own := w.store.entries.filter (·.session == s.sessionId)
    { w.store with entries := w.store.entries.filter (·.session != s.sessionId) ++ own.reverse }
  | .dropReservation =>
    match w.store.entries.find? fun e => e.session == s.sessionId && !e.committed with
    | some e => { w.store with entries := w.store.entries.erase e }
    | none => w.store
  | .duplicateReservation =>
    match w.store.entries.find? fun e => e.session == s.sessionId && !e.committed with
    | some e => { w.store with entries := w.store.entries ++ [e] }
    | none => w.store

def fillBody (w : World) (l : Lane) (g : GStep) : EventBody :=
  match g.body with
  | .sessionStart sid pd req perms apprs _ => .sessionStart sid pd req perms apprs w.store
  | .ledgerSync _ => .ledgerSync (syncLedger w l.s g.sync)
  | b => b

def stamp (w : World) (l : Lane) (g : GStep) : Event :=
  let seq := if g.intent == .staleSeq then l.s.lastSeq else l.n + 1
  let lag := if (g.lane % w.lanes.size) % 2 == 1 then w.skew else 0
  -- Hosts send max(last_time, now), so a lagging clock never makes a lane's time go back.
  let time := if g.intent == .timeBack then l.s.lastTime - (g.dt + 1) else max l.s.lastTime (w.clock + g.dt - lag)
  let version := if g.intent == .wrongVersion then l.s.version + 1 else l.s.version
  ⟨seq, time, version, none, fillBody w l g⟩

def readVersion (s : State) (e : Event) : Nat :=
  match e.body with
  | .ledgerSync l | .sessionStart _ _ _ _ _ l => l.version
  | _ => s.ledger.version

def accepted : Verdict → Bool
  | .ok .. => true
  | .rejected _ => false

/-- One store under section 7: compare-and-swap on the state version and the ledger version the
step read; the ledger is written only if the step changed its version. `none` is a conflict. -/
def commit (w : World) (l : Lane) (e : Event) (s' : State) (v : Verdict) : Option (World × Lane) :=
  let rv := readVersion l.s e
  let changed := s'.ledger.version != rv
  if accepted v && (w.strict || changed) && w.store.version != rv then none
  else
    let w := { w with clock := max w.clock e.time, store := if accepted v && changed then s'.ledger else w.store }
    some (w, { l with s := s', n := l.n + 1 })

def feed (stepF : StepFn) (p : Policy) (w : World) (g : GStep) : World × List Checks.Item :=
  if g.oob then
    if w.store.tombstone then
      ({ w with store := { w.store with tombstone := false, version := w.store.version + 1 } }, [.storeClear])
    else (w, [])
  else
    let l := w.lane g.lane
    let (w, l) := match g.body with
      | .sessionStart .. =>
        if l.dead || l.s.ended then
          ({ w with nextInst := w.nextInst + 1 }, ({ s := State.initial "pd", inst := w.nextInst } : Lane))
        else (w, l)
      | _ => (w, l)
    if l.dead then (w.setLane g.lane l, [])
    else
      let e := stamp w l g
      let (s', v) := stepF p l.s e
      match commit w l e s' v with
      | some (w, l') => (w.setLane g.lane l', [.step ⟨l.inst, l.s, e, v, s'⟩])
      | none =>
        let se : Event := ⟨l.n + 1, e.time, l.s.version, none, .ledgerSync w.store⟩
        let (s2, v2) := stepF p l.s se
        let syncItem := Checks.Item.step ⟨l.inst, l.s, se, v2, s2⟩
        let w := { w with clock := max w.clock e.time }
        let l2 := { l with s := s2, n := l.n + 1 }
        if !accepted v2 then (w.setLane g.lane { l2 with dead := true }, [syncItem])
        else
          let e2 : Event := ⟨l2.n + 1, e.time, s2.version, none, fillBody w l2 g⟩
          let (s3, v3) := stepF p s2 e2
          match commit w l2 e2 s3 v3 with
          | some (w, l3) => (w.setLane g.lane l3, [syncItem, .step ⟨l.inst, s2, e2, v3, s3⟩])
          | none => (w.setLane g.lane l2, [syncItem])

def replayWith (stepF : StepFn) (g : GTrace) : Checks.Trace :=
  let (_, items) := g.steps.foldl (init := (World.init g, (#[] : Array Checks.Item))) fun (w, acc) st =>
    let (w, its) := feed stepF g.policy w st
    (w, acc ++ its.toArray)
  { policy := g.policy, initLedger := g.initLedger, items := items.toList }

def replay (g : GTrace) : Checks.Trace := replayWith step g

/-- Templates bias one feature family: 1 consent groups and escalators, 2 grants, 3 meters and
retries, 4 limits and escalation, 5 several sessions on principal meters; 0 mixes everything. -/
structure Tpl where
  n : Nat

def genRoleSet (ar : List String) : Gen (Option (List String)) := do
  if ← chance 45 then pure none else pure (some (← nonEmptySubset ar 45))

def genClause (ar : List String) (maxK : Nat) : Gen Clause := do
  pure ⟨1 + (← below maxK), ← genRoleSet ar, ← chance 50, ← chance 35⟩

def genConsent (ar : List String) (t : Nat) : Gen Consent := do
  match ← weighted [(3, 0), (3, 1), (4, 2), (if t == 1 then 6 else 2, 3), (if t == 1 then 3 else 1, 4)] with
  | 0 => pure .none
  | 1 => pure .perCall
  | 2 => pure ⟨[⟨[← genClause ar 3], false⟩]⟩
  | 3 =>
    let n := 2 + (← below 2)
    let cls ← (List.range n).mapM fun _ => genClause ar 2
    pure (.allOf cls (← chance 60))
  | _ => pure ⟨[⟨[← genClause ar 2], false⟩, ⟨[← genClause ar 1, ← genClause ar 1], ← chance 50⟩]⟩

def singleConsent (ar : List String) : Gen Consent := do
  match ← weighted [(2, 0), (3, 1), (4, 2)] with
  | 0 => pure .none
  | 1 => pure .perCall
  | _ => pure ⟨[⟨[← genClause ar 1], false⟩]⟩

def meterPool : List (String × MeterUnit) :=
  [("usd", .money "USD"), ("usd2", .money "USD"), ("eur", .money "EUR"), ("calls", .calls)]

def genWindow (t : Nat) : Gen (Option Nat) := do
  match ← weighted [(50, 0), (if t == 3 then 20 else 8, 1), (35, 2)] with
  | 0 => pure none
  | 1 => pure (some 1)
  | _ => pure (some (2 + (← below 50)))

def genMeter (u : MeterUnit) (t : Nat) : Gen MeterSpec := do
  pure
    { unit := u
      cap := ← if ← chance 12 then pure none else some <$> ((if u == .calls then 1 else 3) + ·) <$> below (if t == 3 || t == 5 then 12 else 25)
      scope := ← if t == 5 then weighted [(80, .principal), (20, .session)] else pick [.session, .principal]
      windowMs := ← genWindow t
      maxPerCall := ← if u != .calls && (← chance 35) then some <$> (2 + ·) <$> below 8 else pure none }

def genActionMeters (meters : List (String × MeterSpec)) (t : Nat) : Gen (List String) := do
  if meters.isEmpty then return []
  let k ← weighted [(if t == 3 || t == 5 then 15 else 55, 0), (30, 1), (if t == 3 || t == 5 then 30 else 12, 2)]
  if k == 0 then return []
  let first ← pick meters
  if k == 1 then return [first.1]
  let cur := currencyOf first.2.unit
  let others := meters.filter fun (n, m) => n != first.1 && (currencyOf m.unit == none || cur == none || currencyOf m.unit == cur)
  if others.isEmpty then return [first.1]
  let money := (first :: [← pick others]).filter fun (_, m) => (currencyOf m.unit).isSome
  let curs := (money.filterMap fun (_, m) => currencyOf m.unit).eraseDups
  if curs.length > 1 then return [first.1]
  return [first.1, (← pick others).1].eraseDups

def genAction (ar : List String) (meters : List (String × MeterSpec)) (t : Nat) : Gen Requirements := do
  let ms ← genActionMeters meters t
  let metered := !ms.isEmpty
  let grantable ← chance (if t == 2 then 85 else 20)
  let consent ← if grantable then singleConsent ar else genConsent ar t
  let anyArgs ← chance (if t == 2 then 55 else 30)
  let gr : Option Grantable ← if !grantable then pure none else do
    let dur ← if anyArgs || (← chance 50) then some <$> (5 + ·) <$> below 40 else pure none
    pure (some { scope := ← pick [.turn, .session], maxUses := 1 + (← below 3), maxDurationMs := dur
                 anyArgs, allowAnyArgsMetered := anyArgs && metered })
  let nEsc ← weighted [(if t == 1 then 30 else 60, 0), (30, 1), (if t == 1 then 30 else 10, 2)]
  let esc ← (List.range nEsc).mapM fun i => do
    let g := grantable && (← chance 60)
    let c ← if g then singleConsent (if ← chance 50 then [] else ar) else genConsent ar 1
    let c := if g && c.groups.isEmpty then Consent.perCall else c
    pure (s!"e{i}", ({ consent := c, grantable := g } : Escalator))
  let esc := if grantable && consent.groups.isEmpty && !esc.any (·.2.grantable) then
      esc ++ [("eg", { consent := .perCall, grantable := true })]
    else esc
  let retry ← chance (if t == 3 then 50 else if grantable then (if t == 2 then 65 else 45) else 20)
  pure
    { permission := ← if ← chance (if t == 2 then 10 else 30) then some <$> pick ["p0", "p1"] else pure none
      consent
      consentIfCostOver := ← if ← chance 25 then
          (fun a c => some ⟨a, c⟩) <$> ((1 + ·) <$> below 6) <*> pick currencies
        else pure none
      escalate := esc
      grantable := gr
      idempotent := retry || (← chance 20)
      retryAfterUnknown := retry
      maxAttempts := ← if retry then weighted [(20, 1), (50, 2), (30, 3)] else (1 + ·) <$> below 3
      guards := ← if ← chance (if t == 2 then 5 else 20) then pure ["g0"] else pure []
      meters := ms
      approvalTtlMs := ← if ← chance 15 then some <$> (1 + ·) <$> below 20 else pure none
      authorizedTtlMs := ← if ← chance 15 then some <$> (1 + ·) <$> below 20 else pure none
      exposed := ← chance 94
      mode := ← weighted [(85, none), (8, some .logOnly), (7, some .enforce)] }

def genLimits (t : Nat) : Gen Limits := do
  let pct := if t == 4 then 60 else if t == 2 then 5 else 20
  let opt (lo span : Nat) : Gen (Option Nat) := do
    if ← chance pct then pure (some (lo + (← below span))) else pure none
  pure
    { maxStepsPerTurn := ← opt 1 4, maxProposalsPerTurn := ← opt 1 5
      maxApprovalRequestsPerTurn := ← opt 1 3, maxProposalsPerSession := ← opt 2 12
      maxApprovalRequestsPerSession := ← opt 1 5
      maxConsecutiveFailures := ← if ← chance (if t == 4 then 70 else 25) then some <$> (1 + ·) <$> below 3 else pure none
      maxFailuresPerSession := ← if ← chance (if t == 4 then 50 else 20) then some <$> (1 + ·) <$> below 4 else pure none
      escalationScope := ← pick [.session, .tool]
      approvalTtlMs := ← opt 1 18, authorizedTtlMs := ← opt 1 18 }

def fallbackPolicy : Policy :=
  { approverRoles := ["owner", "admin"], actions := [("t0", { consent := Consent.perCall }), ("t1", {})] }

def genPolicyOnce (t : Nat) : Gen Policy := do
  let ar ← nonEmptySubset rolePool 60
  let meterNames ← subset meterPool (if t == 3 || t == 5 then 75 else 45)
  let meters ← meterNames.mapM fun (n, u) => do pure (n, ← genMeter u t)
  let n := 3 + (← below 4)
  let actions ← (List.range n).mapM fun i => do pure (s!"t{i}", ← genAction ar meters t)
  -- An action on two money meters of one currency, so one report can overrun both.
  let both := meters.any (·.1 == "usd") && meters.any (·.1 == "usd2")
  let actions := if both && (t == 3 || t == 5) then actions ++ [("tm", { meters := ["usd", "usd2"] })] else actions
  pure
    { mode := ← weighted [(9, .enforce), (1, .logOnly)]
      approverRoles := ar
      escalationRoles := ← if ← chance 40 then some <$> nonEmptySubset ar 50 else pure none
      meters, limits := ← genLimits t, actions
      bindingMutable := ← chance 80
      killSetsTombstone := ← chance (if t == 5 then 60 else 30) }

def genPolicy (t : Nat) : Gen Policy := do
  let rec go : Nat → Gen Policy
    | 0 => pure fallbackPolicy
    | n + 1 => do
      let p ← genPolicyOnce t
      if p.check.isEmpty then pure p else go n
  go 30

/-- Defects section 5 says `writ check` refuses; the bad-policy mode asserts that it does. -/
def defects : List String :=
  [ "zero-window", "zero-consecutive-failures", "zero-session-failures", "unexposed-log-only"
  , "mixed-currency", "duplicate-meter", "empty-role-set", "zero-quorum", "grantable-quorum-2"
  , "grantable-escalator-without-grantable", "retry-without-idempotent", "grantable-without-relevant-consent"
  , "grantable-distinct-group", "any-args-without-duration", "any-args-metered", "zero-max-uses" ]

def withAction (p : Policy) (r : Requirements) : Policy := { p with actions := p.actions ++ [("tbad", r)] }

def withMeters (p : Policy) : Policy :=
  let add := [("bu", ({ unit := .money "USD", cap := some 10 } : MeterSpec)), ("be", { unit := .money "EUR", cap := some 10 })]
  { p with meters := p.meters ++ add }

def injectDefect (p : Policy) : String → Policy
  | "zero-window" => { p with meters := p.meters ++ [("bw", { unit := .calls, cap := some 5, windowMs := some 0 })] }
  | "zero-consecutive-failures" => { p with limits := { p.limits with maxConsecutiveFailures := some 0 } }
  | "zero-session-failures" => { p with limits := { p.limits with maxFailuresPerSession := some 0 } }
  | "unexposed-log-only" => withAction p { exposed := false, mode := some .logOnly }
  | "mixed-currency" => withAction (withMeters p) { meters := ["bu", "be"] }
  | "duplicate-meter" => withAction (withMeters p) { meters := ["bu", "bu"] }
  | "empty-role-set" => withAction p { consent := .quorum 1 (some []) true false }
  | "zero-quorum" => withAction p { consent := .quorum 0 none true false }
  | "grantable-quorum-2" => withAction p { consent := .quorum 2 none true false, grantable := some { scope := .session, maxUses := 2 } }
  | "grantable-escalator-without-grantable" =>
    withAction p { consent := .perCall, escalate := [("eb", { consent := .perCall, grantable := true })] }
  | "retry-without-idempotent" => withAction p { retryAfterUnknown := true, idempotent := false, maxAttempts := 2 }
  | "grantable-without-relevant-consent" => withAction p { grantable := some { scope := .session, maxUses := 2 } }
  | "grantable-distinct-group" =>
    withAction p { consent := .allOf [⟨1, none, true, false⟩, ⟨1, none, true, false⟩] true
                   grantable := some { scope := .session, maxUses := 2 } }
  | "any-args-without-duration" =>
    withAction p { consent := .perCall, grantable := some { scope := .session, maxUses := 2, anyArgs := true } }
  | "any-args-metered" =>
    withAction (withMeters p) { consent := .perCall, meters := ["bu"]
                                grantable := some { scope := .session, maxUses := 2, maxDurationMs := some 10, anyArgs := true } }
  | "zero-max-uses" => withAction p { consent := .perCall, grantable := some { scope := .session, maxUses := 0 } }
  | _ => p

/-- The `Policy.check` problem each planted defect must produce. -/
def plantedProblem : String → Problem → Bool
  | "zero-window", .zeroWindow _ => true
  | "zero-consecutive-failures", .zeroFailureLimit => true
  | "zero-session-failures", .zeroSessionFailureLimit => true
  | "unexposed-log-only", .unexposedLogOnly a => a == "tbad"
  | "mixed-currency", .mixedCurrencies a => a == "tbad"
  | "duplicate-meter", .duplicateMeterInAction a _ => a == "tbad"
  | "empty-role-set", .emptyRoles a => a == "tbad"
  | "zero-quorum", .zeroQuorum a => a == "tbad"
  | "grantable-quorum-2", .grantableNeedsSingleApproval a => a == "tbad"
  | "grantable-escalator-without-grantable", .grantableEscalatorWithoutGrantable a _ => a == "tbad"
  | "retry-without-idempotent", .retryNeedsIdempotent a => a == "tbad"
  | "grantable-without-relevant-consent", .grantableWithoutConsent a => a == "tbad"
  | "grantable-distinct-group", .grantableNeedsSingleApproval a => a == "tbad"
  | "any-args-without-duration", .anyArgsNeedsDuration a => a == "tbad"
  | "any-args-metered", .anyArgsMetered a => a == "tbad"
  | "zero-max-uses", .zeroMaxUses a => a == "tbad"
  | _, _ => false

def plantedFound (d : String) (p : Policy) : Bool := p.check.any (plantedProblem d)

def genBadPolicy (seed : Nat) : String × Policy :=
  let gen : Gen (String × Policy) := do
    let p ← genPolicy (← below 6)
    let d ← pick defects
    pure (d, injectDefect p d)
  gen.run' (mix (UInt64.ofNat (seed + 0x5eed)))

def genInitLedger (p : Policy) : Gen Ledger := do
  -- Seeded entries more often where a principal claim can later meet the foreign ones below.
  let both := p.meters.any (fun (_, m) => m.scope == .session && m.windowMs.isSome)
    && p.actions.any fun (_, r) => r.exposed && r.permission.isNone
      && (Checks.metersOf p r).any (·.2.scope == .principal)
  match ← weighted [(if both then 40 else 78, 0), (2, 1), (if both then 58 else 20, 2)] with
  | 1 => pure { tombstone := true, version := 1 }
  | 2 =>
    let principal := p.meters.filter (·.2.scope == .principal)
    let entries ← principal.mapM fun (n, spec) => do
      pure (⟨n, "s0", "old", 0, spec.cap.getD 5 - (← below 3), true, 0, 0⟩ : MeterEntry)
    -- What another policy may leave under the name of one of this policy's windowed session meters:
    -- dated 0, they leave that window once the clock passes it, yet the principal list keeps them.
    let foreign := (p.meters.filter fun (_, m) => m.scope == .session && m.windowMs.isSome).map fun (n, _) =>
      (⟨n, "s0", "old", 0, 1, true, 0, 0⟩ : MeterEntry)
    pure { version := 3, entries := entries ++ foreign }
  | _ => pure {}

def genDt : Gen Nat := do
  match ← weighted [(60, 0), (30, 1), (10, 2)] with
  | 0 => below 3
  | 1 => (3 + ·) <$> below 6
  | _ => (15 + ·) <$> below 45

def genIntent : Gen Intent :=
  weighted [(94, .valid), (2, .staleSeq), (2, .timeBack), (2, .wrongVersion)]

def pickCall (s : State) (preferred : List (String × CallRec)) (pct : Nat) : Gen String := do
  if !preferred.isEmpty && (← chance pct) then pick (preferred.map (·.1))
  else
    let all := s.calls.keys
    if all.isEmpty || (← chance 10) then pure "c99" else pick all

def genGuards (r : Requirements) : Gen (List (String × Bool)) := do
  let gs ← r.guards.filterMapM fun g => do
    match ← weighted [(88, 0), (8, 1), (4, 2)] with
    | 0 => pure (some (g, true))
    | 1 => pure (some (g, false))
    | _ => pure none
  if ← chance 5 then pure (gs ++ [("gx", false)]) else pure gs

def genEscalators (r : Requirements) : Gen (List (String × Bool)) :=
  r.escalate.filterMapM fun (n, _) => do
    match ← weighted [(55, 0), (30, 1), (15, 2)] with
    | 0 => pure (some (n, false))
    | 1 => pure (some (n, true))
    | _ => pure none

def genSessionStart (g : GS) (lane : Nat) : Gen (GS × EventBody) := do
  let l := g.lane lane
  let inst := if l.dead || l.s.ended then g.w.nextInst else l.inst
  let withEntries := (g.w.store.entries.map (·.session)).eraseDups
  let sid ← if !withEntries.isEmpty && (← chance 25) then pick withEntries else pure s!"s{inst + 1}"
  let extra ← subset (startPool.drop 2) 45
  let reused := withEntries.contains sid
  let pd ← weighted [(if reused then 60 else 97, "pd"), (if reused then 40 else 3, "px")]
  let perms ← subset ["p0", "p1"] 60
  pure ({ g with usedSids := g.usedSids ++ [sid] }, .sessionStart sid pd "u1" perms (startPool.take 2 ++ extra) {})

/-- A rejected (tool, digest) proposed again under a fresh id, often with a bad cost or false guards,
so that several propose checks fail at once. -/
def genStackedPropose (p : Policy) (g : GS) (s : State) : Gen (GS × EventBody) := do
  let (tool, digest) ← pick s.rejectedMemory
  let r := reqOf p tool
  let cost ← if ← chance 50 then badCost p r else genCost p r
  let guards ← if ← chance 30 then pure (r.guards.map (·, false)) else genGuards r
  pure ({ g with nextCall := g.nextCall + 1 }, .propose s!"c{g.nextCall}" tool digest cost guards (← genEscalators r))

def genFreshPropose (p : Policy) (g : GS) (s : State) : Gen (GS × EventBody) := do
  -- A blocked tool, or an unexposed one while the session is escalated. Draws only while something
  -- is blocked, so other traces keep their random stream.
  if s.escalated || !s.blockedTools.isEmpty then
    let hidden := (p.actions.filter (!·.2.exposed)).map (·.1)
    let targets := (if s.escalated then hidden else []) ++ s.blockedTools
    if !targets.isEmpty then
      if ← chance 30 then
        let tool ← pick targets
        let r := reqOf p tool
        let body := EventBody.propose s!"c{g.nextCall}" tool (← pick digests) (← genCost p r) (← genGuards r) (← genEscalators r)
        return ({ g with nextCall := g.nextCall + 1 }, body)
  -- Draws only once the session has rejected something, so other traces keep their random stream.
  if !s.rejectedMemory.isEmpty then
    if ← chance 30 then return ← genStackedPropose p g s
  let live := liveGrants s
  let aimed ← if live.isEmpty then pure none else do
    if ← chance 75 then pure (some (← pick live)) else pure none
  let tool ← match aimed with
    | some gr => pure gr.tool
    | none => if ← chance 5 then pure "zz" else pick (toolsOf p)
  let r := reqOf p tool
  let digest ← match aimed.bind (·.digest) with
    | some d => pure d
    | none => pick digests
  let esc ← if aimed.isSome && (← chance 80) then pure (r.escalate.map (·.1, false)) else genEscalators r
  -- A cost-capped grant only covers a cost that fits what is left of its cap.
  let cost ← match aimed.bind (·.maxCost) with
    | some mc => if ← chance 80 then pure (some ⟨← below 3, mc.currency⟩) else genCost p r
    | none => genCost p r
  pure ({ g with nextCall := g.nextCall + 1 }, .propose s!"c{g.nextCall}" tool digest cost (← genGuards r) esc)

def genPropose (p : Policy) (g : GS) (s : State) : Gen (GS × EventBody) := do
  -- Under a log_only policy, a repeat of an unexposed call while escalated must still report the
  -- call's own denial. Draws only in that state, so other traces keep their random stream.
  let unexposed := s.calls.keys.filter fun id => (s.calls.get? id).any fun c => (Checks.reqOf p c.tool).any (!·.exposed)
  if p.mode == .logOnly && s.escalated && !unexposed.isEmpty then
    if ← chance 80 then
      let id ← pick unexposed
      if let some c := s.calls.get? id then
        return (g, .propose id c.tool c.proposedDigest c.proposedCost c.proposedGuards c.proposedEscalators)
  let kind ← weighted [(80, 0), (8, 1), (6, 2), (6, 3)]
  if kind == 0 || s.calls.isEmpty then genFreshPropose p g s
  else
    let edited := s.calls.keys.filter fun id => (s.calls.get? id).any (·.generation > 0)
    let id ← if kind == 2 && !edited.isEmpty && (← chance 70) then pick edited else pick s.calls.keys
    match s.calls.get? id with
    | none => genFreshPropose p g s
    | some c =>
      match kind with
      | 1 => pure (g, .propose id c.tool c.proposedDigest c.proposedCost c.proposedGuards c.proposedEscalators)
      | 2 => pure (g, .propose id c.tool c.digest c.cost c.proposedGuards c.proposedEscalators)
      | _ => pure (g, .propose id c.tool (← pick digests) c.proposedCost c.proposedGuards c.proposedEscalators)

def genRid (s : State) (id : String) (forReject : Bool) : Gen RequestId := do
  let gen := ((s.calls.get? id).map (·.generation)).getD 0
  if forReject && gen > 0 && (← chance 25) then return ⟨s.sessionId, id, gen - 1 - (← below gen)⟩
  match ← weighted [(88, 0), (5, 1), (if gen > 0 then 4 else 0, 2), (3, 3)] with
  | 0 => pure ⟨s.sessionId, id, gen⟩
  | 1 => pure ⟨s.sessionId, id, gen + 1⟩
  | 2 => pure ⟨s.sessionId, id, gen - 1⟩
  | _ => pure ⟨"s0", id, gen⟩

def genApprove (p : Policy) (s : State) : Gen EventBody := do
  let id ← pickCall s (callsWhere s fun st => st == .awaiting) 88
  let rec? := s.calls.get? id
  let tool := (rec?.map (·.tool)).getD "t0"
  let r := reqOf p tool
  let digest := (rec?.map (·.digest)).getD "d1"
  let cost := rec?.bind (·.cost)
  let rd ← if ← chance 93 then pure digest else pick digests
  let rc ← if ← chance 93 then pure cost else genCost p r
  let edit ← if ← chance 14 then do
      let nc ← if ← chance 30 then pure none else genCost p r
      let rejected := (s.rejectedMemory.filter (·.1 == tool)).map (·.2)
      let nd ← if !rejected.isEmpty && (← chance 50) then pick rejected else pick digests
      pure (some { newDigest := nd, newCost := nc, escalators := ← genEscalators r })
    else pure none
  let tally := (rec?.map (·.tally)).getD []
  let consent := (rec?.map (·.consent)).getD .none
  let fresh := s.approvers.toList.filter fun (_, i) =>
    !tally.any (·.1 == i.principal) && rawEligible p s consent i
  let who ← if !fresh.isEmpty && (← chance 75) then pick (fresh.map (·.1)) else pickApprover s
  pure (.approve id (← genRid s id false) who rd rc edit)

def genGrantCreate (p : Policy) (g : GS) (s : State) : Gen (GS × EventBody) := do
  let grantable := p.actions.filter (·.2.grantable.isSome)
  let (fresh, gid) ← if (← chance 88) || s.grants.isEmpty then pure (true, s!"g{g.nextGrant}")
    else do pure (false, ← pick s.grants.keys)
  let tool ← if !grantable.isEmpty && (← chance 88) then pick (grantable.map (·.1)) else pick (toolsOf p)
  let r := reqOf p tool
  let gr := r.grantable.getD { scope := .session, maxUses := 1 }
  let scope ← if ← chance 70 then pure (if gr.scope == .turn && !s.turnActive && (← chance 85) then .session else gr.scope)
    else pick [.turn, .session]
  let maxUses ← if ← chance 90 then (1 + ·) <$> below gr.maxUses else pure (gr.maxUses + 1)
  let digest ← if ← chance (if gr.anyArgs then 40 else 65) then some <$> pick digests else pure none
  let maxCost ← if ← chance 35 then do
      let cur := (moneyCurrency p r).getD (← pick currencies)
      pure (some ⟨← pick [2, 4, 6, 10], if ← chance 90 then cur else "XXX"⟩)
    else pure none
  let clock := g.w.clock
  let nb ← match ← weighted [(80, 0), (10, 1), (10, 2)] with
    | 1 => pure (some (clock - 1))
    | 2 => pure (some (clock + 3))
    | _ => pure none
  -- Mostly inside the action's max_duration_ms from creation, sometimes just past it.
  let exp ← if ← chance 82 then do
      let span ← match gr.maxDurationMs with
        | some d => do if ← chance 90 then pure (1 + (← below d)) else pure (d + 1 + (← below 3))
        | none => do pure (3 + (← below 30))
      pure (some (clock + span))
    else pure none
  -- With a not_before ahead, an even in-range expiry moves to max_duration_ms after not_before,
  -- which is past the creation time plus max_duration_ms unless dt reaches the lead; odd ones keep
  -- their drawn expiry, so valid grants with a future window still occur.
  let exp := match nb, gr.maxDurationMs, exp with
    | some n, some d, some x => if n > clock && x ≤ clock + d && x % 2 == 0 then some (n + d) else exp
    | _, _, _ => exp
  let g := if fresh then { g with nextGrant := g.nextGrant + 1 } else g
  let consents := r.consent :: (r.escalate.filter (·.2.grantable)).map (·.2.consent)
  let eligible := s.approvers.toList.filter fun (_, i) =>
    consents.all fun c => (Checks.clausesOf c).all (Checks.eligibleFor p s.requester i ·)
  let who ← if !eligible.isEmpty && (← chance 75) then pick (eligible.map (·.1)) else pickApprover s
  pure (g, .grantCreate gid who tool digest scope maxUses maxCost nb exp "rs")

def genAttest (s : State) : Gen EventBody := do
  match ← weighted [(50, 0), (20, 1), (30, 2)] with
  | 0 => do let (id, i) ← pick latePool; pure (.approverAttest id i)
  | 1 =>
    match s.approvers.toList with
    | [] => pure (.approverAttest "erin" ⟨"erin", .human, ["owner"]⟩)
    | l => do let (id, i) ← pick l; pure (.approverAttest id i)
  | _ =>
    let ids := s.approvers.keys
    let id ← if ids.isEmpty then pure "alice" else pick ids
    let (_, other) ← pick (startPool ++ latePool)
    pure (.approverAttest id other)

def retryableCalls (p : Policy) (s : State) : List (String × CallRec) :=
  (callsWhere s (· == .unknown)).filter fun (_, c) =>
    (reqOf p c.tool).retryAfterUnknown && c.reconciled.isNone && c.attempts < (reqOf p c.tool).maxAttempts

def genDispatch (p : Policy) (s : State) : Gen EventBody := do
  let retryable := retryableCalls p s
  let id ← match ← weighted [(75, 0), (17, 1), (8, 2)] with
    | 0 =>
      let viaGrant := retryable.filter (·.2.grant.isSome)
      if !viaGrant.isEmpty && (← chance 80) then pick (viaGrant.map (·.1))
      else if !retryable.isEmpty && (← chance 40) then pick (retryable.map (·.1))
      else pickCall s (callsWhere s (· == .authorized)) 95
    | 1 =>
      if retryable.isEmpty then pickCall s (callsWhere s (· == .unknown)) 95
      else pick (retryable.map (·.1))
    | _ => pickCall s [] 0
  let rec? := s.calls.get? id
  let tool := (rec?.map (·.tool)).getD "t0"
  let r := reqOf p tool
  let attempts := (rec?.map (·.attempts)).getD 0
  let attempt ← if ← chance 92 then pure (attempts + 1) else pick [attempts, attempts + 2]
  let digest ← if ← chance 95 then pure ((rec?.map (·.digest)).getD "d1") else pick digests
  let cost ← if ← chance 95 then pure (rec?.bind (·.cost)) else genCost p r
  let guards ← if ← chance 85 then pure ((rec?.map (·.proposedGuards)).getD []) else genGuards r
  let key := if ← chance 96 then s!"k:{id}" else "k:other"
  pure (.dispatch id attempt digest cost guards key)

def genActual (s : State) (id : String) (late : Bool) : Gen (Option Nat) := do
  let held := (((s.calls.get? id).bind (·.cost)).map (·.amount)).getD 0
  weighted [(40, none), (22, some held), (if late then 30 else 26, some (held + 1 + (← below 4))), (14, some (held - 1))]

def genOutcome : Gen Outcome := weighted [(50, .succeeded), (30, .failed), (20, .declined)]

def genResult (s : State) (unknown : Bool) : Gen EventBody := do
  let id ← pickCall s (callsWhere s (· == if unknown then .unknown else .dispatched)) 92
  let o ← genOutcome
  let actual ← genActual s id unknown
  let noEffect ← chance (if o == .declined then 40 else if unknown then 25 else 15)
  pure (if unknown then .reconcile id o actual noEffect else .result id o actual noEffect)

def genAck (p : Policy) (g : GS) (s : State) : Gen EventBody := do
  let elig := s.approvers.toList.filter fun (_, i) => Checks.escalationEligible p i
  let who ← if !elig.isEmpty && (← chance 75) then pick (elig.map (·.1)) else pickApprover s
  let older := g.seenEsc.filter (· != s.escalations)
  let echo ← match ← weighted [(75, 0), (if older.isEmpty then 0 else 18, 1), (7, 2)] with
    | 0 => pure s.escalations
    | 1 => pick older
    | _ => pure (s.escalations + 1)
  pure (.escalationAck who echo)

def genBody (p : Policy) (g : GS) (lane : Nat) : Gen (GS × EventBody × Option Nat × SyncMode × Bool) := do
  let l := g.lane lane
  let s := l.s
  let has (f : CallStatus → Bool) := !(callsWhere s f).isEmpty
  let awaiting := has (· == .awaiting)
  let dispatchable := s.calls.any fun _ c => c.status == .authorized
    || (c.status == .unknown && (reqOf p c.tool).retryAfterUnknown)
  let dispatched := has (· == .dispatched)
  let unknown := has (· == .unknown)
  let inFlightRetryable := s.calls.any fun _ c => c.status == .dispatched && (reqOf p c.tool).retryAfterUnknown
  let grantable := p.actions.any (·.2.grantable.isSome)
  let blocked := s.escalated || !s.blockedTools.isEmpty
  let multi := g.lanes > 1
  let grantInFlight := callsWhere s fun st => st == .dispatched
  let grantInFlight := grantInFlight.filter (·.2.grant.isSome)
  let grantHeld := (callsWhere s (· == .authorized)).filter (·.2.grant.isSome)
  let kind ← weighted
    [ (if s.turnActive then 8 else 150, 0), (if s.turnActive then 40 else 10, 1), (50, 2)
    , (220, 3), (if awaiting then 200 else 10, 4), (if awaiting then 40 else 2, 5)
    , (if awaiting then 10 else 1, 6), (if grantable then 60 else 10, 7), (10, 8), (20, 9)
    , (20, 10), (10, 11), (if dispatchable then 220 else 20, 12), (if dispatched then 130 else 3, 13)
    , (if dispatched then (if s.killed then 300 else 90) + (if grantInFlight.isEmpty then 0 else 150) else 2, 14), (if unknown then 40 else 2, 15), (if grantHeld.isEmpty then 30 else 90, 16)
    , (if blocked then 90 else 8, 17), (6, 18)
    , (if inFlightRetryable then 20 else if dispatched then 6 else 2, 19), (if multi then 5 else 3, 20)
    , (if multi then 25 else 4, 21), (if g.w.store.tombstone then 15 else 0, 22) ]
  match kind with
  | 0 => pure (g, .turnStart (← chance 50), none, .store, false)
  | 1 => pure (g, .turnEnd, none, .store, false)
  | 2 => pure (g, .stepStart, none, .store, false)
  | 3 => do let (g, b) ← genPropose p g s; pure (g, b, none, .store, false)
  | 4 => pure (g, ← genApprove p s, none, .store, false)
  | 5 => do
    let id ← pickCall s (callsWhere s fun st => st == .awaiting || st == .authorized) 90
    pure (g, .reject id (← genRid s id true) (← pickApprover s), none, .store, false)
  | 6 => do
    let id ← pickCall s (callsWhere s (· == .awaiting)) 90
    pure (g, .approvalExpire id (← genRid s id false), none, .store, false)
  | 7 => do let (g, b) ← genGrantCreate p g s; pure (g, b, none, .store, false)
  | 8 => do
    let gid ← if s.grants.isEmpty || (← chance 15) then pure "gx" else pick s.grants.keys
    pure (g, .grantRevoke gid, none, .store, false)
  | 9 => pure (g, ← genAttest s, none, .store, false)
  | 10 => pure (g, .permissionAdd (← pick permPool) (← pickApprover s), none, .store, false)
  | 11 => pure (g, .permissionRevoke (← pick permPool), none, .store, false)
  | 12 => do
    let b ← genDispatch p s
    let jump ← match b with
      | .dispatch id .. =>
        if ((s.calls.get? id).any (·.status == .unknown)) && (← chance 35) then pure (some (retryJump p)) else pure none
      | _ => pure none
    pure (g, b, jump, .store, false)
  | 13 => pure (g, ← genResult s false, none, .store, false)
  | 14 => do
    let id ← if !grantInFlight.isEmpty && (← chance 70) then pick (grantInFlight.map (·.1))
      else pickCall s (callsWhere s (· == .dispatched)) 92
    pure (g, .outcomeUnknown id, none, .store, false)
  | 15 => pure (g, ← genResult s true, none, .store, false)
  | 16 => do
    let id ← if !grantHeld.isEmpty && (← chance 60) then pick (grantHeld.map (·.1))
      else pickCall s (callsWhere s fun st => st == .awaiting || st == .authorized) 75
    pure (g, .cancel id, none, .store, false)
  | 17 => pure (g, ← genAck p g s, none, .store, false)
  | 18 => pure (g, .reset, none, .store, false)
  | 19 => pure (g, .kill, none, .store, false)
  | 20 => pure (g, .sessionEnd, none, .store, false)
  | 21 =>
    let modes := [(70, .store), (10, .older), (10, .clearTomb), (10, .foreignEntry), (10, .reorder), (10, .dropReservation)]
    pure (g, .ledgerSync {}, none, ← weighted modes, false)
  | _ => pure (g, .turnEnd, none, .store, true)

def genStep (stepF : StepFn) (p : Policy) (g : GS) : Gen GS := do
  -- Draws only in traces that seed such entries, so every other trace keeps its random stream.
  let g ← if g.plan.isEmpty && !g.otherScopeRan && otherScopeDue p g then do
      if ← chance 10 then startOtherScopePlan p g else pure g
    else pure g
  let g ← if g.plan.isEmpty then startTargetPlan p g else pure g
  let g ← if g.plan.isEmpty && g.tpl == 2 && (← chance 12) then startPlan p g (← below (max g.lanes 1))
    else if g.plan.isEmpty && g.lanes > 1 && (← chance 6) then startPrunePlan p g
    else if g.plan.isEmpty && g.w.skew > 0 && (← chance 12) then startSkewPlan p g
    else if g.plan.isEmpty && (← chance 10) then startSidePlan p g
    else pure g
  let (planned, rest) ← nextPlanned p g g.plan
  let g := { g with plan := rest }
  match planned with
  | some (ps, body) =>
    let lane := ps.lane
    let gs : GStep := { lane, dt := ← match ps.jump with | some j => pure j | none => below 2, body
                        oob := ps.step.isOob, sync := ps.step.syncMode }
    let (w, _) := feed stepF p g.w gs
    pure { g with w, steps := g.steps.push gs }
  | none =>
  let lane ← if g.lanes ≤ 1 then pure 0 else below g.lanes
  let l := g.lane lane
  let finished := l.dead || l.s.ended
  let (g, body, jump, sync, oob) ← if (!l.s.started || finished) && (← chance (if finished then 30 else 95)) then do
      let (g, b) ← genSessionStart g lane
      pure (g, b, none, SyncMode.store, false)
    else genBody p g lane
  let dt ← match jump with | some j => pure j | none => genDt
  let gs : GStep := { lane, intent := ← genIntent, dt, body, sync, oob }
  let (w, _) := feed stepF p g.w gs
  let esc := (w.lane lane).s.escalations
  pure { g with w, steps := g.steps.push gs, seenEsc := if g.seenEsc.contains esc then g.seenEsc else g.seenEsc ++ [esc] }

/-- `stepF` drives generation, so a scratch kernel variant can be fuzzed on the traces it would see. -/
def genTrace (seed len : Nat) (stepF : StepFn := step) : GTrace :=
  let gen : Gen GTrace := do
    let t ← weighted [(1, 0), (1, 1), (3, 2), (1, 3), (1, 4), (1, 5)]
    let p ← genPolicy t
    let led ← genInitLedger p
    let lanes ← if t == 5 then weighted [(60, 2), (40, 3)] else weighted [(65, 1), (22, 2), (13, 3)]
    let strict ← chance 60
    let skew ← if lanes > 1 && (← chance 35) then (1 + ·) <$> below 4 else pure 0
    let g0 : GTrace := { policy := p, initLedger := led, lanes, strict, skew, steps := [] }
    let rec loop : Nat → GS → Gen GS
      | 0, g => pure g
      | n + 1, g => do loop n (← genStep stepF p g)
    let g ← loop len { w := World.init g0, lanes, tpl := t }
    pure { g0 with steps := g.steps.toList }
  gen.run' (mix (UInt64.ofNat seed))

end WritTests.Fuzz
