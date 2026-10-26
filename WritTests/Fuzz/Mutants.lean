import WritTests.Fuzz.Shrink

open Writ

/-!
Mutants for the oracle's mutation run. The oracle's independence rule forbids reading the kernel,
so each mutant wraps the real `step` and alters its input or output to behave like a kernel with
one bug, using raw state fields only. Nothing here changes `Writ/Kernel`.
-/

namespace WritTests.Fuzz

def setReq (p : Policy) (tool : String) (f : Requirements → Requirements) : Policy :=
  { p with actions := p.actions.map fun (n, r) => if n == tool then (n, f r) else (n, r) }

def updCall (s : State) (k : String) (f : CallRec → CallRec) : State :=
  match s.calls.get? k with
  | some c => { s with calls := s.calls.insert k (f c) }
  | none => s

def callOf (s : State) (k : String) : Option CallRec := s.calls.get? k

def toolOf (s : State) (k : String) : String := ((callOf s k).map (·.tool)).getD ""

def acceptAs (s : State) (e : Event) (s' : State) (d : Decision) : State × Verdict :=
  ({ s' with lastSeq := e.seq, lastTime := e.time, version := s.version + 1 }, .ok d none)

/-- Run the real step; when `trigger` holds of its verdict, re-run on an altered input and, if
that is accepted, return `fix` of its post state. -/
def reroute (p : Policy) (s : State) (e : Event) (trigger : Verdict → Bool)
    (p2 : Policy) (s2 : State) (e2 : Event) (fix : State → State := id) : State × Verdict :=
  let (s', v) := step p s e
  if !trigger v then (s', v)
  else
    let (s'', v'') := step p2 s2 e2
    if accepted v'' then (fix s'', v'') else (s', v)

def isRej (r : Reason) (v : Verdict) : Bool := v == .rejected r

def mapEntries (f : MeterEntry → MeterEntry) (cid : String) (s : State) : State :=
  let g (e : MeterEntry) := if e.call == cid && e.session == s.sessionId then f e else e
  { s with sessionMeters := s.sessionMeters.map g, ledger := { s.ledger with entries := s.ledger.entries.map g } }

def preEntry (s : State) (e : MeterEntry) : Option MeterEntry :=
  (s.sessionMeters ++ s.ledger.entries).find? fun x => x.meter == e.meter && x.session == e.session && x.call == e.call

def greedyOk (p : Policy) (s : State) (c : CallRec) : Bool :=
  c.consent.groups.all fun g =>
    if !g.distinct || g.clauses.length ≤ 1 then true
    else
      let slots := g.clauses.flatMap fun cl => List.replicate cl.k cl
      let filled := c.tally.foldl (init := slots.map fun _ => false) fun filled (_, id) =>
        match s.approvers.get? id with
        | none => filled
        | some info =>
          match (List.range slots.length).find? fun i =>
              !(filled.getD i true) && (slots[i]?).any (Checks.eligibleFor p s.requester info ·) with
          | some i => filled.set i true
          | none => filled
      filled.all id

def mutants : List (String × StepFn) :=
  [ ("M01 dispatch-ignores-rejection-memory", fun p s e =>
      match e.body with
      | .dispatch .. => reroute p s e (fun _ => !s.rejectedMemory.isEmpty) p { s with rejectedMemory := [] } e
          ({ · with rejectedMemory := s.rejectedMemory })
      | _ => step p s e)
  , ("M02 attest-repoints-id", fun p s e =>
      match e.body with
      | .approverAttest id info =>
        let (s', v) := step p s e
        if !accepted v && s.approvers.contains id then acceptAs s e { s with approvers := s.approvers.insert id info } .none
        else (s', v)
      | _ => step p s e)
  , ("M03 approval-counted-twice", fun p s e =>
      match e.body with
      | .approve cid _ who .. =>
        let pr := ((s.approvers.get? who).map (·.principal)).getD who
        reroute p s e (isRej .alreadyApproved) p
          (updCall s cid fun c => { c with tally := c.tally.map fun (x, id) => if x == pr then (x ++ "#", id) else (x, id) }) e
      | _ => step p s e)
  , ("M04 cancel-keeps-grant-reservation", fun p s e =>
      let (s', v) := step p s e
      match e.body, (callOf s (match e.body with | .cancel c => c | _ => "")).bind (·.grant) with
      | .cancel _, some g =>
        if accepted v then
          match s.grants.get? g, s'.grants.get? g with
          | some old, some new => ({ s' with grants := s'.grants.insert g { new with reserved := old.reserved, costReserved := old.costReserved } }, v)
          | _, _ => (s', v)
        else (s', v)
      | _, _ => (s', v))
  , ("M05 retry-ignores-max-attempts", fun p s e =>
      match e.body with
      | .dispatch cid .. => reroute p s e (isRej .attemptLimit) (setReq p (toolOf s cid) fun r => { r with maxAttempts := r.maxAttempts + 1 }) s e
      | _ => step p s e)
  , ("M06 dispatch-after-kill", fun p s e =>
      match e.body with
      | .dispatch .. =>
        reroute p s e (fun v => v == .rejected .killed || v == .ok (.dispatchDenied .killed) none) p
          { s with killed := false, ledger := { s.ledger with tombstone := false } } e
          fun s'' => { s'' with killed := s.killed, ledger := { s''.ledger with tombstone := s.ledger.tombstone } }
      | _ => step p s e)
  , ("M07 approve-ignores-ttl", fun p s e =>
      match e.body with
      | .approve cid .. => reroute p s e (isRej .approvalExpired) p (updCall s cid ({ · with requestedAt := e.time })) e
      | _ => step p s e)
  , ("M08 edit-does-not-raise-consent", fun p s e =>
      match e.body with
      | .approve cid rid who rd rc (some ed) =>
        let names := ((Checks.reqOf p (toolOf s cid)).map fun r => r.escalate.map (·.1, false)).getD []
        step p s { e with body := .approve cid rid who rd rc (some { ed with escalators := names }) }
      | _ => step p s e)
  , ("M09 human-only-ignored", fun p s e =>
      match e.body with
      | .approve _ _ who .. =>
        match s.approvers.get? who with
        | some info => reroute p s e (isRej .approverNotEligible) p
            { s with approvers := s.approvers.insert who { info with kind := .human } } e
            ({ · with approvers := s.approvers })
        | none => step p s e
      | _ => step p s e)
  , ("M10 cap-ignores-new-amount", fun p s e =>
      match e.body with
      | .dispatch cid _ _ cost .. =>
        let amt := (cost.map (·.amount)).getD 0 + 1
        let r := (Checks.reqOf p (toolOf s cid)).getD {}
        let p2 := { p with meters := p.meters.map fun (n, m) =>
          if r.meters.contains n then (n, { m with cap := m.cap.map (· + amt) }) else (n, m) }
        reroute p s e (isRej .meterExceeded) p2 s e
      | _ => step p s e)
  , ("M11 dispatch-ignores-escalation", fun p s e =>
      match e.body with
      | .dispatch .. =>
        reroute p s e (fun v => v == .rejected .escalated || v == .ok (.dispatchDenied .escalated) none) p
          { s with escalated := false, blockedTools := [] } e
          ({ · with escalated := s.escalated, blockedTools := s.blockedTools })
      | _ => step p s e)
  , ("M12 grant-ignores-digest", fun p s e =>
      match e.body with
      | .propose _ tool d .. =>
        let (s', v) := step p s e
        match v with
        | .ok (.allowedByGrant _) _ => (s', v)
        | _ =>
          match s.grants.toList.find? (fun (_, g) => g.tool == tool && g.digest.isSome && g.digest != some d) with
          | some (gid, g) =>
            let (s'', v'') := step p { s with grants := s.grants.insert gid { g with digest := none } } e
            match v'' with
            | .ok (.allowedByGrant _) _ =>
              let g'' := (s''.grants.get? gid).getD g
              ({ s'' with grants := s''.grants.insert gid { g'' with digest := g.digest } }, v'')
            | _ => (s', v)
          | none => (s', v)
      | _ => step p s e)
  , ("M13 reset-keeps-epoch", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .reset => if accepted v then ({ s' with epoch := s.epoch }, v) else (s', v)
      | _ => (s', v))
  , ("M14 rejected-step-bumps-seq", fun p s e =>
      let (s', v) := step p s e
      if accepted v then (s', v) else ({ s with lastSeq := max s.lastSeq e.seq }, v))
  , ("M15 any-turn-clears-memory", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .turnStart false => if accepted v then ({ s' with rejectedMemory := [] }, v) else (s', v)
      | _ => (s', v))
  , ("M16 denied-proposals-not-counted", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .propose cid .., .ok (.denied _) _ =>
        if s.calls.contains cid then (s', v)
        else ({ s' with proposalsThisTurn := s.proposalsThisTurn, proposalsThisSession := s.proposalsThisSession }, v)
      | _, _ => (s', v))
  , ("M17 start-drops-tombstone", fun p s e =>
      match e.body with
      | .sessionStart sid pd req perms apprs l =>
        step p s { e with body := .sessionStart sid pd req perms apprs { l with tombstone := false } }
      | _ => step p s e)
  , ("M18 cost-threshold-ignores-currency", fun p s e =>
      match e.body with
      | .propose _ tool _ (some c) .. =>
        step (setReq p tool fun r => { r with consentIfCostOver := r.consentIfCostOver.map ({ · with currency := c.currency }) }) s e
      | _ => step p s e)
  , ("M19 reconcile-overrun-not-a-failure", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .reconcile .. =>
        if accepted v then
          ({ s' with failures := s.failures, failuresThisSession := s.failuresThisSession, escalated := s.escalated
                     blockedTools := s.blockedTools, escalations := s.escalations }, v)
        else (s', v)
      | _ => (s', v))
  , ("M20 overrun-commits-reservation", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .result cid .. => if accepted v then (mapEntries ({ · with excess := 0 }) cid s', v) else (s', v)
      | _ => (s', v))
  , ("M21 dispatch-ignores-digest", fun p s e =>
      match e.body, callOf s (match e.body with | .dispatch c .. => c | _ => "") with
      | .dispatch cid n _ _ g k, some c =>
        reroute p s e (fun v => v == .rejected .digestMismatch || v == .rejected .costMismatch) p s
          { e with body := .dispatch cid n c.digest c.cost g k }
      | _, _ => step p s e)
  , ("M22 permission-add-from-anyone", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .permissionAdd perm _ =>
        if !accepted v && s.started && !s.ended then acceptAs s e { s with permissions := s.permissions ++ [perm] } .none
        else (s', v)
      | _ => (s', v))
  , ("M23 unexposed-allowed", fun p s e =>
      step { p with actions := p.actions.map fun (n, r) => (n, { r with exposed := true }) } s e)
  , ("M24 cancel-terminal-calls", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .cancel cid =>
        if !accepted v && (callOf s cid).any (fun c => c.status != .awaiting && c.status != .authorized && c.status != .dispatched) then
          acceptAs s e (updCall s cid ({ · with status := .cancelled })) .none
        else (s', v)
      | _ => (s', v))
  , ("M25 grant-for-non-grantable-action", fun p s e =>
      match e.body with
      | .grantCreate _ _ tool .. =>
        reroute p s e (isRej .grantNotAllowed)
          (setReq p tool fun r => { r with grantable := some { scope := .session, maxUses := 3, maxDurationMs := some 1000, anyArgs := true } }) s e
      | _ => step p s e)
  , ("M26 approval-budget-ignored", fun p s e =>
      step { p with limits := { p.limits with maxApprovalRequestsPerTurn := none, maxApprovalRequestsPerSession := none } } s e)
  , ("M27 time-may-go-back", fun p s e =>
      reroute p s e (isRej .timeDecreasing) p { s with lastTime := e.time } e)
  , ("M28 duplicate-call-new-content", fun p s e =>
      match e.body with
      | .propose cid .. => reroute p s e (isRej .duplicateCall) p { s with calls := s.calls.erase cid } e
      | _ => step p s e)
  , ("M29 approval-not-in-tally", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .approve cid _ _ _ _ none, .ok .pending _ =>
        (updCall s' cid ({ · with tally := ((callOf s cid).map (·.tally)).getD [] }), v)
      | _, _ => (s', v))
  , ("M30 kill-keeps-pending", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .kill => if accepted v then ({ s' with calls := s.calls }, v) else (s', v)
      | _ => (s', v))
  , ("M31 reject-from-ineligible-approver", fun p s e =>
      match e.body with
      | .reject _ _ who =>
        match s.approvers.get? who with
        | some info =>
          reroute p s e (isRej .approverNotEligible) p
            { s with approvers := s.approvers.insert who { info with kind := .human, roles := p.approverRoles } } e
            ({ · with approvers := s.approvers })
        | none => step p s e
      | _ => step p s e)
  , ("M32 sync-accepts-missing-reservation", fun p s e =>
      match e.body with
      | .ledgerSync l =>
        let lost := s.ledger.entries.filter fun x => x.session == s.sessionId && !x.committed && !l.entries.contains x
        if lost.isEmpty then step p s e
        else
          reroute p s e (isRej .ledgerConflict) p s { e with body := .ledgerSync { l with entries := l.entries ++ lost } }
            ({ · with ledger := l })
      | _ => step p s e)
  , ("M33 escalation-count-doubles", fun p s e =>
      let (s', v) := step p s e
      if accepted v && s'.escalations > s.escalations then ({ s' with escalations := s'.escalations + 1 }, v) else (s', v))
  , ("M34 grant-duration-from-not-before", fun p s e =>
      match e.body with
      | .grantCreate gid who tool d sc n mc (some nb) (some x) rs =>
        if nb > e.time && x ≥ nb - e.time then
          reroute p s e (isRej .grantNotAllowed) p s
            { e with body := .grantCreate gid who tool d sc n mc (some nb) (some (x - (nb - e.time))) rs }
            fun s'' => match s''.grants.get? gid with
              | some g => { s'' with grants := s''.grants.insert gid { g with expiresAt := some x } }
              | none => s''
        else step p s e
      | _ => step p s e)
  , ("M35 repeat-reports-past-before-kill", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .propose cid .., .ok (.denied .killed) sh =>
        match callOf s cid with
        | some c => if c.status != .awaiting && c.status != .authorized then (s', .ok (.existing c.status) sh) else (s', v)
        | none => (s', v)
      | _, _ => (s', v))
  , ("M36 repeat-of-unknown-shadows-escalation", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .propose cid tool .., .ok (.denied .escalated) none =>
        let unexposed := (Checks.reqOf p tool).all (!·.exposed)
        match callOf s cid with
        | some c =>
          match c.status with
          | .denied why =>
            if p.mode == .logOnly && unexposed then (s', .ok (.denied why) (some (.wouldDeny .escalated))) else (s', v)
          | _ => (s', v)
        | none => (s', v)
      | _, _ => (s', v))
  , ("M37 events-accepted-after-kill", fun p s e =>
      match e.body with
      | .dispatch .. => step p s e
      | _ =>
        reroute p s e (isRej .killed) p { s with killed := false, ledger := { s.ledger with tombstone := false } } e
          fun s'' => { s'' with killed := s.killed, ledger := { s''.ledger with tombstone := s.ledger.tombstone } })
  , ("M38 every-stage-reason-is-call-ended", fun p s e =>
      let (s', v) := step p s e
      match v with
      | .rejected r => if Checks.stageCodes.contains r.code then (s', .rejected .callEnded) else (s', v)
      | _ => (s', v))
  , ("M39 overrun-not-reported", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .result .., .ok _ sh | .reconcile .., .ok _ sh => (s', .ok .none sh)
      | _, _ => (s', v))
  , ("M40 no-pruning", fun p s e =>
      let (s', v) := step p s e
      let keep (before after : List MeterEntry) :=
        after ++ before.filter fun x =>
          x.committed && !after.any fun y => y.meter == x.meter && y.session == x.session && y.call == x.call
      match e.body with
      | .ledgerSync _ | .sessionStart .. => (s', v)
      | _ =>
        if !accepted v then (s', v)
        else ({ s' with sessionMeters := keep s.sessionMeters s'.sessionMeters
                        ledger := { s'.ledger with entries := keep s.ledger.entries s'.ledger.entries } }, v))
  , ("F1 overrun-dated-at-reservation", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .result cid .. | .reconcile cid .. =>
        if accepted v then (mapEntries (fun x => if x.excess > 0 then { x with excessAt := x.time } else x) cid s', v)
        else (s', v)
      | _ => (s', v))
  , ("F2 failed-commits-max-reserved-actual", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .result cid .failed _ false | .reconcile cid .failed _ false =>
        if accepted v then
          (mapEntries (fun x => match preEntry s x with
            | some old => if x.amount < old.amount && x.excess == 0 then { x with amount := old.amount } else x
            | none => x) cid s', v)
        else (s', v)
      | _ => (s', v))
  , ("F3 greedy-distinct-matching", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .approve cid .., .ok .authorized sh =>
        match callOf s' cid with
        | some c =>
          if greedyOk p s' c then (s', v)
          else (updCall s' cid ({ · with status := .awaiting, authorizedAt := none }), .ok .pending sh)
        | none => (s', v)
      | _, _ => (s', v))
  , ("F4 ack-without-count-check", fun p s e =>
      match e.body with
      | .escalationAck who _ => reroute p s e (isRej .staleRequest) p s { e with body := .escalationAck who s.escalations }
      | _ => step p s e)
  , ("F5 retry-ignores-window", fun p s e =>
      match e.body with
      | .dispatch cid attempt .. =>
        if attempt > 1 && (callOf s cid).any (·.status == .unknown) then
          let (s', v) := step p (mapEntries ({ · with time := e.time }) cid s) e
          if accepted v then
            (mapEntries (fun x => match preEntry s x with | some old => { x with time := old.time } | none => x) cid s', v)
          else step p s e
        else step p s e
      | _ => step p s e)
  , ("M41 declined-commits", fun p s e =>
      let (s', v) := step p s e
      let asFailed : Option EventBody := match e.body with
        | .result cid .declined a false => some (.result cid .failed a false)
        | .reconcile cid .declined a false => some (.reconcile cid .failed a false)
        | _ => none
      match asFailed with
      | some b =>
        let (s2, v2) := step p s { e with body := b }
        if accepted v && accepted v2 then
          ({ s' with sessionMeters := s2.sessionMeters, ledger := { s'.ledger with entries := s2.ledger.entries } }, v)
        else (s', v)
      | none => (s', v))
  , ("M42 unknown-tool-recorded", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .propose cid tool d cost _ _, .ok (.denied .unknownTool) sh =>
        if s.calls.contains cid || (Checks.reqOf p tool).isSome then (s', v)
        else
          let c : CallRec :=
            { tool, epoch := s.epoch, proposedDigest := d, proposedCost := cost, proposedGuards := []
              proposedEscalators := [], decision := .denied .unknownTool, shadow := sh, consent := {}, digest := d
              cost, status := .denied .unknownTool, generations := [(d, cost)], requestedAt := e.time }
          ({ s' with calls := s'.calls.insert cid c }, v)
      | _, _ => (s', v))
  , ("M43 sync-refuses-foreign-prune", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .ledgerSync l =>
        if accepted v && s.ledger.entries.any (fun x => x.session == s.sessionId && !l.entries.contains x) then
          (s, .rejected .ledgerConflict)
        else (s', v)
      | _ => (s', v))
  , ("M44 dispatch-checks-attempt-before-status", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .dispatch .., .rejected .callDispatched => (s', .rejected .attemptOrder)
      | _, _ => (s', v))
  , ("M45 kill-ends-call-at-dispatch", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .dispatch cid .., .rejected .killed =>
        if (callOf s cid).any (·.status != .dispatched) then
          acceptAs s e (updCall s cid ({ · with status := .deniedAtDispatch .killed })) (.dispatchDenied .killed)
        else (s', v)
      | _, _ => (s', v))
  , ("M46 ended-sync-refuses-cleared-tombstone", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .ledgerSync l =>
        if accepted v && s.ended && s.ledger.tombstone && !l.tombstone then (s, .rejected .ledgerConflict) else (s', v)
      | _ => (s', v))
  , ("M47 prune-ledger-by-any-scope", fun p s e =>
      let (s', v) := step p s e
      let stale (x : MeterEntry) : Bool := (Checks.meterOf p x.meter).any fun m =>
        m.scope == .session && m.windowMs.any (Checks.outsideWindow · e.time x)
      match e.body with
      | .ledgerSync _ | .sessionStart .. => (s', v)
      | _ =>
        if accepted v && s'.ledger.entries != s.ledger.entries then
          ({ s' with ledger := { s'.ledger with entries := s'.ledger.entries.filter (!stale ·) } }, v)
        else (s', v))
  , ("M48 propose-permission-before-limits", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .propose cid tool .., .ok (.denied why) sh =>
        let missing := ((Checks.reqOf p tool).bind (·.permission)).any (!s.permissions.contains ·)
        if (why == .proposalLimit || why == .sessionProposalLimit) && missing && !s.calls.contains cid then
          let d := Decision.denied .permissionMissing
          (updCall s' cid ({ · with decision := d, status := .denied .permissionMissing }), .ok d sh)
        else (s', v)
      | _, _ => (s', v))
  , ("M49 propose-escalated-before-unknown-tool", fun p s e =>
      let (s', v) := step p s e
      match e.body, v with
      | .propose .., .ok (.denied .unknownTool) sh => if s.escalated then (s', .ok (.denied .escalated) sh) else (s', v)
      | _, _ => (s', v))
  , ("M50 cleared-sync-revives-dispatched", fun p s e =>
      let (s', v) := step p s e
      match e.body with
      | .ledgerSync l =>
        if accepted v && s.ended && s.ledger.tombstone && !l.tombstone then
          match s'.calls.toList.find? (·.2.status == .unknown) with
          | some (k, _) => (updCall s' k ({ · with status := .dispatched }), v)
          | none => (s', v)
        else (s', v)
      | _ => (s', v))
  , ("M56 sync-accepts-duplicate-own-entry", fun p s e =>
      match e.body with
      | .ledgerSync l =>
        let once := l.entries.foldl (init := []) fun acc x =>
          if x.session == s.sessionId && acc.contains x then acc else acc ++ [x]
        if once.length == l.entries.length then step p s e
        else
          reroute p s e (isRej .ledgerConflict) p s { e with body := .ledgerSync { l with entries := once } }
            ({ · with ledger := l })
      | _ => step p s e) ]

end WritTests.Fuzz
