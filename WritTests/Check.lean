import Writ

open Writ

#guard Consent.join .none Consent.perCall == Consent.perCall
#guard Consent.join (.quorum 1 (some ["owner","admin"]) false false) (.quorum 2 (some ["admin"]) true false)
        == ⟨(Consent.quorum 1 (some ["owner","admin"]) false false).groups
              ++ (Consent.quorum 2 (some ["admin"]) true false).groups⟩
def thresholdReq : Requirements := { consent := .perCall, consentIfCostOver := some ⟨1000, "USD"⟩ }
#guard (thresholdReq.effectiveConsent (some ⟨999, "USD"⟩) []) == .none
#guard (thresholdReq.effectiveConsent none []) == .perCall
#guard (thresholdReq.effectiveConsent (some ⟨999, "XAU"⟩) []) == .perCall
#guard (thresholdReq.effectiveConsent (some ⟨1000, "USD"⟩) []) == .perCall
#guard (Requirements.effectiveConsent { escalate := [("over_limit", { consent := .perCall })] } none [])
        == .perCall
#guard (Requirements.effectiveConsent { escalate := [("over_limit", { consent := .perCall })] } none
        [("over_limit", false)]) == .none
#guard ({ approverRoles := ["owner"], actions := [("a", { consent := .perCall }), ("a", {})] } : Policy).check
        == [.duplicateAction "a"]
#guard ({ approverRoles := ["owner"], actions := [("buy",
          { consent := .quorum 2 none true false, grantable := some ⟨.session, 5, none, false, false⟩ })] } : Policy).check
        == [.grantableNeedsSingleApproval "buy"]
#guard ({ actions := [("x", { consent := .perCall })] } : Policy).check == [.noApproverRoles "x"]
#guard ({ approverRoles := ["owner"], meters := [("usd", ⟨.money "USD", some 100, .session, none, none⟩)],
          actions := [("buy", { consent := .perCall, meters := ["usd"], grantable := some ⟨.session, 3, some 1000, true, false⟩ })] } : Policy).check
        == [.anyArgsMetered "buy"]
#guard Reason.all.length == 52
#guard Reason.retry .ledgerConflict == .never
#guard Reason.retry .killed == .never && Reason.retry .stepLimit == .nextTurn

#guard ({} : Policy).check == []
#guard ({ meters := [("m", ⟨.money "USD", some 1, .session, none, none⟩), ("m", ⟨.money "USD", some 1, .session, none, none⟩)] }
        : Policy).check == [.duplicateMeter "m"]
#guard ({ actions := [("a", { meters := ["m"] })] } : Policy).check == [.unknownMeter "a" "m"]
#guard ({ approverRoles := ["owner"], actions := [("a", { consent := .quorum 0 none true false })] }
        : Policy).check == [.zeroQuorum "a"]
#guard ({ approverRoles := ["owner"], actions := [("a", { consent := .quorum 1 (some ["x"]) true false })] }
        : Policy).check == [.unknownRole "a" "x"]
#guard ({ approverRoles := ["owner", "admin"], actions := [("a",
          { consent := .quorum 1 (some ["owner"]) true false,
            escalate := [("e", { consent := .quorum 1 (some ["admin"]) true false })] })] } : Policy).check
        == []
#guard ({ approverRoles := ["owner"], actions := [("a",
          { consent := .perCall, grantable := some ⟨.session, 3, none, true, false⟩ })] } : Policy).check
        == [.anyArgsNeedsDuration "a"]
#guard ({ approverRoles := ["owner"], actions := [("a",
          { consent := .perCall, grantable := some ⟨.session, 0, none, false, false⟩ })] } : Policy).check
        == [.zeroMaxUses "a"]
#guard ({ actions := [("a", { retryAfterUnknown := true })] } : Policy).check
        == [.retryNeedsIdempotent "a"]
#guard ({ actions := [("a", { maxAttempts := 0 })] } : Policy).check == [.zeroMaxAttempts "a"]
#guard ({ limits := { maxConsecutiveFailures := some 0 } } : Policy).check == [.zeroFailureLimit]
#guard ({ limits := { maxFailuresPerSession := some 0 } } : Policy).check == [.zeroSessionFailureLimit]
#guard ({ limits := { maxFailuresPerSession := some 1 } } : Policy).check == []
#guard ({ approverRoles := ["owner"], escalationRoles := some ["x"] } : Policy).check
        == [.unknownEscalationRole "x"]

#guard (Consent.join (.quorum 1 (some ["owner"]) false false) (.quorum 1 (some ["admin"]) false false)).clauses
        == [⟨1, some ["owner"], false, false⟩, ⟨1, some ["admin"], false, false⟩]
#guard (Consent.join (.quorum 1 none false false) (.quorum 1 (some ["admin"]) false false)).clauses
        == [⟨1, none, false, false⟩, ⟨1, some ["admin"], false, false⟩]
#guard (Consent.join (.quorum 1 (some ["admin"]) false false) (.quorum 1 none false false)).clauses
        == [⟨1, some ["admin"], false, false⟩, ⟨1, none, false, false⟩]
#guard
  let a := Consent.quorum 1 (some ["x", "y"]) false false
  let b := Consent.quorum 1 (some ["y", "z"]) false false
  let c := Consent.quorum 1 (some ["z", "x"]) false false
  (a.join b).join c == a.join (b.join c) && ((a.join b).join c).groups.length == 3
    && (a.join b).groups.all (· ∈ (b.join a).groups) && (b.join a).groups.all (· ∈ (a.join b).groups)
#guard ({ approverRoles := ["owner", "admin"], actions := [("a",
          { consent := .quorum 1 (some ["owner"]) true false,
            escalate := [("e", { consent := .quorum 1 (some ["admin"]) true false })] })] }
        : Policy).check == []
#guard ({ approverRoles := ["owner"], actions := [("a", { consent := .quorum 1 (some []) true false })] }
        : Policy).check == [.emptyRoles "a"]
#guard GrantScope.le .turn .turn && GrantScope.le .turn .session && GrantScope.le .session .session
        && !GrantScope.le .session .turn
#guard Reason.all.eraseDups.length == Reason.all.length
#guard ({ approverRoles := ["owner"], escalationRoles := some ["x"], limits := { maxConsecutiveFailures := some 0 },
          meters := [("m", ⟨.money "USD", some 1, .session, none, none⟩), ("m", ⟨.money "USD", some 1, .session, none, none⟩)],
          actions := [("a", { consent := .perCall, meters := ["nope"], maxAttempts := 0 }),
                      ("a", { retryAfterUnknown := true })] } : Policy).check
        == [.unknownMeter "a" "nope", .zeroMaxAttempts "a",
            .duplicateAction "a", .retryNeedsIdempotent "a",
            .duplicateMeter "m", .zeroFailureLimit, .unknownEscalationRole "x"]

def shellReq : Requirements :=
  { consent := .none, grantable := some { scope := .session, maxUses := 5 }
    escalate := [("not_allowlisted", { consent := .perCall, grantable := true }),
                 ("dangerous", { consent := .perCall })] }
def gr : Option Grantable := some { scope := .session, maxUses := 3 }
def finClause : Clause := ⟨1, some ["owner"], true, false⟩
def adminClause : Clause := ⟨1, some ["admin"], true, false⟩
def checkOne (r : Requirements) : List Problem :=
  ({ approverRoles := ["owner", "admin"], actions := [("a", r)] } : Policy).check

#guard ({ approverRoles := ["owner"], actions := [("shell", shellReq)] } : Policy).check == []
#guard Consent.join .perCall .perCall == .perCall
#guard (Consent.join (.allOf [finClause]) (.allOf [adminClause])).groups.length == 2
#guard Consent.join .none .none == .none
#guard (Consent.allOf [finClause, adminClause] true).clauses == [finClause, adminClause]
#guard Consent.perCall.single && Consent.none.single && (Consent.allOf [finClause, adminClause]).single
#guard !(Consent.allOf [finClause, adminClause] true).single && !(Consent.quorum 2 none true false).single
#guard (Consent.allOf [finClause] true).single

#guard shellReq.effectiveConsent none [("not_allowlisted", true), ("dangerous", false)] == .perCall
#guard shellReq.effectiveConsent none [("not_allowlisted", false), ("dangerous", false)] == .none
#guard shellReq.effectiveConsent none [] == .perCall
#guard shellReq.firedGrantable [("not_allowlisted", true), ("dangerous", false)]
#guard !shellReq.firedGrantable [("not_allowlisted", true), ("dangerous", true)]
#guard !shellReq.firedGrantable [("not_allowlisted", true)]
#guard shellReq.firedGrantable [("not_allowlisted", false), ("dangerous", false)]

#guard checkOne { consent := .allOf [⟨0, none, true, false⟩, ⟨1, some ["x"], true, false⟩, ⟨0, some [], true, false⟩] }
        == [.zeroQuorum "a", .unknownRole "a" "x", .zeroQuorum "a", .emptyRoles "a"]
#guard checkOne { escalate := [("e", { consent := .quorum 1 (some ["y"]) true false })] }
        == [.unknownRole "a" "y"]
#guard ({ actions := [("a", { escalate := [("e", { consent := .perCall })] })] } : Policy).check
        == [.noApproverRoles "a"]
#guard checkOne { consent := .allOf [finClause, adminClause] true, grantable := gr }
        == [.grantableNeedsSingleApproval "a"]
#guard checkOne { consent := .allOf [finClause, adminClause], grantable := gr } == []
#guard checkOne { consent := .perCall, grantable := gr
                  escalate := [("e", { consent := .quorum 2 none true false, grantable := true })] }
        == [.grantableNeedsSingleApproval "a"]
#guard checkOne { consent := .perCall, grantable := gr
                  escalate := [("e", { consent := .quorum 2 none true false })] } == []
#guard checkOne { grantable := gr } == [.grantableWithoutConsent "a"]
#guard checkOne { grantable := gr, escalate := [("e", { consent := .perCall })] }
        == [.grantableWithoutConsent "a"]
#guard checkOne { grantable := gr, escalate := [("e", { consent := .perCall, grantable := true })] } == []
#guard checkOne { consent := .perCall, escalate := [("e", { consent := .perCall, grantable := true })] }
        == [.grantableEscalatorWithoutGrantable "a" "e"]
#guard checkOne { exposed := false, mode := some .logOnly } == [.unexposedLogOnly "a"]
#guard checkOne { exposed := false } == [] && checkOne { mode := some .logOnly } == []

#guard ({ meters := [("w", { unit := .money "USD", windowMs := some 0 }),
                     ("ok", { unit := .money "USD", windowMs := some 1 })] } : Policy).check
        == [.zeroWindow "w"]
#guard ({ meters := [("c", { unit := .calls, cap := some 5, maxPerCall := some 1 }),
                     ("usd", { unit := .money "USD", maxPerCall := some 1 })] } : Policy).check
        == [.perCallOnCallsMeter "c"]
#guard ({ meters := [("usd", { unit := .money "USD" }), ("eur", { unit := .money "EUR" }),
                     ("usd2", { unit := .money "USD" }), ("n", { unit := .calls })],
          actions := [("a", { meters := ["usd", "eur", "usd2"] }), ("b", { meters := ["usd", "usd2", "n"] })] }
        : Policy).check == [.mixedCurrencies "a"]
#guard ({ actions := [("a", { meters := ["x", "y"] })] } : Policy).check
        == [.unknownMeter "a" "x", .unknownMeter "a" "y"]
#guard ({ meters := [("usd", { unit := .money "USD" }), ("n", { unit := .calls })],
          actions := [("a", { meters := ["usd", "n", "usd"] })] } : Policy).check
        == [.duplicateMeterInAction "a" "usd"]
#guard ({ approverRoles := ["f"], actions := [("a", { escalate := [("x", { consent := .perCall }), ("x", { consent := .perCall })] })] } : Policy).check
        == [.duplicateEscalator "a" "x"]
#guard ({ approverRoles := ["f"], actions := [("a", { escalate := [("x", { consent := .perCall }), ("y", { consent := .perCall })] })] } : Policy).check
        == []

def problemSamples : List Problem :=
  [.duplicateAction "a", .duplicateMeter "m", .unknownMeter "a" "m", .zeroQuorum "a",
   .unknownRole "a" "r", .noApproverRoles "a", .emptyRoles "a", .grantableNeedsSingleApproval "a",
   .grantableWithoutConsent "a", .grantableEscalatorWithoutGrantable "a" "e",
   .anyArgsNeedsDuration "a", .anyArgsMetered "a", .zeroMaxUses "a", .retryNeedsIdempotent "a",
   .zeroMaxAttempts "a", .zeroFailureLimit, .zeroSessionFailureLimit, .unknownEscalationRole "r",
   .unexposedLogOnly "a", .zeroWindow "m", .mixedCurrencies "a", .perCallOnCallsMeter "m",
   .duplicateMeterInAction "a" "m", .duplicateEscalator "a" "e", .emptyConsentGroup "a"]

def warningSamples : List Warning :=
  [.lethalTrifecta "r" "i" "s", .noApprovalTtl, .zeroTtl "a", .costThresholdUnmetered "a",
   .retriesExceedFailureLimit "a", .costThresholdWithoutConsent "a", .messagesNotApplied "a",
   .meterWithoutCap "m", .principalMeterWithoutWindow "m", .perCallAboveCap "m",
   .retryWithoutAttempts "a"]

def snakeCase (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isLower || c == '_'

def noDashes (s : String) : Bool := !s.any fun c => c == '\u2014' || c == '\u2013'

#guard problemSamples.length == 25
#guard (problemSamples.map Problem.code).eraseDups.length == problemSamples.length
#guard problemSamples.all fun x => snakeCase x.code && noDashes x.message && !x.message.isEmpty
#guard warningSamples.length == 11
#guard problemSamples.all fun x => match x.action? with
  | some a => (x.message.splitOn ("\"" ++ a ++ "\"")).length == 1
  | none => true
#guard warningSamples.all fun x => match x.action? with
  | some a => (x.message.splitOn ("\"" ++ a ++ "\"")).length == 1
  | none => true
#guard (warningSamples.map Warning.code).eraseDups.length == warningSamples.length
#guard warningSamples.all fun x => snakeCase x.code && noDashes x.message && !x.message.isEmpty
#guard (Problem.duplicateEscalator "a" "x").code == "duplicate_escalator"
#guard (Problem.duplicateEscalator "a" "x").action? == some "a"
#guard (Problem.duplicateEscalator "a" "x").message == "escalator \"x\" is defined twice"
#guard (Problem.duplicateAction "a").message == "the action is defined twice"
#guard problemSamples.map Problem.ctorIdx == List.range problemSamples.length
#guard warningSamples.map Warning.ctorIdx == List.range warningSamples.length
theorem problem_ctors (x : Problem) : x.ctorIdx < 25 := by cases x <;> simp [Problem.ctorIdx]
theorem warning_ctors (x : Warning) : x.ctorIdx < 11 := by cases x <;> simp [Warning.ctorIdx]
#guard (Problem.zeroWindow "m").action? == none && (Problem.zeroFailureLimit).action? == none
#guard (Warning.zeroTtl "a").action? == some "a" && Warning.noApprovalTtl.action? == none
#guard [Warning.meterWithoutCap "m", .principalMeterWithoutWindow "m", .perCallAboveCap "m"].all
        (·.action? == none)
#guard (Warning.retryWithoutAttempts "a").action? == some "a"
#guard (Warning.meterWithoutCap "m").message == "meter \"m\" has no cap, so it records usage but never denies a call"
#guard (Warning.principalMeterWithoutWindow "m").message
        == "principal meter \"m\" has no window_ms, so its cap is a lifetime limit for each principal"
#guard (Warning.perCallAboveCap "m").message
        == "meter \"m\" has max_per_call above its cap, so the cap denies calls the per-call limit allows"
#guard (Warning.retryWithoutAttempts "a").message
        == "retry_after_unknown is set but max_attempts is 1, so an unknown call can never be retried"

def trifectaPolicy (send : Requirements) : Policy :=
  { approverRoles := ["o"], limits := { approvalTtlMs := some 1 }
    actions := [("r", { flags := [.readsPrivate] }), ("i", { flags := [.ingestsUntrusted] }),
                ("s", send)] }

#guard (trifectaPolicy { flags := [.sendsExternal] }).warnings == [.lethalTrifecta "r" "i" "s"]
#guard (trifectaPolicy { flags := [.sendsExternal], consent := .perCall }).warnings == []
#guard (trifectaPolicy { flags := [.sendsExternal], consent := .perCall
                         grantable := some { scope := .session, maxUses := 1, anyArgs := true } }).warnings
        == [.lethalTrifecta "r" "i" "s"]
#guard (trifectaPolicy { flags := [.sendsExternal], consent := .perCall
                         grantable := some { scope := .session, maxUses := 1 } }).warnings == []
#guard ({ actions := [("r", { flags := [.readsPrivate] }), ("s", { flags := [.sendsExternal] })] }
        : Policy).warnings == []
#guard ({ actions := [("r", { flags := [.readsPrivate, .ingestsUntrusted, .sendsExternal] })] }
        : Policy).warnings == [.lethalTrifecta "r" "r" "r"]

#guard ({ actions := [("a", { consent := .perCall })] } : Policy).warnings == [.noApprovalTtl]
#guard ({ actions := [("a", { consent := .perCall, approvalTtlMs := some 5 })] } : Policy).warnings == []
#guard ({ limits := { approvalTtlMs := some 5 }, actions := [("a", { consent := .perCall })] }
        : Policy).warnings == []
#guard ({ actions := [("a", { escalate := [("e", { consent := .perCall })] })] } : Policy).warnings
        == [.noApprovalTtl]
#guard ({ actions := [("a", {}), ("b", { consent := .perCall, approvalTtlMs := some 5 })] }
        : Policy).warnings == []

#guard ({ actions := [("a", { approvalTtlMs := some 0 }), ("b", { authorizedTtlMs := some 0 }),
                      ("c", { approvalTtlMs := some 1, authorizedTtlMs := some 1 })] } : Policy).warnings
        == [.zeroTtl "a", .zeroTtl "b"]

def thresholdWarn (ms : List String) : List Warning :=
  ({ meters := [("usd", { unit := .money "USD", cap := some 1 }), ("n", { unit := .calls, cap := some 1 })],
     actions := [("a", { consentIfCostOver := some ⟨5, "USD"⟩, meters := ms,
                           consent := .perCall, approvalTtlMs := some 1 })] } : Policy).warnings
#guard thresholdWarn [] == [.costThresholdUnmetered "a"]
#guard thresholdWarn ["n"] == [.costThresholdUnmetered "a"]
#guard thresholdWarn ["usd"] == []
#guard thresholdWarn ["usd", "n"] == []

def retryWarn (attempts failures : Nat) (scope : EscalationScope) : List Warning :=
  ({ limits := { maxConsecutiveFailures := some failures, escalationScope := scope },
     actions := [("a", { idempotent := true, retryAfterUnknown := true, maxAttempts := attempts })] }
   : Policy).warnings
#guard retryWarn 4 3 .session == [.retriesExceedFailureLimit "a"]
#guard retryWarn 3 3 .session == []
#guard retryWarn 4 3 .tool == []
#guard ({ limits := { maxConsecutiveFailures := some 1 },
          actions := [("a", { maxAttempts := 4 })] } : Policy).warnings == []

#guard ({ actions := [("a", { consentIfCostOver := some ⟨5, "USD"⟩, meters := ["usd"] })],
          meters := [("usd", { unit := .money "USD", cap := some 1 })] } : Policy).warnings
        == [.costThresholdWithoutConsent "a"]
#guard ({ actions := [("a", { consentIfCostOver := some ⟨5, "USD"⟩, meters := ["usd"], consent := .perCall,
                              approvalTtlMs := some 1 })],
          meters := [("usd", { unit := .money "USD", cap := some 1 })] } : Policy).warnings == []

def footgunPolicy : Policy :=
  { meters := [("free", { unit := .calls }),
               ("life", { unit := .calls, cap := some 10, scope := .principal }),
               ("odd", { unit := .money "USD", cap := some 5, maxPerCall := some 9 })]
    actions := [("r", { idempotent := true, retryAfterUnknown := true, maxAttempts := 1 })] }
#guard footgunPolicy.check == []
#guard footgunPolicy.warnings
        == [.meterWithoutCap "free", .principalMeterWithoutWindow "life", .perCallAboveCap "odd",
            .retryWithoutAttempts "r"]
#guard (footgunPolicy.warnings.map Warning.code)
        == ["meter_without_cap", "principal_meter_without_window", "per_call_above_cap", "retry_without_attempts"]
#guard ({ meters := [("free", { unit := .money "USD", scope := .principal, maxPerCall := some 3 })] }
        : Policy).warnings == [.meterWithoutCap "free"]
#guard ({ meters := [("ok", { unit := .money "USD", cap := some 10, windowMs := some 1000,
                              maxPerCall := some 10, scope := .principal })] } : Policy).warnings == []
#guard ({ meters := [("ok", { unit := .calls, cap := some 10 })] } : Policy).warnings == []
#guard ({ actions := [("r", { idempotent := true, retryAfterUnknown := true, maxAttempts := 2 })] }
        : Policy).warnings == []
#guard ({ actions := [("r", { maxAttempts := 1 })] } : Policy).warnings == []
#guard ({ actions := [("r", { idempotent := true, retryAfterUnknown := true, maxAttempts := 0 })] }
        : Policy).warnings == []
#guard ({ meters := [("free", { unit := .calls })],
          actions := [("a", { consent := .perCall })] } : Policy).warnings
        == [.noApprovalTtl, .meterWithoutCap "free"]
#guard { trifectaPolicy { flags := [.sendsExternal] } with meters := [("free", { unit := .calls })] }.warnings
        == [.lethalTrifecta "r" "i" "s", .meterWithoutCap "free"]

#guard messageWarnings (.obj #[("actions", .obj #[("a", .obj #[("messages", .obj #[])]), ("b", .obj #[])])])
        == [.messagesNotApplied "a"]
#guard messageWarnings (.obj #[("actions", .obj #[("b", .obj #[])])]) == []
#guard messageWarnings (.obj #[]) == []

def groupPolicy (c : Consent) : Policy :=
  { approverRoles := ["f"], actions := [("a", { consent := c })] }
#guard (groupPolicy ⟨[⟨[], false⟩]⟩).check == [.emptyConsentGroup "a"]
#guard (groupPolicy ⟨[⟨[], true⟩]⟩).check == [.emptyConsentGroup "a"]
#guard (groupPolicy ⟨[⟨[⟨1, some ["f"], true, false⟩], false⟩, ⟨[], false⟩]⟩).check == [.emptyConsentGroup "a"]
#guard (groupPolicy .perCall).check == []
#guard (groupPolicy .none).check == []
#guard ({ approverRoles := ["f"], actions := [("a", { escalate := [("e", { consent := ⟨[⟨[], false⟩]⟩ })] })] }
        : Policy).check == [.emptyConsentGroup "a"]
