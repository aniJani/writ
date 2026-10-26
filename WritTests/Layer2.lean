import Writ

open Writ

#guard decide (Consent.perCall.le (.quorum 2 none true false))
#guard !decide ((Consent.quorum 2 none true false).le .perCall)
#guard decide ((Consent.quorum 1 (some ["owner", "admin"]) true false).le (.quorum 1 (some ["owner"]) true false))
#guard !decide ((Consent.quorum 1 (some ["owner"]) true false).le (.quorum 1 (some ["owner", "admin"]) true false))
#guard decide ((Consent.quorum 1 (some ["owner"]) true false).le .perCall) == false
#guard decide (Consent.perCall.le (.quorum 1 (some ["owner"]) true false))
#guard decide (Consent.none.le .perCall) && decide (Consent.none.le (.quorum 3 (some ["a"]) true true))
#guard !decide (Consent.perCall.le .none)
#guard decide ((Consent.allOf [⟨1, none, true, false⟩]).le (.allOf [⟨1, none, true, false⟩] true))
#guard !decide ((Consent.allOf [⟨1, none, true, false⟩] true).le (.allOf [⟨1, none, true, false⟩]))
#guard decide ((Consent.allOf [⟨1, none, true, false⟩]).le
  (.allOf [⟨1, none, true, false⟩, ⟨1, some ["finance"], true, false⟩]))

def clauseC : Clause := ⟨1, some ["a"], true, false⟩
def clauseA : Clause := ⟨1, some ["a", "b"], true, false⟩

#guard decide ((Consent.allOf [clauseC] true).le (.allOf [clauseC, clauseC] true))
#guard !decide ((Consent.allOf [clauseC, clauseC] true).le (.allOf [clauseC] true))
#guard decide (clauseA.le clauseC)
#guard decide ((Consent.allOf [clauseC] true).le (.allOf [clauseA, clauseC] true))
#guard !decide ((Consent.allOf [clauseA, clauseC] true).le (.allOf [clauseC] true))
#guard decide ((Consent.allOf [clauseA, clauseC]).le (.allOf [clauseC]))
#guard decide ((Consent.allOf [clauseA, clauseC] true).le
  (.allOf [clauseC, ⟨1, some ["b"], true, false⟩] true))

#guard guardJoin ["b", "a"] ["c", "a"] == guardJoin ["c"] ["a", "b"]

#guard Consent.join .perCall .perCall == .perCall
#guard (Consent.join (.quorum 2 none true false) (Consent.join .perCall (.quorum 2 none true false))).groups.length == 2

def grant20 : Grantable := ⟨.session, 20, some 3600000, false, false⟩

#guard (Requirements.joinReq { grantable := some grant20 } { grantable := some .forbid }).grantable == none
#guard (Requirements.joinReq { grantable := some grant20 } { grantable := some (.cap none (some 5) none none) }).grantable
  == some { grant20 with maxUses := 5 }
#guard (Requirements.joinReq { grantable := some grant20 }
    { grantable := some (.cap (some .turn) (some 50) (some 60000) (some false)) }).grantable
  == some ⟨.turn, 20, some 60000, false, false⟩
#guard (Requirements.joinReq {} { grantable := some (.cap none (some 5) none none) }).grantable == none
#guard (Requirements.joinReq { grantable := some grant20 } {}).grantable == some grant20

#guard (Requirements.joinReq { guards := ["b", "a"], flags := [.sendsExternal] }
    { guards := ["a", "c"], flags := [.readsPrivate, .sendsExternal] }).guards == ["a", "b", "c"]
#guard (Requirements.joinReq { guards := ["b", "a"], flags := [.sendsExternal] }
    { guards := ["a", "c"], flags := [.readsPrivate, .sendsExternal] }).flags == [.readsPrivate, .sendsExternal]
#guard (Requirements.joinStrict { flags := [.sendsExternal, .ingestsUntrusted] } { flags := [.ingestsUntrusted] }).flags
  == [.ingestsUntrusted, .sendsExternal]

#guard (Requirements.joinReq { exposed := true } { exposed := some false }).exposed == false
#guard (Requirements.joinReq { exposed := false } { exposed := some true }).exposed == false
#guard (Requirements.joinReq { idempotent := true, retryAfterUnknown := true } { idempotent := some false }).idempotent
  == false
#guard (Requirements.joinReq { mode := some .logOnly } { mode := some .enforce }).mode == some .enforce
#guard (Requirements.joinReq { mode := none } { mode := some .logOnly }).mode == none
#guard (Requirements.joinReq { mode := some .logOnly } {}).mode == some .logOnly
#guard (Requirements.joinStrict { mode := none } { mode := some .logOnly }).mode == none

#guard (Requirements.joinReq { consent := .perCall } { consent := some (.quorum 2 (some ["owner"]) true false) }).consent
  == ⟨Consent.perCall.groups ++ (Consent.quorum 2 (some ["owner"]) true false).groups⟩
#guard (Requirements.joinReq { consent := .perCall, permission := some "p", maxAttempts := 3 } {}).permission == some "p"
#guard (Requirements.joinStrict { permission := some "p", meters := ["m"] } { permission := some "q" }).permission
  == some "p"

#guard decide (Requirements.le { consent := .perCall, grantable := some grant20 }
  (Requirements.joinReq { consent := .perCall, grantable := some grant20 } { grantable := some .forbid }))
#guard !decide (Requirements.le { grantable := none } { grantable := some grant20 })
#guard decide (Requirements.le { permission := some "p" } { permission := some "q" })
#guard decide (Requirements.le { exposed := true } { exposed := false })
#guard !decide (Requirements.le { exposed := false } { exposed := true })
#guard decide (Require.le { consent := some .perCall, grantable := some .forbid, exposed := some false }
  (Requirements.joinReq { grantable := some grant20 } { consent := some .perCall, grantable := some .forbid, exposed := some false }))

example : Policy2 :=
  { base := { approverRoles := ["owner"] }
    «extends» := ["org-baseline.json"]
    labels := [("risk", ⟨["read", "navigate", "device", "spend", "destructive"]⟩)]
    rules := [⟨[("risk", "device")], { consent := some .perCall }⟩, ⟨[("risk", "destructive")], { exposed := some false }⟩]
    actions := [("vm.restart", ⟨{ permission := some "vm.power" }, [("risk", "device")]⟩)] }

