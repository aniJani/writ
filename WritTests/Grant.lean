import WritTests.Fixtures

open Writ

namespace WritTests.Grant

def gp : Policy where
  approverRoles := ["owner", "admin"]
  meters := [("m", { unit := .money "USD", cap := some 1000 })]
  actions :=
    [ ("call", { consent := .perCall, grantable := some { scope := .session, maxUses := 3 } })
    , ("turnOnly", { consent := .perCall, grantable := some { scope := .turn, maxUses := 3 } })
    , ("anyOk", { consent := .perCall
                  grantable := some { scope := .session, maxUses := 3, anyArgs := true } })
    , ("metered", { consent := .perCall, meters := ["m"]
                    grantable := some { scope := .session, maxUses := 3, anyArgs := true } })
    , ("ownerOnly", { consent := .quorum 1 (some ["owner"]) true false
                      grantable := some { scope := .session, maxUses := 3 } })
    , ("short", { consent := .perCall
                  grantable := some { scope := .session, maxUses := 3, maxDurationMs := some 100 } })
    , ("esc", { consent := .perCall, escalate := [("e", { consent := .quorum 2 none true false })]
                grantable := some { scope := .session, maxUses := 3 } })
    , ("shell", { consent := .none, grantable := some { scope := .session, maxUses := 5 }
                  escalate := [("not_allowlisted", { consent := .perCall, grantable := true }),
                               ("dangerous", { consent := .perCall })] })
    , ("spend", { consent := .perCall
                  grantable := some { scope := .session, maxUses := 10, anyArgs := true } })
    , ("plain", { consent := .perCall }) ]

def gc (id tool : String) (digest : Option String := some "d1") (scope : GrantScope := .session)
    (n : Nat := 3) (nb exp : Option Nat := Option.none) (who : String := "alice")
    (mc : Option Cost := Option.none) : EventBody :=
  .grantCreate id who tool digest scope n mc nb exp "rd"

def pr (id tool : String) (d : String := "d1") (e : List (String × Bool) := []) : EventBody :=
  .propose id tool d Option.none [] e

def ctx : List (Nat × EventBody) :=
  [(0, start [] [("alice", alice), ("bob", bob), ("bot", bot)]), (1, .turnStart true)]

def go (b : List (Nat × EventBody)) : State × List Verdict := script gp (ctx ++ b)
def granted : Verdict := .ok (.allowedByGrant "g1") Option.none
def need (c : String) : Verdict := .ok (.needsApproval ⟨"s1", c, 0⟩) Option.none

#guard last (go [(2, gc "g1" "call"), (3, pr "c1" "call")]) == granted
#guard (go [(2, gc "g1" "call")]).2.getLast? == some (.ok .none Option.none)
#guard last (go [(2, gc "g1" "call" (n := 1)), (3, pr "c1" "call"), (4, pr "c2" "call")]) == need "c2"
#guard last (go [(2, gc "g1" "call"), (3, pr "c1" "call" "d2")]) == need "c1"
#guard last (go [(2, gc "g1" "call" (exp := some 50)), (49, pr "c1" "call")]) == granted
#guard last (go [(2, gc "g1" "call" (exp := some 50)), (50, pr "c1" "call")]) == need "c1"
#guard last (go [(2, gc "g1" "call" (nb := some 10)), (9, pr "c1" "call")]) == need "c1"
#guard last (go [(2, gc "g1" "call" (nb := some 10)), (10, pr "c1" "call")]) == granted
#guard last (go [(2, gc "g1" "turnOnly" (scope := .turn)), (3, pr "c1" "turnOnly")]) == granted
#guard last (go [(2, gc "g1" "turnOnly" (scope := .turn)), (3, .turnEnd), (4, .turnStart true),
        (5, pr "c1" "turnOnly")]) == need "c1"
#guard last (go [(2, .turnEnd), (3, gc "g1" "turnOnly" (scope := .turn))]) == .rejected .turnState
#guard last (go [(2, gc "g1" "turnOnly" (scope := .session))]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "call"), (3, .grantRevoke "g1"), (4, pr "c1" "call")]) == need "c1"
#guard last (go [(2, .grantRevoke "g1")]) == .rejected .unknownGrant
#guard last (go [(2, gc "g1" "call"), (3, gc "g1" "call")]) == .rejected .duplicateGrant
#guard last (go [(2, gc "g1" "nope")]) == .rejected .unknownTool
#guard last (go [(2, gc "g1" "plain")]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "call" (n := 0))]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "call" (n := 4))]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "call" (digest := Option.none))]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "anyOk" (digest := Option.none)), (3, pr "c1" "anyOk" "zz")]) == granted
#guard last (go [(2, gc "g1" "metered" (digest := Option.none))]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "ownerOnly" (who := "bob"))]) == .rejected .approverNotEligible
#guard last (go [(2, gc "g1" "ownerOnly")]) == .ok .none Option.none
#guard last (go [(2, gc "g1" "call" (who := "zed"))]) == .rejected .unknownApprover
#guard last (go [(2, gc "g1" "short")]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "short" (exp := some 103))]) == .rejected .grantNotAllowed
#guard last (go [(2, gc "g1" "short" (exp := some 102))]) == .ok .none Option.none
#guard last (go [(2, gc "g1" "esc"), (3, pr "c1" "esc")]) == need "c1"
#guard last (go [(2, gc "g1" "esc"), (3, pr "c1" "esc" (e := [("e", false)]))]) == granted

def sh (id : String) (e : List (String × Bool)) : EventBody := pr id "shell" (e := e)
def shellGrant : List (Nat × EventBody) :=
  [(2, gc "g1" "shell" (n := 5)), (3, sh "c1" [("not_allowlisted", true), ("dangerous", false)])]

-- a session grant covers a not-allowlisted command
#guard last (go shellGrant) == granted
-- but never a dangerous one
#guard last (go (shellGrant ++ [(4, sh "c2" [("not_allowlisted", true), ("dangerous", true)])])) == need "c2"
-- a missing escalator counts as fired and is not grantable
#guard last (go (shellGrant ++ [(4, sh "c3" [("not_allowlisted", true)])])) == need "c3"
-- an automated approver cannot create a grant that stands in for human-only consent
#guard last (go [(2, gc "g1" "shell" (n := 5) (who := "bot"))]) == .rejected .approverNotEligible
#guard last (go [(2, sh "c1" [("not_allowlisted", false), ("dangerous", false)])]) == .ok .allowed Option.none
#guard last (go [(2, gc "g1" "shell" (n := 5) (who := "bob"))]) == .ok .none Option.none
#guard last (go [(2, gc "g1" "shell" (n := 5) (who := "zed"))]) == .rejected .unknownApprover
#guard last (go [(2, gc "g1" "call" (who := "bot"))]) == .rejected .approverNotEligible

def reserved (r : State × List Verdict) : Option Nat :=
  (r.1.grants.get? "g1").map (·.reserved)

#guard reserved (go [(2, gc "g1" "call"), (3, pr "c1" "call")]) == some 1
#guard reserved (go [(2, gc "g1" "call"), (3, pr "c1" "call"), (4, .sessionEnd)]) == some 0
#guard reserved (go [(2, gc "g1" "call"), (3, pr "c1" "call"), (4, pr "c2" "call"),
        (5, .sessionEnd)]) == some 0

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩
def budgetGrant : EventBody := gc "g1" "spend" (digest := Option.none) (n := 10) (mc := usd 5000)
def sp (id : String) (cost : Option Cost) : EventBody := .propose id "spend" "d1" cost [] []
def cgo (b : List (Nat × EventBody)) := checkedScript gp (ctx ++ b)
def costs (r : State × List Verdict × Bool) : Option (Nat × Nat) :=
  (r.1.grants.get? "g1").map fun g => (g.costConsumed, g.costReserved)

#guard lastChecked (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000))]) == granted
#guard lastChecked (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, sp "c2" (usd 2000))]) == granted
#guard (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, sp "c2" (usd 2000))]).2.2
#guard lastChecked (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, sp "c2" (usd 2000)),
        (5, sp "c3" (usd 1))]) == need "c3"
#guard (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, sp "c2" (usd 2000)),
        (5, sp "c3" (usd 1))]).2.2
#guard costs (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000))]) == some (0, 3000)
#guard costs (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, .dispatch "c1" 1 "d1" (usd 3000) [] "k")])
  == some (3000, 0)
#guard lastChecked (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, .cancel "c1"),
        (5, sp "c2" (usd 3000))]) == granted
#guard costs (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, .cancel "c1")]) == some (0, 0)
#guard (cgo [(2, budgetGrant), (3, sp "c1" (usd 3000)), (4, .cancel "c1"), (5, sp "c2" (usd 3000))]).2.2
#guard lastChecked (cgo [(2, budgetGrant), (3, sp "c1" Option.none)]) == need "c1"
#guard lastChecked (cgo [(2, budgetGrant), (3, sp "c1" (some ⟨100, "EUR"⟩))]) == need "c1"
#guard (cgo [(2, budgetGrant), (3, sp "c1" (some ⟨100, "EUR"⟩))]).2.2
#guard lastChecked (cgo [(2, gc "g1" "spend" (digest := Option.none) (mc := usd 0))])
  == .rejected .grantNotAllowed
#guard lastChecked (cgo [(2, gc "g1" "spend" (digest := Option.none) (n := 1) (mc := usd 5000)),
        (3, sp "c1" (usd 10)), (4, sp "c2" (usd 10))]) == need "c2"

end WritTests.Grant
