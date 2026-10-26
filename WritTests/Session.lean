import WritTests.Fixtures

open Writ

def p0 : Policy := { approverRoles := ["owner"] }
#guard last (script p0 [(0, .turnStart true)]) == .rejected .notStarted
#guard last (script p0 [(0, start ["x"] []), (0, start ["x"] [])]) == .rejected .alreadyStarted
#guard last (script p0 [(0, start [] [])] "other") == .rejected .policyDigestMismatch
#guard last (script p0 [(5, start [] []), (4, .turnStart true)]) == .rejected .timeDecreasing
#guard last (script p0 [(0, start [] []), (1, .sessionEnd), (2, .turnStart true)]) == .rejected .sessionEnded
#guard last (script p0 [(0, start [] []), (1, .turnStart true), (2, .turnStart false)]) == .rejected .turnState
#guard last (script p0 [(0, start [] []), (1, .turnEnd)]) == .rejected .turnState
#guard last (script { p0 with limits := { maxStepsPerTurn := some 1 } }
        [(0, start [] []), (1, .turnStart true), (2, .stepStart), (3, .stepStart)]) == .rejected .stepLimit
#guard last (script { p0 with mode := .logOnly, limits := { maxStepsPerTurn := some 1 } }
        [(0, start [] []), (1, .turnStart true), (2, .stepStart), (3, .stepStart)])
        == .ok .none (some (.wouldDeny .stepLimit))

def s1 : State := (step p0 (State.initial "pd") ⟨1, 0, 0, none, start [] []⟩).1
#guard (step p0 s1 ⟨1, 0, 1, none, .turnStart true⟩).2 == .rejected .staleSeq
#guard (step p0 s1 ⟨2, 0, 0, none, .turnStart true⟩).2 == .rejected .stateVersionMismatch
#guard (step p0 s1 ⟨2, 0, 0, none, .turnStart true⟩).1.version == s1.version
#guard (script p0 [(0, start [] []), (1, .turnStart true)]).1.version == 2
#guard (step p0 (State.initial "pd") ⟨1, 0, 0, some "client", start [] []⟩).2
        == (step p0 (State.initial "pd") ⟨1, 0, 0, none, start [] []⟩).2

namespace Sync

def sp : Policy where
  meters := [("pm", { unit := .money "USD", cap := some 100, scope := .principal })]
  actions := [("pay", { meters := ["pm"] })]

def ten : Option Cost := some ⟨10, "USD"⟩
def base : List (Nat × EventBody) :=
  [(0, start [] []), (0, .turnStart true),
   (1, .propose "c1" "pay" "d1" ten [] []), (1, .dispatch "c1" 1 "d1" ten [] "k1"),
   (2, .result "c1" .succeeded none false),
   (3, .propose "c2" "pay" "d1" ten [] []), (3, .dispatch "c2" 1 "d1" ten [] "k2")]
def held : Ledger := (script sp base).1.ledger
def syncWith (f : List MeterEntry → List MeterEntry) : Verdict :=
  last (script sp (base ++ [(4, .ledgerSync { held with entries := f held.entries, version := held.version + 1 })]))

#guard held.entries.map (fun e => (e.call, e.committed)) == [("c1", true), ("c2", false)]
#guard syncWith id == .ok .none none
def syncAfterForeignPrune := syncWith (·.filter (·.call != "c1"))
#guard syncAfterForeignPrune == .ok .none none
def syncMissingReservation := syncWith (·.filter (·.call != "c2"))
#guard syncMissingReservation == .rejected .ledgerConflict
def syncDuplicateOwn := syncWith fun es => es ++ es.filter (·.call == "c2")
#guard syncDuplicateOwn == .rejected .ledgerConflict
def syncChangedEntry := syncWith (·.map fun e => if e.call == "c1" then { e with amount := 9 } else e)
#guard syncChangedEntry == .rejected .ledgerConflict

def kp : Policy := { sp with killSetsTombstone := true }
def killed : List (Nat × EventBody) :=
  [(0, start [] []), (0, .turnStart true),
   (1, .propose "c1" "pay" "d1" ten [] []), (1, .dispatch "c1" 1 "d1" ten [] "k1"),
   (2, .kill), (3, .outcomeUnknown "c1")]
def killedLedger : Ledger := (script kp killed).1.ledger
def cleared : EventBody := .ledgerSync { killedLedger with tombstone := false, version := killedLedger.version + 1 }
def settleAfterClear := checkedScript kp (killed ++ [(4, .sessionEnd), (5, cleared),
  (6, .reconcile "c1" .succeeded none true)])

#guard killedLedger.tombstone
#guard lastChecked (checkedScript kp (killed ++ [(4, cleared)])) == .rejected .ledgerConflict
#guard settleAfterClear.2.1.drop 6 == [.ok .none none, .ok .none none, .ok .none none]
#guard settleAfterClear.2.2
#guard !settleAfterClear.1.ledger.tombstone
#guard settleAfterClear.1.ledger.entries.all (·.call != "c1")

end Sync

#guard last (script p0 [(0, .ledgerSync {})]) == .rejected .notStarted
#guard last (script p0 [(0, start [] []), (1, .sessionEnd), (2, .ledgerSync {})]) == .ok .none Option.none
#guard last (script p0 [(0, start [] []), (1, .sessionEnd), (2, .stepStart)]) == .rejected .sessionEnded

namespace PruneScope

def pol (spendScope : MeterScope) : Policy where
  meters :=
    [ ("spend", { unit := .money "USD", windowMs := some 10, scope := spendScope })
    , ("daily", { unit := .money "USD", scope := .principal }) ]
  actions := [("buy", { meters := ["spend", "daily"] })]

def brought : Ledger :=
  { entries := [{ meter := "spend", session := "other", call := "c0", time := 0, amount := 5, committed := true }] }
def five : Option Cost := some ⟨5, "USD"⟩
def run (p : Policy) : State × List Verdict :=
  script p [(0, start [] [] brought), (100, .turnStart true),
    (100, .propose "c1" "buy" "d1" five [] []), (100, .dispatch "c1" 1 "d1" five [] "k1")]
def keepsOther (p : Policy) : Bool := (run p).1.ledger.entries.any (·.session == "other")

#guard last (run (pol .session)) == .ok .dispatchClaimed none
#guard last (run (pol .principal)) == .ok .dispatchClaimed none
def pruneKeepsOtherScope := keepsOther (pol .session)
#guard pruneKeepsOtherScope
def prunePrincipalByWindow := !keepsOther (pol .principal)
#guard prunePrincipalByWindow

end PruneScope
