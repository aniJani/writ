import WritTests.Fixtures

open Writ

namespace WritTests.Approve

def ap : Policy where
  approverRoles := ["owner", "admin"]
  meters := [("m", { unit := .money "USD", cap := some 100, maxPerCall := some 50 })]
  actions :=
    [ ("call", { consent := .perCall })
    , ("q2", { consent := .quorum 2 Option.none false false })
    , ("human", { consent := .quorum 1 Option.none true false })
    , ("noreq", { consent := .quorum 1 Option.none false true })
    , ("nobody", { consent := .quorum 1 (some []) false false })
    , ("adminOnly", { consent := .quorum 1 (some ["admin"]) false false })
    , ("metered", { consent := .perCall, meters := ["m"] }) ]

def alice2 : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def agentA : ApproverInfo := ⟨"agent", .human, ["owner"]⟩
def u1 : ApproverInfo := ⟨"u1", .human, ["owner"]⟩
def nobodyRole : ApproverInfo := ⟨"carol", .human, ["intern"]⟩

def apprs : List (String × ApproverInfo) :=
  [("alice", alice), ("alice2", alice2), ("bob", bob), ("bot", bot), ("agent", agentA),
   ("u1", u1), ("carol", nobodyRole)]

def rid (g : Nat := 0) : RequestId := ⟨"s1", "c1", g⟩
def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩

def propose (tool : String) (cost : Option Cost := Option.none) : EventBody :=
  .propose "c1" tool "d1" cost [] []

def appr (who : String) (g : Nat := 0) (d : String := "d1") (c : Option Cost := Option.none)
    (e : Option Edit := Option.none) : EventBody :=
  .approve "c1" (rid g) who d c e

def run (p : Policy) (tool : String) (cost : Option Cost := Option.none)
    (rest : List (Nat × EventBody)) : State × List Verdict :=
  script p ([(0, start [] apprs), (1, .turnStart true), (2, propose tool cost)] ++ rest)

def v (tool : String) (b : EventBody) : Verdict := last (run ap tool (rest := [(3, b)]))
def okAuth : Verdict := .ok .authorized Option.none
def okPend : Verdict := .ok .pending Option.none

#guard v "call" (appr "alice") == okAuth
#guard last (run ap "q2" (rest := [(3, appr "alice"), (4, appr "bob")])) == okAuth
#guard last (run ap "q2" (rest := [(3, appr "alice")])) == okPend
#guard last (run ap "q2" (rest := [(3, appr "alice"), (4, appr "alice2")]))
        == .rejected .alreadyApproved

#guard v "human" (appr "bot") == .rejected .approverNotEligible
#guard v "q2" (appr "bot") == okPend
#guard v "call" (appr "agent") == .rejected .approverNotEligible
#guard v "noreq" (appr "u1") == .rejected .approverNotEligible
#guard v "noreq" (appr "alice") == okAuth
#guard v "call" (appr "nobody") == .rejected .unknownApprover
#guard v "nobody" (appr "alice") == .rejected .approverNotEligible
#guard v "adminOnly" (appr "alice") == .rejected .approverNotEligible
#guard v "adminOnly" (appr "bob") == okAuth
#guard v "call" (appr "carol") == .rejected .approverNotEligible

#guard v "call" (appr "alice" (d := "x")) == .rejected .digestMismatch
#guard last (run ap "metered" (usd 5) [(3, appr "alice" (c := usd 6))]) == .rejected .costMismatch
#guard last (run ap "metered" (usd 5) [(3, appr "alice" (c := usd 5))]) == okAuth
#guard v "call" (appr "alice" (g := 1)) == .rejected .staleRequest
#guard v "call" (.approve "other" (rid) "alice" "d1" Option.none Option.none) == .rejected .unknownCall

def edited : Option Edit := some { newDigest := "d2" }
def laundering (bobArgs : EventBody) : Verdict :=
  last (run ap "q2" (rest := [(3, appr "alice" (e := edited)), (4, bobArgs)]))

#guard (run ap "q2" (rest := [(3, appr "alice" (e := edited))])).2.getLast? == some okPend
#guard laundering (appr "bob" (g := 1) (d := "d1")) == .rejected .digestMismatch
#guard laundering (appr "bob" (g := 0) (d := "d2")) == .rejected .staleRequest
#guard laundering (appr "bob" (g := 1) (d := "d2")) == okAuth
#guard laundering (appr "alice2" (g := 1) (d := "d2")) == .rejected .alreadyApproved

#guard last (run { ap with bindingMutable := false } "call"
        (rest := [(3, appr "alice" (e := edited))])) == .rejected .editNotAllowed

def mrun (e : Option Edit) : Verdict :=
  last (run ap "metered" (usd 5) [(3, appr "alice" (c := usd 5) (e := e))])
#guard mrun (some { newDigest := "d2" }) == .rejected .costMissing
#guard mrun (some { newDigest := "d2", newCost := some ⟨1, "EUR"⟩ }) == .rejected .currencyMismatch
#guard mrun (some { newDigest := "d2", newCost := usd 51 }) == .rejected .costAbovePerCall
#guard mrun (some { newDigest := "d2", newCost := usd 50 }) == okAuth
#guard (let r := run ap "metered" (usd 5)
          [(3, appr "alice" (c := usd 5) (e := some { newDigest := "d2", newCost := usd 7 }))]
        match r.1.calls.get? "c1" with
        | some c => c.digest == "d2" && c.cost == usd 7 && c.generation == 1 && c.tally == [("alice", "alice")]
            && c.status == .authorized && c.requestedAt == 3 && c.authorizedAt == some 3
        | Option.none => false)

-- Review Focus 5: TTLs are half-open, valid while time < requestedAt + ttl (spec section 5, limits)
def ttl : Policy := { ap with limits := { approvalTtlMs := some 100 } }
#guard last (run ttl "call" (rest := [(101, appr "alice")])) == okAuth
#guard last (run ttl "call" (rest := [(102, appr "alice")])) == .rejected .approvalExpired
#guard last (run ttl "call" (rest := [(103, appr "alice")])) == .rejected .approvalExpired

def day : Nat := 86400000
def perAction : Policy := { ap with
  limits := { approvalTtlMs := some 600000 }
  actions := ap.actions ++ [("deploy", { consent := .perCall, approvalTtlMs := some (2 * day) })] }
#guard last (run perAction "deploy" (rest := [(2 + day, appr "alice")])) == okAuth
#guard last (run perAction "deploy" (rest := [(2 + 2 * day, appr "alice")])) == .rejected .approvalExpired
#guard last (run perAction "call" (rest := [(2 + 600000, appr "alice")])) == .rejected .approvalExpired
#guard last (run perAction "call" (rest := [(1 + 600000, appr "alice")])) == okAuth
#guard perAction.approvalTtl ((perAction.action? "deploy").getD {}) == some (2 * day)
#guard perAction.approvalTtl ((perAction.action? "call").getD {}) == some 600000
#guard ap.approvalTtl ((ap.action? "call").getD {}) == Option.none

def rej : List (Nat × EventBody) := [(3, .reject "c1" (rid) "alice")]
def reprop : EventBody := .propose "c2" "call" "d1" Option.none [] []
#guard last (run ap "call" (rest := rej)) == .ok .none Option.none
#guard last (run ap "call" (rest := rej ++ [(4, reprop)])) == .ok (.denied .previouslyRejected) Option.none
#guard last (run ap "call" (rest := rej ++ [(4, .turnEnd), (5, .turnStart true),
        (6, .propose "c3" "call" "d1" Option.none [] [])]))
        == .ok (.needsApproval ⟨"s1", "c3", 0⟩) Option.none
#guard last (run ap "call" (rest := rej ++ [(4, appr "alice")])) == .rejected .callEnded
#guard last (run ap "call" (rest := rej ++ [(4, .reject "c1" (rid) "alice")])) == .rejected .callEnded
#guard last (run ap "call" (rest := [(3, .reject "c1" (rid 1) "alice")])) == .rejected .staleRequest
#guard last (run ap "call" (rest := [(3, .reject "c1" (rid) "carol")])) == .rejected .approverNotEligible

namespace Veto

def go (steps : List EventBody) : State × List Verdict × Bool :=
  checkedScript ap ([(0, start [] apprs), (1, .turnStart true), (2, propose "q2")] ++ steps.map (3, ·))
def holds (r : State × List Verdict × Bool) (v : Verdict) : Bool := r.2.2 && lastChecked r == v
def statusOf (r : State × List Verdict × Bool) : Option CallStatus := (r.1.calls.get? "c1").map (·.status)

-- red-team C5: a slow approver's veto of an earlier generation is not lost to an edit
def bobEdits : List EventBody := [appr "bob" (e := some { newDigest := "d2" })]
def lateVeto := go (bobEdits ++ [.reject "c1" (rid 0) "alice"])
#guard holds lateVeto (.ok .none Option.none)
#guard statusOf lateVeto == some .rejected
#guard ("q2", "d1") ∈ lateVeto.1.rejectedMemory && ("q2", "d2") ∈ lateVeto.1.rejectedMemory
#guard holds (go (bobEdits ++ [.reject "c1" (rid 1) "alice"])) (.ok .none Option.none)
#guard holds (go (bobEdits ++ [.reject "c1" (rid 2) "alice"])) (.rejected .staleRequest)
#guard holds (go (bobEdits ++ [.reject "c1" ⟨"s2", "c1", 0⟩ "alice"])) (.rejected .staleRequest)
#guard holds (go (bobEdits ++ [.reject "c1" ⟨"s1", "c9", 0⟩ "alice"])) (.rejected .staleRequest)
#guard statusOf (go (bobEdits ++ [.reject "c1" (rid 2) "alice"])) == some .awaiting

-- the reject records the digest of the generation it echoes, as well as the proposed and current ones
def twoEdits := go [appr "bob" (e := some { newDigest := "d2" }),
  appr "alice" 1 "d2" (e := some { newDigest := "d3" }), .reject "c1" (rid 1) "bob"]
#guard holds twoEdits (.ok .none Option.none)
#guard twoEdits.1.rejectedMemory == [("q2", "d1"), ("q2", "d3"), ("q2", "d2")]
#guard ((twoEdits.1.calls.get? "c1").map (·.generations)) == some [("d1", none), ("d2", none), ("d3", none)]

-- a veto after quorum and before dispatch ends the call
def quorumThenVeto := go [appr "alice", appr "bob", .reject "c1" (rid) "alice"]
#guard holds quorumThenVeto (.ok .none Option.none)
#guard statusOf quorumThenVeto == some .rejected
#guard holds (go [appr "alice", appr "bob", .reject "c1" (rid) "alice",
  .dispatch "c1" 1 "d1" Option.none [] "k"]) (.rejected .callEnded)
#guard holds (go [appr "alice", appr "bob", .dispatch "c1" 1 "d1" Option.none [] "k",
  .reject "c1" (rid) "alice"]) (.rejected .callDispatched)
#guard holds (go [appr "alice", appr "bob", .reject "c1" (rid) "carol"]) (.rejected .approverNotEligible)

end Veto

#guard last (run ap "call" (rest := [(3, .approvalExpire "c1" (rid))])) == .ok .none Option.none
#guard last (run ap "call" (rest := [(3, .approvalExpire "c1" (rid)), (4, appr "alice")]))
        == .rejected .callEnded
#guard last (run ap "call" (rest := [(3, .approvalExpire "c1" (rid 1))])) == .rejected .staleRequest
#guard last (run ap "call" (rest := [(3, appr "alice"), (4, .approvalExpire "c1" (rid))]))
        == .rejected .callAuthorized

def rebind := checkedScript ap [(0, start [] apprs), (1, .turnStart true), (2, propose "q2"),
  (3, appr "bob"), (4, .approverAttest "bob" ⟨"mallory", .human, ["admin"]⟩)]
#guard lastChecked rebind == .rejected .approverChanged
#guard rebind.2.2
def reattest (info : ApproverInfo) := script ap [(0, start [] apprs), (1, .approverAttest "alice" info)]
#guard last (reattest alice) == .ok .none Option.none
#guard (reattest alice).1.approvers.get? "alice" == some alice
#guard last (reattest ⟨"alice", .automated, ["owner"]⟩) == .rejected .approverChanged
#guard last (reattest ⟨"alice", .human, ["admin"]⟩) == .rejected .approverChanged
#guard last (script ap [(0, start [] apprs), (1, .approverAttest "dave" ⟨"dave", .human, ["owner"]⟩)])
        == .ok .none Option.none

namespace Clauses

def fin : ApproverInfo := ⟨"fin", .human, ["finance"]⟩
def mgr : ApproverInfo := ⟨"mgr", .human, ["requester_manager"]⟩
def finmgr : ApproverInfo := ⟨"finmgr", .human, ["finance", "requester_manager"]⟩
def finBot : ApproverInfo := ⟨"fin-bot", .automated, ["finance"]⟩
def aliceFin : ApproverInfo := ⟨"alice", .human, ["finance"]⟩

def finance : Clause := ⟨1, some ["finance"], true, false⟩
def manager : Clause := ⟨1, some ["requester_manager"], true, false⟩

def cp : Policy where
  approverRoles := ["finance", "requester_manager"]
  actions :=
    [ ("both", { consent := .allOf [finance, manager] })
    , ("sod", { consent := .allOf [finance, manager] (distinct := true) })
    , ("twoFin", { consent := .allOf [⟨2, some ["finance"], true, false⟩, manager] (distinct := true) })
    , ("q2", { consent := .quorum 2 Option.none false false }) ]

#guard cp.check.isEmpty

def apprs : List (String × ApproverInfo) :=
  [("fin", fin), ("mgr", mgr), ("finmgr", finmgr), ("finbot", finBot), ("alice", aliceFin),
   ("alice2", aliceFin), ("bob", bob)]

def pr (id tool : String) : EventBody := .propose id tool "d1" Option.none [] []
def appr (id who : String) (g : Nat := 0) (d : String := "d1") (e : Option Edit := Option.none) :
    EventBody :=
  .approve id ⟨"s1", id, g⟩ who d Option.none e
def w (bodies : List EventBody) : State × List Verdict × Bool :=
  checkedScript cp ([(0, start [] apprs), (1, .turnStart true)] ++ bodies.zipIdx.map fun (b, i) => (i + 2, b))

-- overlapping group: one principal may satisfy both clauses
#guard lastChecked (w [pr "c1" "both", appr "c1" "finmgr"]) == .ok .authorized none
-- distinct group: one principal is not enough
#guard lastChecked (w [pr "c1" "sod", appr "c1" "finmgr"]) == .ok .pending none
-- Review Focus 2: greedy order fails, matching succeeds
#guard lastChecked (w [pr "c1" "sod", appr "c1" "finmgr", appr "c1" "fin"]) == .ok .authorized none
#guard (w [pr "c1" "sod", appr "c1" "finmgr", appr "c1" "fin"]).2.2
-- an approver eligible for no clause is refused
#guard lastChecked (w [pr "c1" "sod", appr "c1" "bob"]) == .rejected .approverNotEligible
#guard lastChecked (w [pr "c1" "sod", appr "c1" "finbot"]) == .rejected .approverNotEligible
-- an approver already in the tally may edit
#guard lastChecked (w [pr "c1" "q2", appr "c1" "alice", appr "c1" "alice" 0 "d1" (some ⟨"d2", none, []⟩)]) == .ok .pending none

#guard lastChecked (w [pr "c1" "both", appr "c1" "fin"]) == .ok .pending none
#guard lastChecked (w [pr "c1" "both", appr "c1" "fin", appr "c1" "mgr"]) == .ok .authorized none
#guard lastChecked (w [pr "c1" "sod", appr "c1" "fin", appr "c1" "mgr"]) == .ok .authorized none
#guard lastChecked (w [pr "c1" "sod", appr "c1" "fin", appr "c1" "alice"]) == .ok .pending none
#guard lastChecked (w [pr "c1" "twoFin", appr "c1" "finmgr", appr "c1" "fin"]) == .ok .pending none
#guard lastChecked (w [pr "c1" "twoFin", appr "c1" "finmgr", appr "c1" "fin", appr "c1" "alice"])
        == .ok .authorized none
#guard lastChecked (w [pr "c1" "twoFin", appr "c1" "fin", appr "c1" "alice", appr "c1" "mgr"])
        == .ok .authorized none
#guard lastChecked (w [pr "c1" "q2", appr "c1" "alice", appr "c1" "alice2" 0 "d1" (some ⟨"d2", none, []⟩)])
        == .ok .pending none
#guard ((w [pr "c1" "q2", appr "c1" "alice", appr "c1" "alice" 0 "d1" (some ⟨"d2", none, []⟩)]).1.calls.get? "c1").map
          (fun c => (c.tally, c.generation)) == some ([("alice", "alice")], 1)
#guard lastChecked (w [pr "c1" "q2", appr "c1" "alice", appr "c1" "alice" 0 "d1" (some ⟨"d2", none, []⟩),
          appr "c1" "fin" 1 "d2"]) == .ok .authorized none

-- Eleven distinct slots and ten approvers: refused by counting, not by trying 10! assignments.
def wideRoles : List String := (List.range 11).map (s!"x{·}")

def wide : Policy where
  approverRoles := "finance" :: wideRoles
  actions := [("wide", { consent := .allOf (wideRoles.map fun r => ⟨1, some ["finance", r], true, false⟩) true })]

#guard wide.check.isEmpty

def tenFin : List (String × ApproverInfo) :=
  (List.range 10).map fun i => (s!"f{i}", ⟨s!"f{i}", .human, ["finance"]⟩)

#guard lastChecked (checkedScript wide ([(0, start [] tenFin), (1, .turnStart true), (2, pr "c1" "wide")] ++
          (List.range 10).map fun i => (i + 3, appr "c1" s!"f{i}"))) == .ok .pending none

end Clauses

end WritTests.Approve
