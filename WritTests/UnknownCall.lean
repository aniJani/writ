import WritTests.Fixtures

open Writ

namespace WritTests.UnknownCall

def up : Policy := { approverRoles := ["owner"], actions := [("free", {})] }

def ctx : List (Nat × EventBody) :=
  [(0, start [] [("alice", alice)]), (1, .turnStart true), (2, .propose "c1" "free" "d1" Option.none [] [])]

def before : State := (script up ctx).1
def rid : RequestId := ⟨"s1", "nope", 0⟩

def rejectsUnknown (b : EventBody) : Bool :=
  let r := checkedScript up (ctx ++ [(3, b)])
  r.2.2 && lastChecked r == .rejected .unknownCall && r.1.version == before.version

#guard rejectsUnknown (.approve "nope" rid "alice" "d1" Option.none Option.none)
#guard rejectsUnknown (.reject "nope" rid "alice")
#guard rejectsUnknown (.approvalExpire "nope" rid)
#guard rejectsUnknown (.dispatch "nope" 1 "d1" Option.none [] "k")
#guard rejectsUnknown (.result "nope" .succeeded Option.none false)
#guard rejectsUnknown (.outcomeUnknown "nope")
#guard rejectsUnknown (.reconcile "nope" .succeeded Option.none false)
#guard rejectsUnknown (.cancel "nope")

-- an unknown-tool proposal leaves no record, so its call id is as unknown as one never proposed
def afterUnknownTool (b : EventBody) : Bool :=
  let r := checkedScript up (ctx ++ [(3, .propose "nope" "zz" "d1" Option.none [] []), (4, b)])
  r.2.2 && lastChecked r == .rejected .unknownCall

#guard afterUnknownTool (.approve "nope" rid "alice" "d1" Option.none Option.none)
#guard afterUnknownTool (.dispatch "nope" 1 "d1" Option.none [] "k")
#guard afterUnknownTool (.result "nope" .succeeded Option.none false)
#guard afterUnknownTool (.cancel "nope")

def endedCtx : List (Nat × EventBody) := ctx ++ [(3, .sessionEnd)]
def ended : State := (script up endedCtx).1

def afterEnd (b : EventBody) : State × List Verdict × Bool := checkedScript up (endedCtx ++ [(4, b)])

-- reconcile still reaches the handler after session end; every other call event stops at the envelope
#guard (afterEnd (.reconcile "nope" .succeeded Option.none false)).2.2
#guard lastChecked (afterEnd (.reconcile "nope" .succeeded Option.none false)) == .rejected .unknownCall
#guard (afterEnd (.reconcile "nope" .succeeded Option.none false)).1.version == ended.version
#guard [EventBody.approve "nope" rid "alice" "d1" Option.none Option.none, .reject "nope" rid "alice",
    .approvalExpire "nope" rid, .dispatch "nope" 1 "d1" Option.none [] "k",
    .result "nope" .succeeded Option.none false, .outcomeUnknown "nope", .cancel "nope"].all
  fun b => lastChecked (afterEnd b) == .rejected .sessionEnded

end WritTests.UnknownCall
