import WritTests.Harness
import WritTests.JsonHelpers

open Writ

namespace WritTests.Explore

def tinyText : String := include_str "../tests/cli/traces/tiny.json"

def parsed (text : String) : Policy × Json :=
  match Policy.parseDoc text with
  | .ok r => r
  | .error _ => ({}, .null)

def cfg : Explore.Config := { depth := 2 }

def tiny : Explore.Result := let (p, doc) := parsed tinyText; Explore.run "tiny" p cfg doc

-- Parsed again from different text, so the compiler cannot share the two runs.
def tinyAgain : Explore.Result :=
  let (p, doc) := parsed (" " ++ tinyText)
  Explore.run "tiny" p cfg doc

#guard tiny == tinyAgain
#guard tiny.traces.all (·.replay.ok)
#guard tiny.traces.all (·.steps.all (·.expect.isSome))
#guard tiny.traces.all fun t => t.steps.length ≤ cfg.depth + 1
#guard (tiny.traces.filter (·.id.startsWith "tiny/a/")).size > 0

def roundTrips (t : Trace) : Bool :=
  ((Json.parse (toJson t).compact).toOption.map fun j => (decode j : Except DecodeError Trace) == .ok t) == some true

#guard tiny.traces.all roundTrips

#guard (tiny.states, tiny.traces.size, tiny.truncated) == (80, 261, false)

def tinyPolicy : Policy := (parsed tinyText).1

def owner : ApproverInfo := ⟨"u1", .human, ["owner"]⟩

def after (steps : List EventBody) : State :=
  (script tinyPolicy (((.sessionStart "s1" "pd" "u1" [] [("u1", owner)] {}) :: steps).map (1, ·))).1

def ping (c d : String) : EventBody := .propose c "ping" d none [] []

#guard Explore.key (after [ping "c1" "d1"]) == Explore.key (after [ping "c2" "d2"])
#guard Explore.key (after [ping "c1" "d1"]) == Explore.key (after [ping "c1" "d2"])
#guard Explore.key (after [ping "c1" "d1", .cancel "c1"]) == Explore.key (after [ping "c2" "d2", .cancel "c2"])
#guard Explore.key (after [ping "c1" "d1"]) != Explore.key (after [ping "c1" "d1", .cancel "c1"])
#guard Explore.key (after [ping "c1" "d1"]) != Explore.key (after [ping "c1" "d1", ping "c2" "d1"])
#guard Explore.key (after [ping "c1" "d1", ping "c2" "d1"]) != Explore.key (after [ping "c1" "d1", ping "c2" "d2"])
-- seq and state_version are not part of the key: an accepted no-op leaves it unchanged.
#guard Explore.key (after [ping "c1" "d1"]) == Explore.key (after [ping "c1" "d1", ping "c1" "d1"])

-- The idempotency key is renamed with its call.
#guard Explore.key (after [ping "c1" "d1", .approve "c1" ⟨"s1", "c1", 0⟩ "u1" "d1" none none,
    .dispatch "c1" 1 "d1" none [] "k-c1"]) ==
  Explore.key (after [ping "c2" "d2", .approve "c2" ⟨"s1", "c2", 0⟩ "u1" "d2" none none,
    .dispatch "c2" 1 "d2" none [] "k-c2"])

/-- `State.findGrant` takes the first valid grant in id order, so grant ids are not renamed: these
two states would get one key under renaming by first occurrence, yet `propose c2 ping d1` is
covered by the `d1` grant in the first and by the `any_args` grant in the second. -/
def grantPing : Requirements :=
  { consent := .perCall, grantable := some ⟨.session, 2, some 1000, true, false⟩ }

def grantPolicy : Policy := { approverRoles := ["owner"], actions := [("ping", grantPing)] }

def granted (first second : Option String) : State :=
  let grant (g : String) (d : Option String) : EventBody :=
    .grantCreate g "u1" "ping" d .session 2 none none (some 1001) "rsd"
  (script grantPolicy ([.sessionStart "s1" "pd" "u1" [] [("u1", owner)] {}, grant "g1" first,
    grant "g2" second, ping "c1" "d2"].map (1, ·))).1

#guard (granted (some "d1") none).grants.size == 2 && (granted none (some "d1")).calls.size == 1
#guard Explore.key (granted (some "d1") none) != Explore.key (granted none (some "d1"))

-- The reserved principal `agent` is kept, like the requester.
#guard ((Explore.key (after [.approverAttest "a4" ⟨"agent", .human, ["owner"]⟩])).splitOn "\"agent\"").length == 2

/-- Money and calls meters, a grant with a duration, guards and escalators: every event the
alphabet builds for them decodes back to itself. -/
def richText : String :=
  "{\"writ\":\"0.1\",\"approver_roles\":[\"owner\",\"finance\"],\"kill_scope\":\"principal\"," ++
  "\"meters\":{\"usd\":{\"currency\":\"USD\",\"cap\":10,\"max_per_call\":5,\"window_ms\":1000}," ++
  "\"calls\":{\"unit\":\"calls\",\"cap\":2,\"scope\":\"principal\"}}," ++
  "\"limits\":{\"approval_ttl_ms\":100,\"max_consecutive_failures\":1}," ++
  "\"actions\":{\"buy\":{\"meters\":[\"usd\",\"calls\"],\"consent\":\"per_call\"," ++
  "\"consent_if_cost_over\":{\"amount\":\"3\",\"currency\":\"USD\"},\"guards\":[\"card\"]," ++
  "\"grantable\":{\"scope\":\"session\",\"max_uses\":2,\"max_duration_ms\":500}}," ++
  "\"run\":{\"permission\":\"run\",\"idempotent\":true,\"retry_after_unknown\":true,\"max_attempts\":2," ++
  "\"escalate\":{\"risky\":{\"consent\":{\"quorum\":1,\"roles\":[\"finance\"]}}}}}}"

def rich : Explore.Result := let (p, doc) := parsed richText; Explore.run "rich" p { depth := 2 } doc

#guard (parsed richText).1.check.isEmpty
#guard rich.traces.all roundTrips
#guard rich.traces.all (·.replay.ok)

def richPolicy : Policy := (parsed richText).1

def usd (n : Nat) : Option Cost := some ⟨n, "USD"⟩

/-- States past depth 2: a dispatched call on both meters, an unknown retry, a grant. -/
def richStates : List State :=
  let start : EventBody := .sessionStart "s1" "pd" "u1" ["run"]
    [("u1", ⟨"u1", .human, ["owner", "finance"]⟩)] {}
  let buy : EventBody := .propose "c1" "buy" "d1" (usd 4) [("card", true)] []
  let approved := [start, buy, .approve "c1" ⟨"s1", "c1", 0⟩ "u1" "d1" (usd 4) none]
  let dispatched := approved ++ [.dispatch "c1" 1 "d1" (usd 4) [("card", true)] "k-c1"]
  let run : List EventBody := [start, .propose "c2" "run" "d2" none [] [("risky", false)],
    .dispatch "c2" 1 "d2" none [] "k-c2", .outcomeUnknown "c2"]
  let granted := [start, .grantCreate "g1" "u1" "buy" (some "d1") .session 2 (usd 1) none (some 500) "rsd", buy]
  [approved, dispatched, dispatched ++ [.result "c1" .succeeded (some 5) false], run, granted].map
    fun steps => (script richPolicy (steps.map (1, ·))).1

def eventRoundTrips (e : Event) : Bool :=
  ((Json.parse (toJson e).compact).toOption.map fun j => Event.decodeWith (some "pd") j == .ok e) == some true

#guard richStates.all fun s => s.calls.size > 0 &&
  (Explore.Alphabet.build richPolicy "pd" |>.events s).all (eventRoundTrips ·.event)

/-- TTLs, a grant duration, a meter window, a cap and `max_uses` at 2^53 - 1 and a cost threshold
of 78 digits:
the explorer drops every event they would push past what the codec reads back, so each trace
survives JSON and replays. -/
def hugeText : String :=
  let big := "9007199254740991"
  let amount := String.ofList (List.replicate 78 '9')
  "{\"writ\":\"0.1\",\"approver_roles\":[\"owner\"]," ++
  s!"\"meters\":\{\"usd\":\{\"currency\":\"USD\",\"cap\":{big},\"window_ms\":{big}}}," ++
  s!"\"limits\":\{\"approval_ttl_ms\":{big}}," ++
  "\"actions\":{\"buy\":{\"meters\":[\"usd\"],\"consent\":\"per_call\"," ++
  s!"\"authorized_ttl_ms\":{big},\"consent_if_cost_over\":\{\"amount\":\"{amount}\",\"currency\":\"USD\"}," ++
  s!"\"grantable\":\{\"scope\":\"session\",\"max_uses\":{big},\"max_duration_ms\":{big}}}}}"

def huge : Explore.Result := let (p, doc) := parsed hugeText; Explore.run "huge" p { depth := 3 } doc

#guard (parsed hugeText).1.actions.length == 1
#guard huge.traces.size > 0
#guard huge.traces.all roundTrips
#guard huge.traces.all (·.replay.ok)

/-- Thirty distinct actions with day-long TTLs: the search must stop at `maxStates`. -/
def many : Policy :=
  { approverRoles := ["owner"]
    actions := (List.range 30).map fun i => (s!"a{i}",
      { permission := some s!"p{i}", consent := .perCall, approvalTtlMs := some 86400000,
        authorizedTtlMs := some 86400000 }) }

#guard let r := Explore.run "many" many { maxStates := 60 }; r.truncated && r.states == 60
#guard let r := Explore.run "many" many { maxStates := 60 }; r.traces.all (·.replay.ok)

end WritTests.Explore
