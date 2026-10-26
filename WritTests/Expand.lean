import Writ
import WritTests.JsonHelpers
import WritTests.Layer2Codec

open Writ

namespace WritTests.Expand

open WritTests.Layer2Codec (specLayer2 doc layer1Docs)

/-! A document that does not parse makes every helper return a sentinel no guard expects (an
action named after the error with `max_attempts` 0, a problem or message naming it), so a typo in a
test document fails its guard instead of testing an empty policy. -/

def files (leaf : String) (parents : List (String × String)) : Except String (File2 × List File2) := do
  pure (← File2.parseDoc leaf, ← parents.mapM fun (n, t) => File2.parseDoc t n)

def exp (leaf : String) (parents : List String := []) : Policy :=
  match files leaf (parents.map ("", ·)) with
  | .ok (l, ps) => expand (ps.map (·.policy)) l.policy
  | .error e => { approverRoles := ["parse error"], actions := [("parse error: " ++ e, { maxAttempts := 0 })] }

def act (p : Policy) (n : String) : Requirements := (p.action? n).getD { maxAttempts := 99 }

/-- For guards on one field, so a missing action (or an unparsed document) never matches a default. -/
def act? (p : Policy) (n : String) : Option Requirements := p.action? n

def probs (leaf : String) (parents : List (String × String) := []) : List Problem2 :=
  match files leaf parents with
  | .ok (l, ps) => Policy2.problems ps l
  | .error e => [.conflictingField "parse error" e]

def chk (leaf : String) (parents : List (String × String) := []) : List String :=
  match files leaf parents with
  | .ok (l, ps) => Policy2.check ps l
  | .error e => ["parse error: " ++ e]

#guard (probs "{\"writ\":\"0.1\",\"rules\":[").map (·.action?) == [some "parse error"]
#guard (exp (doc "\"actions\":{\"a\":{\"consnet\":\"none\"}}")).check != []
#guard chk (doc "\"actions\":{\"a\":{\"consnet\":\"none\"}}") == ["parse error: actions.a.consnet: unknown field"]

def riskLabels : String :=
  "\"labels\":{\"risk\":{\"order\":[\"read\",\"navigate\",\"device\",\"spend\",\"destructive\"]}}"

def specRules : String :=
  "\"rules\":[{\"when\":{\"risk\":\">=device\"},\"require\":{\"consent\":\"per_call\"}}," ++
  "{\"when\":{\"risk\":\">=destructive\"},\"require\":{\"exposed\":false}}]"

/-! The spec's example: `vm.restart` is `device`, so the first rule matches and the second does not. -/
#guard (exp specLayer2).actions.map (·.1) == ["vm.restart"]
#guard act (exp specLayer2) "vm.restart" == { permission := some "vm.power", consent := .perCall }
#guard (exp specLayer2).approverRoles == [] && (exp specLayer2).mode == .enforce

def specPolicy2 : Policy2 := ((File2.parseDoc specLayer2).toOption.map (·.policy)).getD
  { labels := [("parse error", ⟨[]⟩)] }
#guard specPolicy2.resolvedLabel [("risk", "device")] "risk" == some 2
#guard specPolicy2.resolvedLabel [] "risk" == some 4
#guard specPolicy2.resolvedLabel [("risk", "devise")] "risk" == some 4
#guard specPolicy2.resolvedLabel [("risk", "device")] "data" == none
#guard specPolicy2.rules.map (·.matches specPolicy2 ⟨{}, [("risk", "navigate")]⟩) == [false, false]
#guard specPolicy2.rules.map (·.matches specPolicy2 ⟨{}, [("risk", "spend")]⟩) == [true, false]
#guard specPolicy2.rules.map (·.matches specPolicy2 ⟨{}, []⟩) == [true, true]
#guard (Rule.matches specPolicy2 ⟨[], {}⟩ ⟨{}, [("risk", "read")]⟩)
#guard !(Rule.matches specPolicy2 ⟨[("data", "private")], {}⟩ ⟨{}, [("data", "private")]⟩)
#guard !(Rule.matches specPolicy2 ⟨[("risk", "devise")], {}⟩ ⟨{}, [("risk", "destructive")]⟩)

/-! Review Focus 2: an action with no `risk` label takes `destructive`, so it is hidden. -/
def unlabeled : String :=
  doc (riskLabels ++ "," ++ specRules ++ ",\"actions\":{\"files.wipe\":{},\"web.read\":{\"labels\":{\"risk\":\"read\"}}}")
#guard act (exp unlabeled) "files.wipe" == { consent := .perCall, exposed := false }
#guard act (exp unlabeled) "web.read" == {}
#guard probs unlabeled == []

/-! Review Focus 3: a quorum-2 rule drops `grantable`, and the expanded policy checks. -/
def grantEscFwd : String :=
  ",\"escalate\":{\"not_allowlisted\":{\"consent\":\"per_call\",\"grantable\":true}}"
def payDoc (rule : String) : String :=
  doc ("\"approver_roles\":[\"owner\",\"admin\"]," ++ riskLabels ++ ",\"rules\":[" ++ rule ++ "]," ++
    "\"actions\":{\"pay\":{\"labels\":{\"risk\":\"spend\"},\"consent\":\"per_call\"," ++
    "\"grantable\":{\"scope\":\"session\",\"max_uses\":5}}}")
def quorum2 : String := payDoc "{\"when\":{\"risk\":\">=spend\"},\"require\":{\"consent\":{\"quorum\":2}}}"
#guard (act? (exp quorum2) "pay").map (·.grantable) == some (none)
#guard (act? (exp quorum2) "pay").map (·.consent) == some (Consent.perCall.join (.quorum 2 none true false))
#guard chk quorum2 == []
#guard (exp quorum2).check == []
def quorum2Destructive : String :=
  payDoc "{\"when\":{\"risk\":\">=destructive\"},\"require\":{\"consent\":{\"quorum\":2}}}"
#guard (act? (exp quorum2Destructive) "pay").map (·.grantable) == some (some ⟨.session, 5, none, false, false⟩)
def distinctRule : String :=
  payDoc "{\"when\":{},\"require\":{\"consent\":{\"all\":[{\"quorum\":1},{\"quorum\":1,\"roles\":[\"admin\"]}],\"distinct\":true}}}"
#guard (act? (exp distinctRule) "pay").map (·.grantable) == some none && chk distinctRule == []
def payEscDoc (rule : String) : String :=
  doc ("\"approver_roles\":[\"owner\",\"admin\"],\"rules\":[" ++ rule ++ "]," ++
    "\"actions\":{\"pay\":{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"session\",\"max_uses\":5}" ++
    grantEscFwd ++ "}}")
def capRule : String :=
  payDoc "{\"when\":{},\"require\":{\"grantable\":{\"max_uses\":0}}}"
def payEsc2 : String := payEscDoc "{\"when\":{},\"require\":{\"consent\":{\"quorum\":2}}}"
#guard (act? (exp payEsc2) "pay").map (·.grantable) == some (none)
#guard (act? (exp payEsc2) "pay").map (·.escalate) == some ([("not_allowlisted", ⟨.perCall, false⟩)])
#guard chk payEsc2 == []
def payForbid : String := payEscDoc "{\"when\":{},\"require\":{\"grantable\":null}}"
#guard (act? (exp payForbid) "pay").map (·.grantable) == some (none)
#guard (act? (exp payForbid) "pay").map (·.escalate) == some ([("not_allowlisted", ⟨.perCall, false⟩)])
#guard chk payForbid == []
#guard (act? (exp (payEscDoc "{\"when\":{},\"require\":{\"exposed\":false}}")) "pay").map (·.escalate) == some ([("not_allowlisted", ⟨.perCall, true⟩)])
#guard (act? (exp capRule) "pay").map (·.grantable) == some (some ⟨.session, 0, none, false, false⟩)
#guard chk capRule == ["pay: its grantable has max_uses of 0"]

/-! A rule's other fields at the expansion level. -/
def ruleOn? (action rule : String) : Option Requirements :=
  act? (exp (doc ("\"approver_roles\":[\"owner\"],\"rules\":[{\"when\":{},\"require\":" ++ rule ++ "}]," ++
    "\"actions\":{\"a\":" ++ action ++ "}"))) "a"
#guard (ruleOn? "{\"mode\":\"log_only\"}" "{\"mode\":\"enforce\"}").map (·.mode) == some (some .enforce)
#guard (ruleOn? "{}" "{\"mode\":\"log_only\"}").map (·.mode) == some (none)
#guard (ruleOn? "{\"idempotent\":true,\"max_attempts\":2}" "{\"idempotent\":false}").map (·.idempotent) == some (false)
#guard (ruleOn? "{\"idempotent\":true}" "{\"idempotent\":true}").map (·.idempotent) == some (true)
#guard (ruleOn? "{\"flags\":[\"sends_external\"]}" "{\"flags\":[\"reads_private\",\"sends_external\"]}").map (·.flags) == some ([.readsPrivate, .sendsExternal])
#guard (ruleOn? "{\"guards\":[\"z\"]}" "{\"guards\":[\"a\",\"z\"]}").map (·.guards) == some (["a", "z"])
#guard (ruleOn? ("{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"session\",\"max_uses\":20," ++
    "\"max_duration_ms\":3600000,\"any_args\":true}}")
    "{\"grantable\":{\"scope\":\"turn\",\"max_uses\":5,\"any_args\":false}}").map (·.grantable) == some (some ⟨.turn, 5, some 3600000, false, false⟩)
#guard (ruleOn? ("{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"session\",\"max_uses\":20," ++
    "\"max_duration_ms\":3600000,\"any_args\":true}}") "{\"grantable\":{\"max_duration_ms\":60000}}").map (·.grantable) == some (some ⟨.session, 20, some 60000, true, false⟩)
#guard (ruleOn? "{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"session\",\"max_uses\":20}}"
    "{\"grantable\":null}").map (·.grantable) == some (none)

/-! Review Focus 1: a child cannot weaken a parent's action. -/
def orgDoc : String :=
  doc ("\"actions\":{\"files.delete\":{\"exposed\":false},\"pay\":{\"consent\":{\"quorum\":2,\"roles\":[\"finance\"]}}," ++
    "\"book\":{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"turn\",\"max_uses\":5}}}," ++
    "\"rules\":[{\"when\":{},\"require\":{\"guards\":[\"org_ok\"]}}]")
def teamDoc : String :=
  doc ("\"approver_roles\":[\"finance\",\"owner\"],\"extends\":[\"org.json\"]," ++
    "\"actions\":{\"files.delete\":{\"exposed\":true},\"pay\":{\"consent\":\"per_call\"}," ++
    "\"book\":{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"session\",\"max_uses\":50}},\"team.only\":{}}")
def team : Policy := exp teamDoc [orgDoc]
#guard (act? team "files.delete").map (·.exposed) == some (false)
#guard (act? team "pay").map (·.consent) == some (Consent.perCall.join (.quorum 2 (some ["finance"]) true false))
#guard (act? team "book").map (·.grantable) == some (some ⟨.turn, 5, none, false, false⟩)
#guard team.actions.map (·.1) == ["files.delete", "pay", "book", "team.only"]
#guard team.actions.all fun (_, r) => r.guards == ["org_ok"]
#guard team.approverRoles == ["finance", "owner"]
#guard probs teamDoc [("org.json", orgDoc)] == []
#guard chk teamDoc [("org.json", orgDoc)] == []

/-! `permission`, `meters`, `review` and `messages` come from whichever file sets them, and must agree. -/
def permParent : String := doc "\"actions\":{\"a\":{\"permission\":\"p\",\"max_attempts\":3},\"b\":{}}"
#guard (act? (exp (doc "\"rules\":[],\"actions\":{\"a\":{}}") [permParent]) "a").map (·.permission) == some (some "p")
#guard probs (doc "\"rules\":[],\"actions\":{\"a\":{\"permission\":\"p\"}}") [("org.json", permParent)] == []
#guard probs (doc "\"rules\":[],\"actions\":{\"a\":{\"permission\":\"q\"}}") [("org.json", permParent)]
  == [.conflictingField "a" "permission"]
#guard chk (doc "\"rules\":[],\"actions\":{\"a\":{\"permission\":\"q\"}}") [("org.json", permParent)]
  == ["a: the policy and the policies it extends set \"permission\" to different values"]
#guard probs (doc "\"rules\":[],\"actions\":{\"a\":{\"permission\":null}}") [("org.json", permParent)]
  == [.conflictingField "a" "permission"]
#guard probs (doc "\"rules\":[],\"actions\":{\"b\":{\"review\":{\"title\":\"x\"}}}")
    [("org.json", doc "\"actions\":{\"b\":{\"review\":{\"title\":\"y\"}}}")]
  == [.conflictingField "b" "review"]
def srcOf (c : Char) : String := "{\"tool_digest\":\"sha256:" ++ String.ofList (List.replicate 64 c) ++ "\"}"
#guard probs (doc ("\"rules\":[],\"actions\":{\"b\":{\"source\":" ++ srcOf 'a' ++ "}}"))
    [("org.json", doc ("\"actions\":{\"b\":{\"source\":" ++ srcOf 'b' ++ "}}"))]
  == [.conflictingField "b" "source"]
#guard chk (doc ("\"rules\":[],\"actions\":{\"b\":{\"source\":" ++ srcOf 'a' ++ "}}"))
    [("org.json", doc ("\"actions\":{\"b\":{\"source\":" ++ srcOf 'b' ++ "}}"))]
  == ["b: the policy and the policies it extends set \"source\" to different values"]
#guard probs (doc ("\"rules\":[],\"actions\":{\"b\":{\"source\":" ++ srcOf 'a' ++ "}}"))
    [("org.json", doc ("\"actions\":{\"b\":{\"source\":" ++ srcOf 'a' ++ "}}"))]
  == []
#guard probs (doc "\"rules\":[],\"actions\":{\"b\":{}}")
    [("org.json", doc ("\"actions\":{\"b\":{\"source\":" ++ srcOf 'a' ++ "}}"))]
  == []
#guard probs (doc "\"rules\":[],\"actions\":{\"b\":{\"meters\":[\"m\",\"n\"]}}")
    [("org.json", doc "\"actions\":{\"b\":{\"meters\":[\"n\",\"m\"]}}")]
  == [.conflictingField "b" "meters"]
#guard probs (doc "\"rules\":[],\"actions\":{\"b\":{\"consent\":\"per_call\"}}")
    [("org.json", doc "\"actions\":{\"b\":{\"consent\":\"none\"}}")]
  == []

/-! `consent_if_cost_over`, `escalate`, `max_attempts` and the TTLs join across the files that name
an action, a file that does not write one taking the layer-1 default, so a child cannot weaken them. -/
def buyOrg : String :=
  doc ("\"actions\":{\"shop.buy\":{\"consent\":{\"quorum\":2,\"roles\":[\"finance\"]}," ++
    "\"escalate\":{\"over_limit\":{\"consent\":\"per_call\"}}," ++
    "\"max_attempts\":3,\"approval_ttl_ms\":600000," ++
    "\"consent_if_cost_over\":{\"amount\":\"5000\",\"currency\":\"USD\"}}}")
def buyTeam (fields : String) : String :=
  doc ("\"approver_roles\":[\"finance\"],\"actions\":{\"shop.buy\":{" ++ fields ++ "}}")
def buy? (fields : String) : Option Requirements := act? (exp (buyTeam fields) [buyOrg]) "shop.buy"
def quorum2Finance : Consent := .quorum 2 (some ["finance"]) true false
def overLimit : Escalator := ⟨.perCall, false⟩

-- The reviewer's case: a higher threshold in the team does not waive the org's quorum-2 consent.
def highThreshold : String := "\"consent_if_cost_over\":{\"amount\":\"100000000\",\"currency\":\"USD\"}"
#guard (buy? highThreshold).map (·.consent) == some (quorum2Finance)
#guard (buy? highThreshold).map (·.consentIfCostOver) == some (some ⟨5000, "USD"⟩)
#guard (buy? highThreshold).map (·.effectiveConsent (some ⟨50000, "USD"⟩) [("over_limit", false)])
  == some quorum2Finance
#guard probs (buyTeam highThreshold) [("org.json", buyOrg)] == []
#guard chk (buyTeam highThreshold) [("org.json", buyOrg)] == []
#guard (buy? "\"consent_if_cost_over\":{\"amount\":\"100\",\"currency\":\"USD\"}").map (·.consentIfCostOver) == some (some ⟨100, "USD"⟩)
#guard (buy? "").map (·.consentIfCostOver) == some (none)
def euro : String := "\"consent_if_cost_over\":{\"amount\":\"100\",\"currency\":\"EUR\"}"
#guard (buy? euro).map (·.consentIfCostOver) == some (none)
#guard probs (buyTeam euro) [("org.json", buyOrg)] == [.conflictingCurrency "shop.buy" [("", "EUR"), ("org.json", "USD")]]
#guard chk (buyTeam euro) [("org.json", buyOrg)] ==
  ["shop.buy: consent_if_cost_over uses different currencies (EUR in this policy, USD in org.json), so it never lowers consent"]

-- Escalators: the union by reason, both consents and grantable only if both are.
#guard (buy? "").map (·.escalate) == some ([("over_limit", overLimit)])
#guard (buy? "\"escalate\":{\"dangerous\":{\"consent\":\"per_call\"}}").map (·.escalate) == some ([("dangerous", ⟨.perCall, false⟩), ("over_limit", overLimit)])
#guard (buy? "\"escalate\":{\"over_limit\":{\"consent\":{\"quorum\":1,\"roles\":[\"finance\"]}}}").map (·.escalate) == some ([("over_limit", ⟨(Consent.quorum 1 (some ["finance"]) true false).join .perCall, false⟩)])
#guard probs (buyTeam "\"escalate\":{\"dangerous\":{\"consent\":\"per_call\"}}") [("org.json", buyOrg)] == []
#guard escJoin [("x", ⟨.perCall, true⟩), ("y", ⟨.none, true⟩)] [("x", ⟨.perCall, false⟩)]
  == [("x", ⟨.perCall, false⟩), ("y", ⟨.none, true⟩)]
#guard escJoin [("x", ⟨.perCall, true⟩)] [("x", ⟨.perCall, true⟩)] == [("x", ⟨.perCall, true⟩)]

-- `max_attempts`: the smaller, a file that does not write it meaning 1.
#guard (buy? "\"max_attempts\":5").map (·.maxAttempts) == some (3)
#guard (buy? "\"max_attempts\":2").map (·.maxAttempts) == some (2)
#guard (buy? "").map (·.maxAttempts) == some (1)
#guard probs (buyTeam "\"max_attempts\":5") [("org.json", buyOrg)] == []

-- TTLs: the shortest written; a file that does not write one has no opinion.
#guard (buy? "\"approval_ttl_ms\":60000").map (·.approvalTtlMs) == some (some 60000)
#guard (buy? "\"approval_ttl_ms\":6000000").map (·.approvalTtlMs) == some (some 600000)
#guard (buy? "").map (·.approvalTtlMs) == some (some 600000)
#guard (buy? "\"authorized_ttl_ms\":1000").map (·.authorizedTtlMs) == some (some 1000)
#guard (buy? "").map (·.authorizedTtlMs) == some (none)

/-! Taking `grantable` away also takes it from the escalators, so the expansion still checks. -/
def grantEsc : String :=
  ",\"escalate\":{\"not_allowlisted\":{\"consent\":\"per_call\",\"grantable\":true}}"
def bookOrg : String :=
  doc ("\"actions\":{\"book\":{\"consent\":\"per_call\",\"grantable\":{\"scope\":\"session\",\"max_uses\":5}" ++
    grantEsc ++ "}}")
def bookTeam : String := doc "\"approver_roles\":[\"owner\"],\"actions\":{\"book\":{\"guards\":[\"g\"]}}"
#guard (act? (exp bookTeam [bookOrg]) "book").map (·.grantable) == some (none)
#guard (act? (exp bookTeam [bookOrg]) "book").map (·.escalate) == some ([("not_allowlisted", ⟨.perCall, false⟩)])
#guard chk bookTeam [("org.json", bookOrg)] == []
#guard (act? (exp (doc ("\"approver_roles\":[\"owner\"],\"actions\":{\"book\":{\"consent\":\"per_call\"," ++
    "\"grantable\":{\"scope\":\"session\",\"max_uses\":5}" ++ grantEsc ++ "}}"))) "book").map (·.escalate) == some ([("not_allowlisted", ⟨.perCall, true⟩)])
-- A file that writes a grantable escalator without `grantable` is a layer-2 problem; the expansion
-- itself clears the escalator, so the layer-1 check does not report it a second time.
def escNoGrant : String :=
  doc ("\"approver_roles\":[\"owner\"],\"actions\":{\"book\":{\"consent\":\"per_call\"" ++ grantEsc ++ "}}")
#guard probs escNoGrant == [.grantableEscalatorWithoutGrantable "" "book" "not_allowlisted"]
#guard chk escNoGrant == ["book: escalator \"not_allowlisted\" is grantable but the action has no grantable"]
#guard (act? (exp escNoGrant) "book").map (·.escalate) == some [("not_allowlisted", ⟨.perCall, false⟩)]
#guard probs bookTeam [("org.json", bookOrg)] == []
#guard probs bookTeam [("org.json", doc ("\"actions\":{\"book\":{\"consent\":\"per_call\"" ++ grantEsc ++ "}}"))]
  == [.grantableEscalatorWithoutGrantable "org.json" "book" "not_allowlisted"]
#guard chk bookTeam [("org.json", doc ("\"actions\":{\"book\":{\"consent\":\"per_call\"" ++ grantEsc ++ "}}"))]
  == ["book: escalator \"not_allowlisted\" is grantable but the action has no grantable (in org.json)"]

/-! Monotone without a check: dropping `grantable` from an action never loosens its expansion. -/
def monoDoc (grant : String) : String :=
  doc ("\"approver_roles\":[\"owner\"],\"rules\":[{\"when\":{},\"require\":{\"consent\":{\"quorum\":2}}}]," ++
    "\"actions\":{\"pay\":{\"consent\":\"per_call\"" ++ grant ++
    ",\"escalate\":{\"x\":{\"consent\":\"per_call\",\"grantable\":true}}}}")
def monoA : Option Requirements := act? (exp (monoDoc ",\"grantable\":{\"scope\":\"session\",\"max_uses\":5}")) "pay"
def monoA' : Option Requirements := act? (exp (monoDoc "")) "pay"
#guard match (File2.parseDoc (monoDoc ",\"grantable\":{\"scope\":\"session\",\"max_uses\":5}")).toOption,
    (File2.parseDoc (monoDoc "")).toOption with
  | some a, some a' => match a.policy.actions, a'.policy.actions with
    | [(_, x)], [(_, x')] => decide (x.req.le x'.req)
    | _, _ => false
  | _, _ => false
#guard match monoA, monoA' with
  | some e, some e' => decide (e.le e') && e.escalate == e'.escalate && e.escalate == [("x", ⟨.perCall, false⟩)]
  | _, _ => false

-- An escalator with no consent that is grantable adds nothing, like an absent one, so expansion
-- drops it rather than making it non-grantable.
def bottomEsc : String := ",\"escalate\":{\"x\":{\"consent\":\"none\",\"grantable\":true}}"
def payOnly (extra : String) : String :=
  doc ("\"approver_roles\":[\"owner\"],\"actions\":{\"pay\":{\"consent\":\"per_call\"" ++ extra ++ "}}")
def reqOf (text : String) : Option Requirements :=
  (File2.parseDoc text).toOption.bind fun f => (f.policy.actions.lookup "pay").map (·.req)
#guard match reqOf (payOnly bottomEsc), reqOf (payOnly "") with
  | some a, some a' => decide (a.le a')
  | _, _ => false
#guard match act? (exp (payOnly bottomEsc)) "pay", act? (exp (payOnly "")) "pay" with
  | some e, some e' => decide (e.le e') && e.escalate == []
  | _, _ => false
def payOrgBottom : String := doc ("\"actions\":{\"pay\":{\"consent\":\"per_call\"" ++ bottomEsc ++ "}}")
#guard match act? (exp (payOnly "") [payOrgBottom]) "pay", act? (exp (payOnly "")) "pay" with
  | some e, some e' => decide (e.le e') && e.escalate == []
  | _, _ => false
#guard (act? (exp (payOnly (",\"grantable\":{\"scope\":\"session\",\"max_uses\":5}" ++ bottomEsc))) "pay").map
    (·.escalate) == some [("x", ⟨.none, true⟩)]

/-! An extended policy may not set policy-level fields, written defaults included. -/
def meteredParent : String := doc "\"meters\":{\"calls\":{\"unit\":\"calls\",\"cap\":5}},\"actions\":{}"
#guard probs (doc "\"rules\":[]") [("org.json", meteredParent)] == [.parentPolicyField "org.json" "meters"]
#guard chk (doc "\"rules\":[]") [("org.json", meteredParent)]
  == ["an extended policy (in org.json) sets policy-level field \"meters\"; only the extending policy may"]
#guard probs (doc "\"rules\":[]") [("org.json", doc "\"mode\":\"enforce\",\"$schema\":\"x\",\"extends\":[]")]
  == [.parentPolicyField "org.json" "mode"]
#guard probs (doc "\"mode\":\"enforce\",\"rules\":[]") [("org.json", doc "\"labels\":{}")] == []

/-! A policy that extends others may not turn on policy-wide `log_only`, which would shadow every
action the files it extends require; per-action `log_only` on a parent's action leaves it at the
policy's mode, since `log_only` needs every naming file to say so. -/
#guard probs (doc "\"mode\":\"log_only\",\"rules\":[]") [("org.json", doc "\"labels\":{}")] == [.extendsLogOnly]
#guard chk (doc "\"mode\":\"log_only\",\"rules\":[]") [("org.json", doc "\"labels\":{}")] ==
  ["the policy extends other policies and sets \"mode\": \"log_only\", so every action they require " ++
    "would only be logged; set \"mode\": \"log_only\" on this policy's own actions instead"]
#guard probs (doc "\"mode\":\"log_only\",\"rules\":[]") == []
#guard probs (doc "\"mode\":\"log_only\",\"rules\":[]") [] == []
def dropOrg : String := doc "\"actions\":{\"db.drop\":{\"consent\":{\"quorum\":2}}}"
def dropLeaf : String :=
  doc "\"approver_roles\":[\"dba\"],\"extends\":[\"org.json\"],\"actions\":{\"db.drop\":{\"mode\":\"log_only\"},\"mine\":{\"mode\":\"log_only\"}}"
#guard probs dropLeaf [("org.json", dropOrg)] == []
#guard (act? (exp dropLeaf [dropOrg]) "db.drop").map (·.mode) == some none
#guard (act? (exp dropLeaf [dropOrg]) "mine").map (·.mode) == some (some .logOnly)
#guard (exp dropLeaf [dropOrg]).modeOf "db.drop" == .enforce

/-! Labels: dimensions merge, and each file that names an action gives its own view of the labels,
an unlabeled dimension being the strictest, joined by max, so no file can lower another's. -/
def labeledOrg : String :=
  doc (riskLabels ++ "," ++ specRules ++ ",\"actions\":{\"files.delete\":{\"labels\":{\"risk\":\"destructive\"}}," ++
    "\"web.read\":{\"labels\":{\"risk\":\"read\"}},\"tool.x\":{}}")
def relabel : String :=
  doc "\"actions\":{\"files.delete\":{\"labels\":{\"risk\":\"read\"}},\"web.read\":{\"guards\":[\"g\"]},\"tool.x\":{\"labels\":{\"risk\":\"read\"}}}"
-- A child relabels the org's `destructive` action as `read`: still hidden by the org's rule.
#guard act (exp relabel [labeledOrg]) "files.delete" == { consent := .perCall, exposed := false }
-- The parent names `tool.x` unlabeled, the child labels it `read`: it resolves strictest.
#guard act (exp relabel [labeledOrg]) "tool.x" == { consent := .perCall, exposed := false }
-- The child names the parent's `read` action without labels: it resolves strictest.
#guard act (exp relabel [labeledOrg]) "web.read" == { guards := ["g"], consent := .perCall, exposed := false }
#guard act (exp (doc "\"actions\":{\"web.read\":{\"labels\":{\"risk\":\"read\"},\"guards\":[\"g\"]}}") [labeledOrg])
    "web.read" == { guards := ["g"] }
#guard act (exp labeledOrg) "web.read" == {}
#guard probs relabel [("org.json", labeledOrg)] == []
#guard act (exp (doc "\"actions\":{\"web.read\":{\"labels\":{\"risk\":\"spend\"}}}") [labeledOrg]) "web.read"
  == { consent := .perCall }
#guard act (exp (doc "\"actions\":{\"mine\":{\"labels\":{\"risk\":\"navigate\"}}}") [labeledOrg]) "mine" == {}
#guard mergedActionLabels [("risk", ⟨["read", "spend"]⟩), ("data", ⟨["public", "private"]⟩)]
    [[("risk", "read")], [("risk", "spend"), ("data", "public")], [("risk", "read")]]
  == [("risk", "spend"), ("data", "private")]
#guard mergedActionLabels [("risk", ⟨["read", "spend"]⟩), ("data", ⟨["public", "private"]⟩)]
    [[("risk", "read"), ("data", "public")], [("risk", "read"), ("data", "public")]]
  == [("risk", "read"), ("data", "public")]
#guard mergedActionLabels [("risk", ⟨["read", "spend"]⟩)] [[("risk", "huge")]] == [("risk", "spend")]
#guard mergedActionLabels [("risk", ⟨["read", "spend"]⟩), ("data", ⟨["public", "private"]⟩)] []
  == [("risk", "spend"), ("data", "private")]

/-! Layer-2 problems. -/
#guard probs (doc (riskLabels ++ ",\"actions\":{\"a\":{\"labels\":{\"risk\":\"huge\",\"data\":\"private\"}}}"))
  == [.unknownLabelValue "" "a" "risk" "huge", .unknownLabelDimension "" "a" "data"]
#guard probs (doc "\"actions\":{\"a\":{\"labels\":{\"data\":\"private\"}}}")
    [("org.json", doc "\"labels\":{\"data\":{\"order\":[\"public\",\"private\"]}}")]
  == []
#guard probs (doc "\"labels\":{\"data\":{\"order\":[\"public\",\"private\"]}}")
    [("org.json", doc "\"labels\":{\"data\":{\"order\":[\"public\",\"internal\",\"private\"]}}")]
  == [.conflictingDimension "data"]

/-! The codec refuses a duplicate order value, so these are Lean-built: a parent's duplicate is
reported with its file, and so is one the leaf shares with it, once per file. -/
def dupDims : Policy2 := { labels := [("risk", ⟨["low", "high", "low"]⟩)] }
#guard Policy2.problems [] ⟨dupDims, {}, "", []⟩ == [.duplicateLabelValue "" "risk" "low"]
#guard Policy2.problems [⟨dupDims, {}, "org.json", []⟩] ⟨{}, {}, "", []⟩ == [.duplicateLabelValue "org.json" "risk" "low"]
#guard Policy2.problems [⟨dupDims, {}, "org.json", []⟩] ⟨dupDims, {}, "", []⟩ ==
  [.duplicateLabelValue "" "risk" "low", .duplicateLabelValue "org.json" "risk" "low"]
#guard Policy2.check [] ⟨dupDims, {}, "", []⟩ ==
  ["label dimension \"risk\" lists value \"low\" twice in its order"]
#guard Policy2.check [⟨dupDims, {}, "org.json", []⟩] ⟨{}, {}, "", []⟩ ==
  ["label dimension \"risk\" lists value \"low\" twice in its order (in org.json)"]
#guard Policy2.problems [] ⟨{ labels := [("risk", ⟨["low", "high"]⟩)] }, {}, "", []⟩ == []
#guard firstDupValue ["a", "b", "c", "b", "a"] == some "a" && firstDupValue ["a", "b"] == none
#guard probs (doc (riskLabels ++ ",\"approver_roles\":[\"owner\"],\"rules\":[" ++
    "{\"when\":{\"risk\":\">=huge\",\"data\":\">=private\"},\"require\":{}}," ++
    "{\"when\":{},\"require\":{\"consent\":{\"all\":[{\"quorum\":1,\"roles\":[]},{\"quorum\":1,\"roles\":[\"owner\",\"cfo\"]}]}}}]"))
  == [.unknownRuleValue "" 0 "risk" "huge", .unknownRuleDimension "" 0 "data", .ruleEmptyRoles "" 1,
    .ruleUnknownRole "" 1 "cfo"]
#guard probs (doc "\"rules\":[{\"when\":{},\"require\":{\"consent\":{\"quorum\":0}}}]") == [.ruleZeroQuorum "" 0]
#guard chk (doc "\"approver_roles\":[\"owner\"],\"rules\":[{\"when\":{},\"require\":{\"consent\":{\"quorum\":0}}}]")
  == ["rules[0]: a consent clause has a quorum of 0"]

-- A parent reached twice reports each problem once.
#guard probs (doc "\"approver_roles\":[\"owner\"],\"rules\":[]")
    [("org.json", meteredParent), ("org.json", meteredParent ++ "")]
  == [.parentPolicyField "org.json" "meters"]
#guard probs (doc "\"approver_roles\":[\"owner\"],\"rules\":[]")
    [("org.json", doc "\"rules\":[{\"when\":{},\"require\":{\"consent\":{\"quorum\":1,\"roles\":[\"cfo\"]}}}]"),
     ("org.json", doc "\"rules\":[{\"when\":{},\"require\":{\"consent\":{\"quorum\":1,\"roles\":[\"cfo\"]}}}]")]
  == [.ruleUnknownRole "org.json" 0 "cfo"]
#guard probs (doc "\"approver_roles\":[\"owner\"],\"rules\":[]")
    [("org.json", doc "\"rules\":[{\"when\":{},\"require\":{\"consent\":{\"quorum\":1,\"roles\":[\"cfo\"]}}}]")]
  == [.ruleUnknownRole "org.json" 0 "cfo"]
#guard chk (doc "\"approver_roles\":[\"owner\"],\"rules\":[]")
    [("org.json", doc "\"rules\":[{\"when\":{\"risk\":\">=read\"},\"require\":{\"consent\":{\"quorum\":1,\"roles\":[\"cfo\"]}}}]")]
  == ["rules[0] (in org.json): when names dimension \"risk\", which is not declared",
    "rules[0] (in org.json): a consent clause names role \"cfo\", which is not an approver role"]

/-! An extended file's labels and rules are checked against the dimensions it declares and those it
inherits from the files it extends, not the extending policy's: otherwise a leaf could declare a
dimension a parent uses but never declares, in an order that turns the parent's rule off. -/
def invOrg : String :=
  doc ("\"rules\":[{\"when\":{\"risk\":\">=medium\"},\"require\":{\"exposed\":false}}]," ++
    "\"actions\":{\"db.drop\":{\"labels\":{\"risk\":\"high\"}}}")
def invTeam : String :=
  doc "\"approver_roles\":[\"dba\"],\"labels\":{\"risk\":{\"order\":[\"high\",\"medium\"]}},\"actions\":{}"
#guard probs invTeam [("org.json", invOrg)] ==
  [.unknownLabelDimension "org.json" "db.drop" "risk", .unknownRuleDimension "org.json" 0 "risk"]
#guard act? (exp invTeam [invOrg]) "db.drop" == some {}
#guard chk invTeam [("org.json", invOrg)] ==
  ["db.drop: it is labeled on dimension \"risk\", which is not declared (in org.json)",
    "rules[0] (in org.json): when names dimension \"risk\", which is not declared"]

def lowHigh : List (String × LabelDim) := [("risk", ⟨["low", "high"]⟩)]
def parentFile (text : String) (inherited : List (String × LabelDim)) : File2 :=
  match File2.parseDoc text "team.json" with
  | .ok f => { f with inherited }
  | .error e => { policy := {}, name := "parse error: " ++ e }
def teamUses (label : String) : String :=
  doc ("\"rules\":[{\"when\":{\"risk\":\">=high\"},\"require\":{\"exposed\":false}}]," ++
    "\"actions\":{\"a\":{\"labels\":{\"risk\":\"" ++ label ++ "\"}}}")
def lowHighOrg : File2 := { policy := { labels := lowHigh }, name := "org.json" }
-- The dimension comes from the file `team.json` extends: no problem.
#guard Policy2.problems [parentFile (teamUses "low") lowHigh, lowHighOrg] { policy := {} } == []
-- Without it, both the label and the rule are on an undeclared dimension for `team.json`.
#guard Policy2.problems [parentFile (teamUses "low") [], lowHighOrg] { policy := {} } ==
  [.unknownLabelDimension "team.json" "a" "risk", .unknownRuleDimension "team.json" 0 "risk"]
-- A value is checked against the order the file sees.
#guard Policy2.problems [parentFile (teamUses "huge") lowHigh, lowHighOrg] { policy := {} } ==
  [.unknownLabelValue "team.json" "a" "risk" "huge"]
-- The leaf sees every file's dimensions.
#guard probs (doc "\"actions\":{\"a\":{\"labels\":{\"risk\":\"low\"}}}")
    [("team.json", doc "\"actions\":{}"), ("org.json", doc "\"labels\":{\"risk\":{\"order\":[\"low\",\"high\"]}}")]
  == []

/-! A rule that makes an action with `retry_after_unknown` non-idempotent fails the layer-1 check at
that action, so the policy fails closed. -/
#guard chk (doc ("\"rules\":[{\"when\":{},\"require\":{\"idempotent\":false}}]," ++
    "\"actions\":{\"a\":{\"idempotent\":true,\"retry_after_unknown\":true,\"max_attempts\":2}}"))
  == ["a: retry_after_unknown needs the action to be idempotent"]

/-! Layer-2 problems come first, then the expanded policy's. -/
#guard chk (doc "\"rules\":[],\"actions\":{\"a\":{\"labels\":{\"risk\":\"x\"},\"consent\":\"per_call\"}}")
  == ["a: it is labeled on dimension \"risk\", which is not declared",
    "a: it needs approval but the policy has no approver roles"]
#guard chk (doc (riskLabels ++ "," ++ specRules ++ ",\"actions\":{\"a\":{}}"))
  == ["a: it needs approval but the policy has no approver roles"]

def problem2Samples : List Problem2 :=
  [.conflictingDimension "d", .duplicateLabelValue "f" "d" "v", .parentPolicyField "f" "k", .unknownLabelDimension "f" "a" "d",
    .unknownLabelValue "f" "a" "d" "v", .unknownRuleDimension "f" 0 "d", .unknownRuleValue "f" 0 "d" "v",
    .ruleEmptyRoles "f" 0, .ruleZeroQuorum "f" 0, .ruleUnknownRole "f" 0 "r", .conflictingField "a" "k",
    .conflictingCurrency "a" [("", "USD"), ("f", "EUR")], .grantableEscalatorWithoutGrantable "f" "a" "e",
    .extendsLogOnly]
#guard (problem2Samples.map (·.code)).eraseDups.length == problem2Samples.length
#guard problem2Samples.all fun p => p.code.all fun c => c.isLower || c == '_'
#guard problem2Samples.all fun p => !p.message.any fun c => c == '—' || c == '–'

/-! The fields files must agree on are the codec's: every action field neither a rule nor a join sets. -/
#guard agreeFields == ["permission", "meters", "review", "messages", "source"]
#guard (File2.parseDoc (doc ("\"$schema\":\"s\",\"rules\":[],\"actions\":{\"a\":{\"consent\":\"none\"," ++
    "\"meters\":[\"m\"],\"max_attempts\":2,\"review\":{\"b\":1,\"a\":2}}}"))).map (·.facts)
  == .ok ⟨["writ", "$schema", "rules", "actions"], [("a", [("meters", "[\"m\"]"), ("review", "{\"a\":2,\"b\":1}")])]⟩

/-! Every layer-1 policy in `schema/examples` and the corpus, read as layer 2, expands to itself. -/
#guard layer1Docs.all fun j =>
  match (decode j : Except DecodeError Policy), (decode j : Except DecodeError Policy2) with
  | .ok p, .ok q =>
    expand [] q == p && Policy.toJsonText (expand [] q) == Policy.toJsonText p &&
      Policy2.check [] { policy := q, facts := DocFacts.ofJson j } == []
  | _, _ => false

end WritTests.Expand
