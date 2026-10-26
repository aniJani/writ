import Writ

open Writ

namespace WritTests.ProfileVectors

/-- Every call status, `denied` and `denied_at_dispatch` once with each reason. -/
def statuses : List CallStatus :=
  [.awaiting, .authorized, .dispatched, .succeeded, .failed, .declined, .unknown, .rejected,
    .expired, .cancelled] ++ Reason.all.map .denied ++ Reason.all.map .deniedAtDispatch

def rid : RequestId := ⟨"s1", "c1", 0⟩

/-- A rejected verdict for every reason, then one verdict of each other shape the envelope reads. -/
def verdicts : List (String × Verdict) :=
  Reason.all.map (fun r => (s!"rejected/{r.code}", .rejected r)) ++
  [ ("denied/permission_missing", .ok (.denied .permissionMissing) none)
  , ("dispatch_denied/authorization_expired", .ok (.dispatchDenied .authorizationExpired) none)
  , ("needs_approval", .ok (.needsApproval rid) none)
  , ("allowed", .ok .allowed none)
  , ("allowed/would_deny", .ok .allowed (some (.wouldDeny .guardFalse)))
  , ("allowed/would_need_approval", .ok .allowed (some .wouldNeedApproval))
  , ("allowed_by_grant", .ok (.allowedByGrant "g1") none)
  , ("pending", .ok .pending none)
  , ("authorized", .ok .authorized none)
  , ("dispatch_claimed", .ok .dispatchClaimed none)
  , ("existing/denied", .ok (.existing (.denied .killed)) none)
  , ("overrun", .ok (.overrun ["usd_day"]) none)
  , ("accepted", .ok .none none) ]

def statusId (s : CallStatus) : String :=
  match s.reason? with
  | some r => s!"status/{s.code}/{r.code}"
  | none => s!"status/{s.code}"

def line (id : String) (input : Array (String × Json)) : String :=
  let output := Api.profile (Json.obj (#[("profile", .str Profile.McpToolApproval.id)] ++ input)).compact
  let out := (Json.parse output).toOption.getD (.str output)
  (Json.obj #[("id", .str id),
    ("input", .obj (#[("profile", .str Profile.McpToolApproval.id)] ++ input)),
    ("output", out)]).compact

/-- `corpus/profiles/mcp-tool-approval-v1.jsonl`, as the profile gives it through `Writ.Api.profile`.
Verdicts are written as the kernel writes them, at state version 7. -/
def text : String :=
  let ls := (statuses.map fun s => line (statusId s) #[("status", toJson s)]) ++
    (verdicts.map fun (p : String × Verdict) => line s!"verdict/{p.1}" #[("verdict", Verdict.toJsonWith p.2 7)])
  String.join (ls.map (· ++ "\n"))

end WritTests.ProfileVectors
