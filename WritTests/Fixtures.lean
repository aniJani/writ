import WritTests.Harness

open Writ

def alice : ApproverInfo := ⟨"alice", .human, ["owner"]⟩
def bob : ApproverInfo := ⟨"bob", .human, ["admin"]⟩
def bot : ApproverInfo := ⟨"reviewer-bot", .automated, ["admin"]⟩

def start (perms : List String) (approvers : List (String × ApproverInfo))
    (ledger : Ledger := {}) : EventBody :=
  .sessionStart "s1" "pd" "u1" perms approvers ledger
