"""The gate walk-through in README.md (Run a gate): a free call, then a call that needs approval and spends money."""

import json
import uuid

from writ import Cost, MemoryStore, call_digest, create_gate, load_kernel

policy_text = json.dumps({
    "writ": "0.1",
    "approver_roles": ["owner"],
    "meters": {"spend": {"currency": "USD", "cap": 5000, "scope": "principal", "window_ms": 86_400_000}},
    "actions": {"shop.search": {"consent": "none"}, "shop.buy": {"consent": "per_call", "meters": ["spend"]}},
})
gate = create_gate(kernel=load_kernel(), policy_text=policy_text, store=MemoryStore())
session_id = str(uuid.uuid4())

gate.start(
    session_id,
    requester="user:alice",            # the principal the session acts for
    permissions=[],
    approvers={"alice-laptop": {"principal": "user:alice", "kind": "human", "roles": ["owner"]}},
    user_initiated=True,               # also starts the first turn
)
gate.step_start(session_id)            # one per model response

# A free call: propose, dispatch, run, report.
search_digest = call_digest({"server": "shop", "tool": "shop.search", "tool_digest": "sha256:tool-v1",
                             "args": {"q": "tea"}})
p1 = gate.propose(session_id, call_id="c1", tool="shop.search", call_digest=search_digest)
if p1.kind == "allowed":
    d = gate.dispatch(session_id, call_id="c1", call_digest=search_digest)
    if d.claimed:
        # run the tool now, then report what happened
        gate.result(session_id, call_id="c1", outcome="succeeded")

# A call that needs approval and spends money.
cost: Cost = {"amount": "1999", "currency": "USD"}  # 19.99 USD
buy_digest = call_digest({"server": "shop", "tool": "shop.buy", "tool_digest": "sha256:tool-v1",
                          "args": {"sku": "tea-100", "qty": 2}, "cost": cost})
p2 = gate.propose(session_id, call_id="c2", tool="shop.buy", call_digest=buy_digest, cost=cost)
if p2.kind == "needs_approval":
    assert p2.request_id is not None   # always set for needs_approval
    # show the call to the approver in a trusted renderer, then:
    gate.approve(session_id, call_id="c2", request_id=p2.request_id, approver_id="alice-laptop",
                 reviewed_digest=buy_digest, reviewed_cost=cost)
    d = gate.dispatch(session_id, call_id="c2", call_digest=buy_digest, cost=cost)
    if d.claimed:
        # run the tool, then report what it actually charged
        gate.result(session_id, call_id="c2", outcome="succeeded", actual_cost="1999")

view = gate.inspect(session_id)
assert view is not None
for c in view.calls:
    print(f"{c.call_id} {c.tool}: {c.status}")
for m in view.meters:
    print(f"meter {m.meter}: used {m.used} of {m.cap}")
