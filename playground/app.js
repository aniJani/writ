import * as engine from "./engine.js"

const $ = (id) => document.getElementById(id)

let kernel = null
let session = null
let player = null
let scenarios = []

function el(tag, attrs = {}, ...children) {
  const node = document.createElement(tag)
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") node.className = v
    else node.setAttribute(k, v)
  }
  for (const c of children) if (c !== null && c !== undefined) node.append(c)
  return node
}

const json = (v) => JSON.stringify(v, null, 2)

function setStatus(text, kind) {
  const s = $("load-status")
  s.textContent = text
  s.className = `status ${kind}`
}

function showFailure(code, message, event = null) {
  $("verdict-out").replaceChildren(el("dl", { class: "verdict" },
    el("dt", {}, "error"), el("dd", {}, el("span", { class: "badge failure" }, code)),
    el("dt", {}, "message"), el("dd", { class: "message" }, message),
    el("dt", {}, "session"), el("dd", { class: "message" }, "unchanged"),
  ))
  $("event-json").textContent = event === null ? "" : json(event)
  $("verdict-json").textContent = ""
}

function showVerdict(event, verdict) {
  const rows = [["verdict", el("span", { class: `badge ${verdict.verdict}` }, verdict.verdict)]]
  if (verdict.decision !== undefined) rows.push(["decision", verdict.decision])
  if (verdict.reason !== undefined) rows.push(["reason", verdict.reason])
  if (verdict.request_id !== undefined) rows.push(["request_id", JSON.stringify(verdict.request_id)])
  if (verdict.grant !== undefined) rows.push(["grant", verdict.grant])
  if (verdict.status !== undefined) rows.push(["status", JSON.stringify(verdict.status)])
  if (verdict.meters !== undefined) rows.push(["meters", verdict.meters.join(", ")])
  if (verdict.would_deny !== undefined) rows.push(["would_deny", verdict.would_deny])
  if (verdict.would_need_approval !== undefined) rows.push(["would_need_approval", "true"])
  if (verdict.retry !== undefined) rows.push(["retry", verdict.retry])
  rows.push(["state_version", String(verdict.state_version)])
  const dl = el("dl", { class: "verdict" })
  for (const [k, v] of rows) dl.append(el("dt", {}, k), el("dd", {}, v))
  if (verdict.message !== undefined) dl.append(el("dt", {}, "message"), el("dd", { class: "message" }, verdict.message))
  $("verdict-out").replaceChildren(dl)
  $("event-json").textContent = json(event)
  $("verdict-json").textContent = json(verdict)
}

function statusText(status) {
  return typeof status === "string" ? status : `${status.status} (${status.reason})`
}

function table(caption, head, rows) {
  if (rows.length === 0) return el("p", { class: "note" }, `${caption}: none`)
  return el("div", { class: "table-wrap" }, el("table", {},
    el("caption", {}, caption),
    el("thead", {}, el("tr", {}, ...head.map((h) => el("th", { scope: "col" }, h)))),
    el("tbody", {}, ...rows.map((r) => el("tr", {}, ...r.map((c) => el("td", {}, c))))),
  ))
}

function showState(view) {
  const flag = (name, on) => el("li", { class: on ? "on" : "" }, `${name}: ${on}`)
  $("state-out").replaceChildren(
    el("ul", { class: "flags", "aria-label": "Session flags" },
      el("li", {}, `session: ${view.session_id || "(not started)"}`),
      el("li", {}, `state_version: ${view.state_version}`),
      el("li", {}, `started: ${view.started}`),
      flag("ended", view.ended),
      flag("killed", view.killed),
      flag("escalated", view.escalated),
      el("li", {}, `escalations: ${view.escalations}`),
    ),
    table("Calls", ["call", "tool", "status", "attempts", "gen", "cost"], view.calls.map((c) => [
      c.call_id, c.tool, statusText(c.status), String(c.attempts), String(c.generation),
      c.cost === null ? "" : `${c.cost.amount} ${c.cost.currency}`,
    ])),
    table("Meters", ["meter", "scope", "used", "cap", "remaining"], view.meters.map((m) => [
      m.meter, m.scope, m.used, m.cap ?? "none", m.remaining ?? "",
    ])),
    view.blocked_tools.length === 0 ? "" : el("p", { class: "note" }, `Blocked tools: ${view.blocked_tools.join(", ")}`),
  )
}

function refreshCalls(view) {
  const select = $("call-select")
  const keep = select.value
  const options = view.calls.map((c) => el("option", { value: c.call_id }, `${c.call_id} ${c.tool} (${statusText(c.status)})`))
  select.replaceChildren(...(options.length > 0 ? options : [el("option", { value: "" }, "no calls yet")]))
  if (view.calls.some((c) => c.call_id === keep)) select.value = keep
  else if (view.calls.length > 0) select.value = view.calls.at(-1).call_id
}

function addHistory(event, verdict) {
  $("history").append(el("li", { class: verdict.verdict },
    `${engine.eventLine(event)} -> ${engine.verdictLine(verdict)}`))
}

function showResult(r) {
  if (!r.ok) {
    showFailure(r.error.code, r.error.message, r.event)
    return
  }
  showVerdict(r.event, r.verdict)
  showState(r.view)
  refreshCalls(r.view)
  addHistory(r.event, r.verdict)
  $("call-id").value = session.nextCallId()
}

function formFor(type) {
  return {
    sessionId: $("session-id").value,
    permissions: $("permissions").value,
    userInitiated: $("user-initiated").checked,
    callId: type === "propose" ? $("call-id").value : $("call-select").value,
    tool: $("tool").value,
    args: type === "dispatch" ? $("dispatch-args").value : $("args").value,
    costAmount: $("cost").value,
    costCurrency: $("currency").value,
    guards: $("guards").value,
    escalators: $("escalators").value,
    outcome: $("outcome").value,
    actualCost: $("actual-cost").value,
  }
}

function showCheck(made) {
  const items = []
  for (const e of made.errors ?? []) items.push(el("li", { class: "error" }, `error ${e.code}${e.action ? ` (${e.action})` : ""}: ${e.message}`))
  for (const w of made.warnings ?? []) items.push(el("li", { class: "warning" }, `warning ${w.code}${w.action ? ` (${w.action})` : ""}: ${w.message}`))
  if (made.ok) items.unshift(el("li", { class: "ok" }, `ok, policy digest ${made.session.policyDigest}`))
  $("check-out").replaceChildren(el("ul", { class: "findings" }, ...items))
}

function onCheck() {
  const made = engine.createPlayground(kernel, $("policy").value)
  showCheck(made)
  if (!made.ok) {
    if (session !== null) $("check-out").append(el("p", { class: "note" }, "The running session keeps its earlier policy."))
    return
  }
  session = made.session
  player = null
  $("scenario-steps").replaceChildren()
  $("scenario-desc").textContent = ""
  updateScenarioButtons()
  $("session-panel").hidden = false
  $("tools").replaceChildren(...engine.actionNames(session.policyText).map((n) => el("option", { value: n })))
  $("history").replaceChildren()
  $("call-id").value = session.nextCallId()
  showState(session.view)
  refreshCalls(session.view)
  $("verdict-out").replaceChildren(el("p", { class: "note" }, "New session. Start with Start session."))
  $("event-json").textContent = ""
  $("verdict-json").textContent = ""
}

async function loadScenarios() {
  const select = $("scenario-select")
  try {
    const res = await fetch("scenarios/index.json")
    if (!res.ok) throw new Error(`scenarios/index.json: ${res.status}`)
    const files = await res.json()
    const groups = []
    for (const file of files) {
      const r = await fetch(`scenarios/${file}`)
      if (!r.ok) throw new Error(`scenarios/${file}: ${r.status}`)
      const list = engine.parseScenarios(await r.text())
      const group = el("optgroup", { label: file })
      for (const s of list) {
        group.append(el("option", { value: String(scenarios.length) }, s.id))
        scenarios.push(s)
      }
      groups.push(group)
    }
    select.replaceChildren(...groups)
    const swap = scenarios.findIndex((s) => s.id === "langgraph-resume/argument-swap")
    if (swap >= 0) select.value = String(swap)
    select.disabled = false
    $("scenario-load").disabled = false
  } catch (e) {
    select.replaceChildren(el("option", { value: "" }, "no scenarios"))
    $("scenario-desc").textContent = `Scenarios did not load: ${e.message}`
  }
}

function updateScenarioButtons() {
  const live = player !== null && !player.done
  $("scenario-step").disabled = !live
  $("scenario-run").disabled = !live
}

function scenarioRow(i, row) {
  const li = $("scenario-steps").children[i]
  li.className = row.matches ? "match" : "miss"
  const badge = el("span", { class: `badge ${row.matches ? "match" : "miss"}` }, row.matches ? "matches expect" : "differs from expect")
  li.replaceChildren(
    `${engine.eventLine(row.event)} -> ${row.error ? row.error.message : engine.verdictLine(row.verdict)} `, badge,
    row.matches ? "" : el("span", { class: "detail" }, `expect ${JSON.stringify(row.expect)}`),
  )
}

function onScenarioLoad() {
  const scenario = scenarios[Number($("scenario-select").value)]
  if (scenario === undefined) return
  player = engine.scenarioPlayer(kernel, scenario)
  session = null
  $("session-panel").hidden = true
  $("policy").value = json(scenario.policy) + "\n"
  $("check-out").replaceChildren(el("p", { class: "note" }, `Policy of ${scenario.id}. Press Check to play it by hand.`))
  $("scenario-desc").textContent = scenario.description
  $("scenario-steps").replaceChildren(...scenario.events.map(({ event, expect }) =>
    el("li", { class: "pending" }, `${engine.eventLine(event)} (expect ${engine.verdictLine(expect)})`)))
  $("history").replaceChildren()
  showState(player.view)
  $("verdict-out").replaceChildren(el("p", { class: "note" }, `Loaded ${scenario.id}, ${scenario.events.length} events. Press Step.`))
  $("event-json").textContent = ""
  $("verdict-json").textContent = ""
  updateScenarioButtons()
}

function stepScenario() {
  const i = player.rows.length
  const row = player.next()
  if (row === null) return
  scenarioRow(i, row)
  for (const li of $("scenario-steps").children) li.classList.remove("current")
  $("scenario-steps").children[i].classList.add("current")
  if (row.verdict === null) showFailure(row.error.code, row.error.message, row.event)
  else {
    showVerdict(row.event, row.verdict)
    addHistory(row.event, row.verdict)
  }
  showState(player.view)
  updateScenarioButtons()
}

function guard(fn) {
  return async (...args) => {
    try {
      await fn(...args)
    } catch (e) {
      showFailure("page_error", e instanceof Error ? e.message : String(e))
    }
  }
}

async function main() {
  $("policy").value = engine.SAMPLE_POLICY
  const boot = await engine.bootKernel()
  if (!boot.ok) {
    setStatus(boot.message, "error")
    return
  }
  kernel = boot.kernel
  setStatus(`Kernel loaded in this tab: ${kernel.version()}.`, "ready")
  $("check").disabled = false
  $("check").addEventListener("click", guard(onCheck))
  $("sample").addEventListener("click", () => { $("policy").value = engine.SAMPLE_POLICY })
  for (const button of document.querySelectorAll("[data-event]")) {
    button.addEventListener("click", guard(async () => {
      const type = button.dataset.event
      showResult(await session.send(type, formFor(type)))
    }))
  }
  $("send-raw").addEventListener("click", guard(() => showResult(session.apply($("raw").value))))
  $("scenario-load").addEventListener("click", guard(onScenarioLoad))
  $("scenario-step").addEventListener("click", guard(stepScenario))
  $("scenario-run").addEventListener("click", guard(() => { while (player !== null && !player.done) stepScenario() }))
  await loadScenarios()
}

main().catch((e) => setStatus(`${engine.SERVE_HINT}. ${e instanceof Error ? e.message : String(e)}`, "error"))
