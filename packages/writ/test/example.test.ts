import assert from "node:assert/strict"
import { execFileSync } from "node:child_process"
import { test } from "node:test"
import { fileURLToPath } from "node:url"

test("the shop example prints one line per verdict", () => {
  const script = fileURLToPath(new URL("../examples/shop-agent.js", import.meta.url))
  const out = execFileSync(process.execPath, [script], { encoding: "utf8" })
  assert.deepEqual(out.trimEnd().split("\n"), [
    "start: accepted",
    "step: accepted",
    "propose search: allowed",
    "dispatch search: accepted dispatch_claimed",
    "result search: accepted",
    "propose buy: needs_approval",
    "approve buy: accepted authorized",
    "dispatch buy: accepted dispatch_claimed",
    "result buy: accepted",
  ])
})

test("the hello example runs a free call and an approved call", () => {
  const script = fileURLToPath(new URL("../examples/hello.js", import.meta.url))
  const out = execFileSync(process.execPath, [script], { encoding: "utf8" })
  assert.deepEqual(out.trimEnd().split("\n"), [
    "search: { ran: true, value: '3 results' }",
    "ask: Email bob@example.com?",
    "email: { ran: true, value: 'sent' }",
  ])
})
