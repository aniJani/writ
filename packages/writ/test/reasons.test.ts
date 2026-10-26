import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"
import { test } from "node:test"
import { repoRoot } from "./helpers.js"
import { REASONS, RETRY_CLASSES } from "../src/index.js"

const contract = JSON.parse(readFileSync(join(repoRoot, "schema/reasons.json"), "utf8")) as { code: string; retry: string }[]

test("REASONS matches schema/reasons.json in order", () => {
  assert.deepEqual([...REASONS], contract.map((r) => r.code))
})

test("RETRY_CLASSES holds exactly the retry classes in schema/reasons.json", () => {
  assert.deepEqual([...RETRY_CLASSES].sort(), [...new Set(contract.map((r) => r.retry))].sort())
  assert.equal(new Set(RETRY_CLASSES).size, RETRY_CLASSES.length)
})
