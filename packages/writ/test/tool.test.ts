import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"
import { test } from "node:test"
import { repoRoot } from "./helpers.js"
import { toolDigest, toolPreimage, WritInputError } from "../src/index.js"

interface Vector {
  id: string
  tool_text: string
  canonical?: string
  digest?: string
  error_contains?: string
}

const vectors = readFileSync(join(repoRoot, "corpus/digests/tool-v1.jsonl"), "utf8")
  .split("\n").filter((l) => l !== "").map((l) => JSON.parse(l) as Vector)

const firstTool = (text: string): unknown => {
  const doc = JSON.parse(text) as unknown
  const list = Array.isArray(doc) ? doc : (doc as { tools?: unknown }).tools
  return Array.isArray(list) ? list[0] : doc
}

// toolDigest takes one parsed tool, so it cannot see duplicate keys (JSON.parse keeps the last) or problems of the list around the tool.
const listOrTextOnly = new Set(["err-duplicate-key", "err-duplicate-tool-name", "err-not-a-list"])

test("the tool vectors cover what the brief lists", () => {
  const ids = new Set(vectors.map((v) => v.id))
  for (const id of ["num-0.5", "num-1.5e3", "num-neg-zero", "num-1E-7", "num-100", "num-2.0", "tools-list-next-cursor",
    "annotations-present", "annotations-absent", "err-16-digits", "err-1e400", "err-duplicate-key", "err-missing-name"]) {
    assert.ok(ids.has(id), id)
  }
})

for (const v of vectors) {
  if (v.error_contains !== undefined) {
    if (listOrTextOnly.has(v.id)) continue
    test(`tool vector ${v.id} is refused`, async () => {
      const tool = firstTool(v.tool_text)
      await assert.rejects(async () => toolDigest(tool), (e: unknown) => {
        assert.ok(e instanceof WritInputError, String(e))
        assert.ok(e.message.includes(v.error_contains!), e.message)
        return true
      })
    })
  } else {
    test(`tool vector ${v.id}`, async () => {
      const tool = firstTool(v.tool_text)
      assert.equal(toolPreimage(tool), v.canonical)
      assert.equal(await toolDigest(tool), v.digest)
    })
  }
}

test("reordered keys and whitespace give the same digest; a dropped annotation does not", () => {
  const by = (id: string) => vectors.find((v) => v.id === id)!.digest
  assert.equal(by("annotations-present"), by("annotations-reordered"))
  assert.notEqual(by("annotations-present"), by("annotations-absent"))
  assert.equal(by("tools-list-next-cursor"), by("tools-list-meta"))
  assert.equal(by("tools-list-next-cursor"), by("tools-list-unknown-key"))
})

test("toolDigest refuses values JSON cannot carry and numbers it cannot print exactly", async () => {
  for (const [tool, path] of [[{ name: "t", n: Number.NaN }, "n"], [{ name: "t", n: [Infinity] }, "n[0]"],
    [{ name: "t", n: 0.1 + 0.2 }, "n"], [{ name: "t", n: 2 ** 60 }, "n"], [{ name: "t", s: "\ud800" }, "s"]] as const) {
    await assert.rejects(toolDigest(tool), (e: unknown) => e instanceof WritInputError && e.path === path)
  }
  for (const bad of [null, [], "x", 5]) await assert.rejects(toolDigest(bad), WritInputError)
  await assert.rejects(toolDigest({ name: "t", n: 1.234567890123456e301 }), /more than 15 significant digits/)
  assert.equal(toolPreimage({ name: "t", n: 1e20, z: -0 }), '{"t":"writ.tool.v1","tool":{"n":100000000000000000000,"name":"t","z":0}}')
})
