import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { existsSync, readdirSync, readFileSync } from "node:fs"
import { join } from "node:path"
import { test } from "node:test"
import { fixture, nativeWrit, repoRoot } from "./helpers.js"
import { loadKernel } from "../src/index.js"

const kernel = await loadKernel()
const dir = join(repoRoot, "corpus/examples")
const files = readdirSync(dir).filter((f) => f.endsWith(".jsonl")).sort()

function expectedIds(file: string): string[] {
  if (existsSync(nativeWrit)) {
    const r = spawnSync(nativeWrit, ["replay", join(dir, file)], { encoding: "utf8" })
    assert.equal(r.status, 0, r.stderr)
    return r.stdout.split("\n").filter((l) => l.startsWith("ok ")).map((l) => l.slice(3))
  }
  const prefix = file.replace(/\.jsonl$/, "") + "/"
  return fixture("replay-corpus.out").split("\n").filter((l) => l.startsWith(`ok ${prefix}`)).map((l) => l.slice(3))
}

for (const file of files) {
  test(`replay of corpus/examples/${file}`, () => {
    const result = kernel.replay(readFileSync(join(dir, file), "utf8"))
    const want = expectedIds(file)
    assert.ok(want.length > 0)
    assert.deepEqual(result.traces.map((t) => t.id), want)
    for (const t of result.traces) assert.deepEqual([t.ok, t.mismatches], [true, []], t.id)
  })
}
