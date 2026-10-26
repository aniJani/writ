import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import type { Kernel, WritEvent } from "../src/index.js"

// dist/test/helpers.js -> packages/writ -> repository root
export const repoRoot = join(dirname(fileURLToPath(import.meta.url)), "../../../..")

export const fixture = (p: string): string => readFileSync(join(repoRoot, "tests/cli", p), "utf8")

export const nativeWrit = join(repoRoot, ".lake/build/bin/writ")

export function sessionRunner(kernel: Kernel): () => { verdicts: string[]; results: string[]; state: string } {
  const policy = fixture("policies/simple.json")
  // The fixture has one deliberately malformed line, which cannot be a typed event.
  const events = fixture("oracle-events.jsonl").split("\n").filter((l) => l !== "").flatMap((l) => {
    try { return [JSON.parse(l) as WritEvent] } catch { return [] }
  })
  return () => {
    let state = kernel.initial(policy).state
    const verdicts: string[] = []
    const results: string[] = []
    for (const e of events) {
      const r = kernel.step(policy, state, e)
      state = r.state
      verdicts.push(JSON.stringify(r.verdict))
      results.push(JSON.stringify(r))
    }
    return { verdicts, results, state }
  }
}
