import { spawnSync } from "node:child_process"
import { copyFileSync, existsSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const repo = join(here, "..")
const site = join(here, "site")
const dist = join(repo, "packages/writ/dist/src")
const wasm = join(repo, "packages/writ/wasm")
const corpus = join(repo, "corpus/examples")

function fail(message) {
  console.error(`playground build: ${message}`)
  process.exit(1)
}

if (!existsSync(join(dist, "index.js"))) fail("packages/writ/dist is missing: run cd packages/writ && npm run build")
const newestSource = readdirSync(join(repo, "packages/writ/src"), { recursive: true })
  .map((f) => statSync(join(repo, "packages/writ/src", f)).mtimeMs)
  .reduce((a, b) => Math.max(a, b), 0)
if (newestSource > statSync(join(dist, "index.js")).mtimeMs) {
  fail("packages/writ/dist is older than its sources: run npm run build in packages/writ")
}
for (const f of ["writ.mjs", "writ.wasm"]) {
  if (!existsSync(join(wasm, f))) fail(`packages/writ/wasm/${f} is missing: run scripts/build-wasm.sh`)
}
const stamp = spawnSync(process.execPath, [join(repo, "packages/writ/scripts/check-wasm.mjs")], { stdio: "inherit" })
if (stamp.status !== 0) fail("the WebAssembly stamp check failed (see above)")

rmSync(site, { recursive: true, force: true })
mkdirSync(join(site, "dist/src"), { recursive: true })
mkdirSync(join(site, "wasm"))
mkdirSync(join(site, "scenarios"))

for (const f of ["index.html", "style.css", "app.js"]) copyFileSync(join(here, f), join(site, f))

// In the repository engine.js reaches the package two levels up; in site/ the package's dist/ sits beside it.
const FROM = '"../packages/writ/dist/src/index.js"'
const engine = readFileSync(join(here, "engine.js"), "utf8")
if (engine.split(FROM).length !== 2) fail(`engine.js must import ${FROM} exactly once`)
writeFileSync(join(site, "engine.js"), engine.replace(FROM, '"./dist/src/index.js"'))

const modules = readdirSync(dist).filter((f) => f.endsWith(".js"))
for (const f of modules) {
  if (!existsSync(join(dist, f + ".map"))) fail(`packages/writ/dist/src/${f}.map is missing: run npm run build in packages/writ`)
  copyFileSync(join(dist, f), join(site, "dist/src", f))
  copyFileSync(join(dist, f + ".map"), join(site, "dist/src", f + ".map"))
}
for (const f of ["writ.mjs", "writ.wasm"]) copyFileSync(join(wasm, f), join(site, "wasm", f))

const traces = readdirSync(corpus).filter((f) => f.endsWith(".jsonl")).sort()
for (const f of traces) copyFileSync(join(corpus, f), join(site, "scenarios", f))
writeFileSync(join(site, "scenarios/index.json"), JSON.stringify(traces) + "\n")

console.log(`built playground/site: 4 page files, ${modules.length} kernel modules with their source maps, the WebAssembly kernel, ${traces.length} scenario files`)
console.log("serve it with: node playground/serve.mjs")
