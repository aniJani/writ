// Prints the import closure of a Lean module, one module name per line, by asking
// `lean --deps` for the imports of each module's source. Usage:
//   node build/wasm/closure.mjs <lean-binary> <toolchain-lib> <toolchain-src> <repo> <root-module>
import { execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import { join } from "node:path";

const [lean, tlib, tsrc, repo, root] = process.argv.slice(2);
const blib = join(repo, ".lake/build/lib/lean");
const env = { ...process.env, LEAN_PATH: `${tlib}:${blib}` };

function source(mod) {
  const rel = mod.split(".").join("/") + ".lean";
  for (const dir of [repo, tsrc]) {
    if (existsSync(join(dir, rel))) return join(dir, rel);
  }
  throw new Error(`no source for ${mod}`);
}

function moduleOf(olean) {
  for (const dir of [tlib, blib]) {
    if (olean.startsWith(dir + "/")) {
      return olean.slice(dir.length + 1, -".olean".length).split("/").join(".");
    }
  }
  throw new Error(`olean outside the search path: ${olean}`);
}

const seen = new Set([root]);
const queue = [root];
while (queue.length > 0) {
  const mod = queue.shift();
  const out = execFileSync(lean, ["--deps", source(mod)], { cwd: repo, env, encoding: "utf8" });
  for (const line of out.split("\n")) {
    if (line === "") continue;
    const dep = moduleOf(line.startsWith("/") ? line : join(repo, line));
    if (!seen.has(dep)) {
      seen.add(dep);
      queue.push(dep);
    }
  }
}
process.stdout.write([...seen].sort().join("\n") + "\n");
