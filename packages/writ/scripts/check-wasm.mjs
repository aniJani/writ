import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const path = (rel) => fileURLToPath(new URL(rel, import.meta.url));

for (const f of ["writ.mjs", "writ.wasm"]) {
  if (!existsSync(path(`../wasm/${f}`))) {
    console.error(`packages/writ/wasm/${f} is missing: run scripts/build-wasm.sh from the repository root first`);
    process.exit(1);
  }
}

// Outside the repository there are no sources to compare with.
const hashScript = path("../../../scripts/wasm-source-hash.sh");
if (existsSync(hashScript)) {
  let tree;
  try {
    tree = execFileSync(hashScript, { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }).trim();
  } catch (e) {
    const why = (e.stderr?.toString().trim() || e.message).replace(/\s+/g, " ");
    console.error(`could not hash the WASM sources: ${why}; run scripts/build-wasm.sh from the repository root`);
    process.exit(1);
  }
  if (!/^sha256:[0-9a-f]{64}$/.test(tree)) {
    console.error(`could not hash the WASM sources: unexpected output ${JSON.stringify(tree)}; run scripts/build-wasm.sh from the repository root`);
    process.exit(1);
  }
  const stampFile = path("../wasm/writ.source");
  const stamp = existsSync(stampFile) ? readFileSync(stampFile, "utf8").trim() : "";
  if (stamp !== tree) {
    console.error(
      `packages/writ/wasm is stale (built from ${stamp || "unknown sources"}, tree is ${tree}): run scripts/build-wasm.sh from the repository root`,
    );
    process.exit(1);
  }
}
