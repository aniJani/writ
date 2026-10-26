import { createReadStream, existsSync, statSync } from "node:fs"
import { createServer } from "node:http"
import { dirname, extname, join, normalize, sep } from "node:path"
import { fileURLToPath } from "node:url"

const root = join(dirname(fileURLToPath(import.meta.url)), "site")

const TYPES = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".map": "application/json; charset=utf-8",
  ".jsonl": "text/plain; charset=utf-8",
  ".wasm": "application/wasm",
}

function resolve(urlPath) {
  let path
  try {
    path = decodeURIComponent(urlPath.split("?")[0])
  } catch {
    return null
  }
  if (path.endsWith("/")) path += "index.html"
  const file = normalize(join(root, path))
  if (file !== root && !file.startsWith(root + sep)) return null
  return existsSync(file) && statSync(file).isFile() ? file : null
}

export function playgroundServer() {
  return createServer((req, res) => {
    const file = req.method === "GET" || req.method === "HEAD" ? resolve(req.url ?? "/") : null
    if (file === null) {
      res.writeHead(404, { "content-type": "text/plain; charset=utf-8" })
      res.end("not found\n")
      return
    }
    res.writeHead(200, {
      "content-type": TYPES[extname(file)] ?? "application/octet-stream",
      "cache-control": "no-store",
      "x-content-type-options": "nosniff",
    })
    if (req.method === "HEAD") res.end()
    else createReadStream(file).on("error", () => res.destroy()).pipe(res)
  })
}

async function check() {
  const server = playgroundServer()
  await new Promise((ok) => server.listen(0, "127.0.0.1", ok))
  const base = `http://127.0.0.1:${server.address().port}`
  const want = [
    ["/", "text/html"],
    ["/style.css", "text/css"],
    ["/app.js", "text/javascript"],
    ["/engine.js", "text/javascript"],
    ["/dist/src/index.js", "text/javascript"],
    ["/dist/src/kernel.js", "text/javascript"],
    ["/dist/src/index.js.map", "application/json"],
    ["/wasm/writ.mjs", "text/javascript"],
    ["/wasm/writ.wasm", "application/wasm"],
    ["/scenarios/index.json", "application/json"],
    ["/scenarios/langgraph-resume.jsonl", "text/plain"],
  ]
  let bad = 0
  try {
    for (const [path, type] of want) {
      const res = await fetch(base + path)
      const got = res.headers.get("content-type") ?? ""
      const bytes = (await res.arrayBuffer()).byteLength
      const ok = res.status === 200 && got.startsWith(type) && bytes > 0
      if (!ok) bad++
      console.log(`${ok ? "ok  " : "FAIL"} ${path} ${res.status} ${got} ${bytes} bytes`)
    }
    const escape = await fetch(base + "/..%2fpackage.json")
    if (escape.status !== 404) bad++
    console.log(`${escape.status === 404 ? "ok  " : "FAIL"} /..%2fpackage.json ${escape.status} (outside site/)`)
  } finally {
    server.close()
  }
  process.exitCode = bad === 0 ? 0 : 1
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  if (!existsSync(join(root, "index.html"))) {
    console.error("playground/site is missing: run node playground/build.mjs first")
    process.exit(1)
  }
  if (process.argv.includes("--check")) {
    await check()
  } else {
    const port = Number(process.env.PORT ?? 8787)
    // Bound to the loopback interface only: the playground is for local use.
    playgroundServer().listen(port, "127.0.0.1", () => {
      console.log(`Writ playground at http://localhost:${port} (Ctrl-C to stop)`)
    })
  }
}
