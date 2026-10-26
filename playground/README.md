# Writ playground

A static page that runs the Writ policy kernel in your browser. There is no model, no server logic and no API key: you play the agent, the approver and the tool. Write a policy, check it, send events from small forms (or as raw JSON), and see each verdict and the session state. A scenario picker plays the conformance traces in `corpus/examples` event by event and marks whether each verdict matches the trace's `expect`.

It runs the same kernel as `@anijani/writ`: the page loads the package's compiled `dist/src` and `wasm/writ.wasm` and calls `loadKernel`, `check`, `step` and `inspect` exactly as a host would. Nothing you type leaves the browser; the server only hands out static files.

## Run it

From the repository root:

```sh
cd packages/writ && npm run build && cd ../..
node playground/build.mjs
node playground/serve.mjs
```

Then open http://localhost:8787. `build.mjs` assembles `playground/site/` (the page, the package's `dist/src` with its source maps, the WebAssembly kernel and the corpus traces) and refuses to run when the package is not built or the WebAssembly build is stale. `serve.mjs` serves that folder on the loopback interface only, with `.wasm` as `application/wasm`; `node playground/serve.mjs --check` starts it on a free port, fetches the files the page needs, prints what came back and exits. Opening `index.html` from disk does not work, because browsers refuse module and WebAssembly loads from `file://`; the page says so.

The page is for local use. Do not deploy it.

## Try this

1. Press **Check** on the sample policy (`web_search` free, `send_email` needs one approval and spends from a `spend` meter capped at 5000).
2. **Start session**, **Start turn**, **Start step**, then **Propose** the prefilled `send_email`: the kernel answers `needs_approval`.
3. Pick the call and **Approve**, **Dispatch** (`dispatch_claimed`), then **Report result**. The meter shows 25 used.
4. Propose again, approve, and dispatch with other arguments in the dispatch box: the kernel refuses with `digest_mismatch`, because the approval covers only the call that was shown.
5. Load the `langgraph-resume/argument-swap` scenario and press **Step** or **Run to end**.

The forms fill in `seq`, `time` (one second after the last accepted event) and `state_version`. A raw event may set them itself, for example to see `stale_seq`, and a raw `session_start` without `policy_digest` gets the checked policy's digest. A policy that fails `writ check`, malformed JSON or a rejected event is shown in the verdict panel and leaves the session as it was.

## Files

- `engine.js`: all the logic (sessions, event forms, scenario playback, load errors). It imports the package from `../packages/writ/dist/src/index.js`; `build.mjs` rewrites that one import for `site/`.
- `app.js`: wires the page to the engine.
- `index.html`, `style.css`: the page, with light and dark color schemes.
- `test/engine.test.mjs`: the engine against the real kernel (`npm test`, after building `packages/writ`).
