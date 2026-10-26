import assert from "node:assert/strict"
import { test } from "node:test"
import { MAX_INPUT_BYTES, MAX_SEALED_CHARS, open, seal, WritInputError } from "../src/index.js"

const subtle = globalThis.crypto.subtle
const newKey = (hash = "SHA-256") => subtle.generateKey({ name: "HMAC", hash }, false, ["sign", "verify"])
const state = '{"schema":"writ.state/1","note":"café 😀"}'

function flip(sealed: string, part: 0 | 1): string {
  const parts = sealed.split(".")
  const s = parts[part]!
  // Change the first character, which carries full bits in base64url.
  parts[part] = (s[0] === "A" ? "B" : "A") + s.slice(1)
  return parts.join(".")
}

test("seal then open gives the state back", async () => {
  const key = await newKey()
  const sealed = await seal(state, key)
  assert.match(sealed, /^[A-Za-z0-9_-]{43}\.[A-Za-z0-9_-]+$/)
  assert.equal(await open(sealed, key), state)
  assert.equal(await open(await seal("", key), key), "")
})

test("the body is base64url of the UTF-8 state", async () => {
  const key = await newKey()
  const body = (await seal(state, key)).split(".")[1]!
  const bytes = Uint8Array.from(atob(body.replace(/-/g, "+").replace(/_/g, "/")), (c) => c.charCodeAt(0))
  assert.equal(new TextDecoder().decode(bytes), state)
})

test("a tampered state throws", async () => {
  const key = await newKey()
  await assert.rejects(open(flip(await seal(state, key), 1), key), WritInputError)
})

test("a tampered MAC throws", async () => {
  const key = await newKey()
  await assert.rejects(open(flip(await seal(state, key), 0), key), WritInputError)
})

test("a wrong key throws", async () => {
  const sealed = await seal(state, await newKey())
  await assert.rejects(open(sealed, await newKey()), WritInputError)
})

test("malformed sealed text throws", async () => {
  const key = await newKey()
  const sealed = await seal(state, key)
  const [mac, body] = sealed.split(".") as [string, string]
  for (const bad of ["", mac, `${mac}.${body}.x`, `${mac}=.${body}`, `${mac}.${body}+`, `${mac.slice(1)}.${body}`, `${mac}.${body}A`]) {
    await assert.rejects(open(bad, key), WritInputError, bad)
  }
})

test("seal refuses a lone surrogate and a key that is not HMAC SHA-256", async () => {
  await assert.rejects(seal("\ud800", await newKey()), WritInputError)
  await assert.rejects(seal(state, await newKey("SHA-1")), WritInputError)
  await assert.rejects(open(await seal(state, await newKey()), await newKey("SHA-512")), WritInputError)
})

test("open refuses oversize input before any work", async () => {
  const key = await newKey()
  const big = `${"A".repeat(43)}.${"A".repeat(MAX_SEALED_CHARS - 43)}`
  const start = performance.now()
  await assert.rejects(open(big, key), WritInputError)
  assert.ok(performance.now() - start < 50, "returns in under 50 ms")
})

test("open checks the MAC length first", async () => {
  const key = await newKey()
  const body = (await seal(state, key)).split(".")[1]!
  await assert.rejects(open(`${"!".repeat(42)}.${body}`, key), /sealed MAC has the wrong length/)
})

test("open refuses a stale state", async () => {
  const key = await newKey()
  const text = '{"schema":"writ.state/1","session_id":"s1","state_version":3}'
  const blob = await seal(text, key)
  await assert.rejects(open(blob, key, { sessionId: "s1", stateVersion: 5 }), (e: unknown) => {
    assert.ok(e instanceof WritInputError)
    assert.match(e.message, /3/)
    assert.match(e.message, /5/)
    return true
  })
  assert.equal(await open(blob, key, { sessionId: "s1", stateVersion: 3 }), text)
  await assert.rejects(open(blob, key, { sessionId: "s2", stateVersion: 3 }), WritInputError)
})

test("open takes a null expect as absent and refuses one that is not an object", async () => {
  const key = await newKey()
  const blob = await seal(state, key)
  assert.equal(await open(blob, key, null as never), state)
  for (const bad of [5, "s1", true, ["s1", 3]]) {
    await assert.rejects(open(blob, key, bad as never), (e: unknown) => e instanceof WritInputError && e.path === "expect", String(bad))
  }
})

test("a state of MAX_INPUT_BYTES seals to at most MAX_SEALED_CHARS and opens; one byte more is refused", async () => {
  const key = await newKey()
  const text = "a".repeat(MAX_INPUT_BYTES)
  const sealed = await seal(text, key)
  assert.ok(sealed.length <= MAX_SEALED_CHARS)
  assert.equal(await open(sealed, key), text)
  await assert.rejects(seal(text + "a", key), WritInputError)
})
