# Digest vectors

## Call digest vectors

`call-v1.jsonl` holds test vectors for the `writ-call-v1/RFC8785-JCS+SHA-256` call digest (docs/design.md, section 6). Ports in other languages can test against it.

Each line is one JSON object:

- `id`: vector name.
- `input`: `server`, `tool`, `tool_digest`, and optionally `cost` (`{amount, currency}` or `null`) and arguments as either `args_text` or `args`. With neither, the arguments are missing and become `{}`.
  - `args_text` is raw text to run through a strict parser (duplicate keys, large integers, `-0`, lone surrogates and depth only show up in text).
  - `args` is a JSON value used as given.
- `canonical`: the expected preimage, the RFC 8785 canonical JSON of `{"t":"writ.call.v1","server":...,"tool":...,"tool_digest":...,"args":...,"cost":...}`. Keys sort by UTF-16 code unit, so `args` comes first.
- `digest`: `"sha256:"` plus the lowercase hex SHA-256 of the UTF-8 bytes of `canonical`.
- `error`: instead of `canonical` and `digest`, the input must be rejected. `error.path` is the JSON path of the offending value, `args.items[3].name` style, with `args` as the root. Paths for syntax errors are the path of the enclosing value. A lone surrogate in an object key is reported at the key's own path.

### Rules the vectors pin

- Numbers use ECMAScript `Number.prototype.toString`. Integers outside plus or minus (2^53 - 1) are rejected even where RFC 8785 would print them, so `1e21`, `1E30` and `9007199254740992` are errors. This follows the I-JSON rule in the spec. Fractions are fine.
- A number literal must have the same decimal value as its shortest round-trip form: its normalized sign, significant digits and exponent must equal those of `String(Number(text))`. This also rejects exact binary expansions such as `0.1000000000000000055511151231257827021181583404541015625`. So `9007199254740991.2`, `1.00000000000000001`, `2.5e-324` and `3.141592653589793238` are errors (carry such values as strings), while `4.50`, `1E2`, `19.99` and `0.30000000000000004` pass. Expected values for the new passing vectors are `String(x)` of the number, checked against ECMAScript.
- `-0` (any spelling), non-finite numbers (`1e400`), and numbers that underflow to zero (`1e-400`) are rejected.
- Duplicate keys are rejected after unescaping (`"a"` and `"a"` collide).
- Lone surrogates, raw or as `\ud800`-style escapes, are rejected in strings and keys.
- Nesting is limited to 128 levels counted from the arguments value, so `[` x 128 is accepted and x 129 is rejected.
- Only space, tab, line feed and carriage return are whitespace; trailing data, trailing commas, `NaN`, leading zeros, a leading `+` or `.`, single quotes and raw control characters in strings are rejected.

### Where expected values come from

None of the expected values were produced by the implementation under test.

- Canonical strings were written by hand in the generator script from the rules above. Digests were computed with Node's `crypto.createHash("sha256")` over those strings, and two were cross-checked with `shasum -a 256`.
- Number vectors:
  - RFC 8785 appendix B (number serialization samples): `4.50` gives `4.5`, `2e-3` gives `0.002`, `0.000000000000000000000000001` gives `1e-27`, `5e-324` gives `5e-324`, `1E30` (listed there as `1e+30`, rejected here as an out-of-range integer).
  - ECMAScript Number::toString (ECMA-262 6.1.6.1.20): `1e-7` gives `1e-7`, `0.000001` gives `0.000001`, `0.1`, `1.5`, `100`, `1.0` gives `1`, `-1`, and `9007199254740991` (the largest safe integer, printed in full). `1e21` would print as `1e+21`, but is an error here because it is an integer above 2^53 - 1.
- Key order: `a` (U+0061) < `é` (U+00E9) < `😀` (U+D83D U+DE00 in UTF-16) < U+FFFF. Code point order would put U+FFFF before `😀`, so this vector separates UTF-16 order from code point order.
- Escapes follow RFC 8785 section 3.2.2.2: `\b \f \n \r \t`, `\"`, `\\`, other characters below U+0020 as lowercase `\u00xx`, everything else (including `/`, DEL, U+2028 and astral characters) raw.

The package test also cross-checks the vectors against the Lean `kernel.canonical`, with the raw `args_text` spliced into the preimage:
- Integer-only ok vectors must give the same canonical string, except `depth-128` (Lean counts depth over the whole preimage, so 128 nested levels in args is 129 there), and `num-1.0` and `num-1E2` (not integer spellings).
- Error vectors with `args_text` must also be rejected by Lean, except `err-neg-zero` (Lean reads `-0` as the integer 0).
- Lean's parser is integer-only, so it does not exercise the fraction rules (round-trip value, precision, exponent printing).

## Tool digest vectors

`tool-v1.jsonl` holds test vectors for the `writ-tool-v1` tool digest (`docs/formats.md`, Tool digests). Each line is one JSON object:

- `id`: vector name.
- `tool_text`: a tools.json document holding the tool, either an MCP `tools/list` result or a bare array. An accepted vector's document lists exactly one tool.
- `canonical`: the expected preimage, the RFC 8785 canonical JSON of `{"t":"writ.tool.v1","tool":<the tool>}`.
- `digest`: `"sha256:"` plus the lowercase hex SHA-256 of the UTF-8 bytes of `canonical`.
- `error_contains`: instead of `canonical` and `digest`, reading the document must fail with an error that contains this text.

### Rules the vectors pin

- Every member of the tool is digested, and nothing outside it: a `tools/list` result's `nextCursor`, `_meta` and any other member do not count, and members other than `tools` and `nextCursor` are ignored whatever their type (`tools-list-next-cursor`, `tools-list-meta` and `tools-list-unknown-key` have one digest). Key order and whitespace do not count either (`annotations-present` and `annotations-reordered` have one digest); dropping the annotations does (`annotations-absent`).
- Keys sort by UTF-16 code unit, as for call digests (`key-order-non-ascii`, where an escaped `\u00e9` key sorts beside a raw `é2`), and integer-like keys sort as strings: `-1`, `01`, `1`, `1.5`, `10`, `9` (`key-order-integer-like`). The `tool_text` of `unicode-escapes` and `astral-escaped-and-raw` holds escape text beside the same characters written raw: `\u00e9` beside `é`, `\u2028` and `\u2029`, `\u007f` beside a raw DEL, `\/`, `\u001f`, `\u0000`, and the surrogate pairs `\ud834\udd1e` beside a raw 𝄞 and `\ud83d\ude00` beside a raw 😀. Escapes are unescaped and printed by RFC 8785 rules, so the canonical text is the same whichever way a character was written: U+2028, U+2029, DEL and astral characters raw, U+001F and U+0000 as `\u001f` and `\u0000`.
- A number literal with at most 15 significant digits and a magnitude of 0 or within 1e-300 to 1e300 prints as ECMAScript prints the nearest double: `0.5`, `1.5e3` gives `1500`, `-0` gives `0`, `1E-7` gives `1e-7`, `100`, `2.0` gives `2`, `1e21` gives `1e+21`, `100000000000000000000` stays as written, `123e-20` gives `1.23e-18`, and the bounds `1e300` and `-1e-300` are accepted. Significant digits run from the first to the last nonzero digit, so trailing zeros are free (`num-trailing-zeros`).
- Refused: a literal with 16 or more significant digits (`err-16-digits`, `err-17-digit-fraction`), a magnitude outside 1e-300 to 1e300 (`err-1e400`, `err-1.5e300`, `err-1e-301`), a duplicate key, a lone surrogate, a tool without a string `name`, a name listed twice, and a document that is neither a result nor an array. A literal that breaks both number rules reports the digits (`err-digits-and-range`).

### Where expected values come from

None of the expected values were produced by the implementation under test. A Node script, kept outside the repository, parsed each `tool_text` with `JSON.parse` and wrote `canonical` itself: each object's keys sorted with the default JavaScript sort (UTF-16 code units), and every key, string and number printed by `JSON.stringify`, which RFC 8785 is defined to agree with. Objects are written by hand rather than by `JSON.stringify` of a sorted copy, because a JavaScript object lists integer-like keys first whatever order they were added in. Each canonical string was cross-checked against `canonicalize` of `@anijani/writ` wherever that accepts the value (it refuses `-0` and integers above 2^53 - 1). Digests are Node's `crypto.createHash("sha256")` of those strings. The number cases were checked by hand against ECMA-262 Number::toString.

The Lean tests (`WritTests/Tool.lean`) run every vector through `Jcs.parse`, `Tool.listOf`, `Tool.preimage` and `Tool.digest`. The package test (`packages/writ/test/tool.test.ts`) runs `toolPreimage` and `toolDigest` on the first tool of each `tool_text` read with `JSON.parse`. It skips the refusals it cannot see in a parsed tool: a duplicate key, which `JSON.parse` resolves silently, and the problems of the list around the tool.
