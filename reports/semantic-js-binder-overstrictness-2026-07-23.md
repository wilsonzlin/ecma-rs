# semantic-js binder over-strictness — 2026-07-23

Pass-corpus BIND false positives: **11 → 0** (plus 1 parser-owned skip:
`431ecef8c85d4d24.js`).

Verified by `cargo test -p semantic-js --test pass_corpus_bind`.

## Before (probe)

| File | Code | Cause |
| --- | --- | --- |
| `06f0deb843fbf358.js` | BIND0007 | escaped `'use\x20strict'` |
| `855b8dea36c841ed.js` | BIND0007 | escaped directive in function |
| `ac73bc36bbc48890.js` | BIND0007 | escaped `"use\x20strict"` |
| `cb625ce2970fe52a.js` | BIND0007 | escaped directive in function |
| `09e84f25af85b836.js` | BIND0013 | `({set a(yield){}})` |
| `fa5b398eeef697a6.js` | BIND0005 | `({set a(eval){}})` |
| `6b76b8761a049c19.js` | BIND0013 | `function *a(){({set b(yield){}})}` |
| `0d137e8a97ffe083.js` | BIND0013 | `function *a(){({get b(){yield}})}` |
| `9a666205cafd530f.js` | BIND0013 | `function *a(){({b(){yield}})}` |
| `b205355de22689d1.js` | BIND0013 | `function *a(){({set b(c){yield}})}` |
| `3dabeca76119d501.js` | BIND0001 | `try {} catch (a) { if(1) function a(){} }` |

## Fixes

See `wiki/crates/semantic-js.md` (resolved over-strictness table).
