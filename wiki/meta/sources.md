# Absorption ledger

Tracks every pre-wiki knowledge source: where its content now lives, and what should
eventually happen to the original. Per [how-to-write](./how-to-write.md), absorbed
sources must not drift from the wiki; when you change one, reconcile the other in the
same session. Status values: **absorbed** (content integrated; original still present),
**pointerized** (original reduced to a stub pointing here), **generated** (original is a
build artifact), **live** (original remains authoritative for now), **deleted**
(original removed after absorption).

Last reconciled: 2026-07-24 (`AGENTS.md` living-docs cross-refs; phase 1 wiki
migration otherwise closed 2026-07-23).

| Source | Absorbed into | Status | Planned disposition |
| --- | --- | --- | --- |
| `README.md` | [index](../index.md), [architecture/overview](../architecture/overview.md), [engineering/workflows](../engineering/workflows.md) | pointerized (2026-07-23) | Keep as short public landing page; points at wiki |
| `AGENTS.md` | [vision](../vision.md), [architecture/*](../architecture/overview.md), [theory](../theory/compiler-theory.md), [meta/how-to-work](./how-to-work.md), [status/roadmap](../status/roadmap.md), [engineering/testing](../engineering/testing.md), [architecture/diagnostics](../architecture/diagnostics.md) | absorbed + living-docs pointers (2026-07-24) | **Harness-wired contract stays normative** (principles, playbook A–F, coding standards). Wiki owns status/health/roadmap, crate depth, theory, ops. Further slimming needs owner sign-off ([roadmap decisions](../status/roadmap.md#decisions-needing-an-owner)). |
| `CONTRIBUTING.md` | [engineering/workflows](../engineering/workflows.md), [meta/how-to-work](./how-to-work.md) | pointerized (2026-07-23) | Done — short page + wiki links |
| `docs/architecture.md` | [architecture/overview](../architecture/overview.md), [architecture/engine](../architecture/engine.md) | pointerized (2026-07-23) | Done — stub |
| `wiki/architecture/deps.md` (was `docs/deps.md`) | [architecture/overview](../architecture/overview.md#dependency-graph) | generated (into wiki, 2026-07-23) | Live artifact of `scripts/gen_deps_graph.sh` / `just docs`; CI diffs this path. `docs/deps.md` is a stub pointer. |
| `docs/quickstart.md` | [engineering/workflows](../engineering/workflows.md) | pointerized (2026-07-23) | Done — stub |
| `docs/examples.md` | [engineering/workflows](../engineering/workflows.md#runnable-examples) | pointerized (2026-07-23) | Done — stub |
| `docs/diagnostic-codes.md` | [architecture/diagnostics](../architecture/diagnostics.md) | pointerized (2026-07-23) | Done — stub. **Out-of-scope straggler:** `scripts/check_diagnostic_codes.sh` still prints a hint naming `docs/diagnostic-codes.md` (hint text only; stub still exists). |
| `notes/AST design rationale.md` | [crates/parse-js](../crates/parse-js.md#ast-design-rationale), [graveyard](../graveyard.md) | deleted (2026-07-23) | Done |
| `notes/Lexical lifetimes.md` | [crates/minify-js](../crates/minify-js.md#lexical-lifetimes-variable-slot-reuse) | deleted (2026-07-23) | Done; full numbering scheme + worked puzzles absorbed into the wiki page (2026-07-23). |
| `notes/Name minification.md` | [crates/minify-js](../crates/minify-js.md#name-minification-algorithm) | deleted (2026-07-23) | Done; both worked examples absorbed verbatim. |
| `notes/Parentheses.md` | [crates/emit-js](../crates/emit-js.md#parentheses-beyond-precedence) | deleted (2026-07-23) | Done |
| `notes/Textual compression.md` | [crates/minify-js](../crates/minify-js.md#rejected-textual-compression), [graveyard](../graveyard.md) | deleted (2026-07-23) | Done |
| `planner_scratchpad.md` | [crates/types-ts-interned](../crates/types-ts-interned.md), [graveyard](../graveyard.md#completed-scratchpads) | deleted (2026-07-23) | Done |
| `megatest/README.md` | [engineering/testing](../engineering/testing.md#megatest-stress-programs) | absorbed | Keep (tiny, colocated with fixtures) |
| `typecheck-ts-harness/README.md` | [engineering/testing](../engineering/testing.md#typescript-conformance--difftsc-typecheck-ts-harness) | absorbed | Keep as operational README; wiki owns rationale |
| `conformance-harness/README.md` | [engineering/testing](../engineering/testing.md#shared-harness-mechanics-conformance-harness) | absorbed | Keep (crate README) |
| `test262/README.md` | [engineering/testing](../engineering/testing.md#test262-parser-harness-test262) | absorbed | Keep (crate README) |
| `test262-semantic/README.md` | [engineering/testing](../engineering/testing.md#test262-semantic-runner-test262-semantic) | absorbed | Keep (crate README) |
| `parse-js/README.md` | [crates/parse-js](../crates/parse-js.md) | absorbed | Keep (published crate face) |
| `parse-js/notes/syntax_gaps.md` | [crates/parse-js](../crates/parse-js.md#conformance-and-the-syntax-gap-tracker) | absorbed | Keep as the live gap tracker (updated by conformance runs) |
| `semantic-js/README.md` | [crates/semantic-js](../crates/semantic-js.md) | absorbed | Keep; shrink toward summary |
| `examples/semantic-js/README.md` | [crates/semantic-js](../crates/semantic-js.md#examples) | absorbed | Keep (doctest mirror) |
| `types-ts-interned/README.md` | [crates/types-ts-interned](../crates/types-ts-interned.md) | absorbed | Keep; shrink toward summary |
| `minify-js/README.md` | [crates/minify-js](../crates/minify-js.md) | absorbed | Keep (published crate face; release tooling rewrites it) |
| `minify-js-cli/README.md` | [crates/minify-js](../crates/minify-js.md#cli-minify-js-cli) | absorbed | Keep |
| `minify-js-nodejs/README.md` | [crates/minify-js](../crates/minify-js.md#nodejs-bindings-minify-js-nodejs) | absorbed | Keep (npm package face) |
| `parse-js-cli/README.md` | [crates/parse-js](../crates/parse-js.md#cli-parse-js-cli) | absorbed | Keep |
| `typecheck-ts-cli/README.md` | [crates/typecheck-ts](../crates/typecheck-ts.md#cli-typecheck-ts-cli) | absorbed | Keep |
| `optimize-js-debugger/README.md` | [crates/optimize-js](../crates/optimize-js.md#debugger-ui-optimize-js-debugger) | absorbed | Keep |
| `diagnostics/README.md` | [architecture/diagnostics](../architecture/diagnostics.md) | absorbed | Keep; shrink toward summary (link updated to wiki, 2026-07-23) |
| `bench/typecheck-ts/README.md` | [engineering/testing](../engineering/testing.md#benchmarks) | absorbed | Keep |
| `vm-js/docs/webidl_host_objects.md` | [crates/vm-js](../crates/vm-js.md#webidl-host-objects-rooting-rules-and-wrapper-caches) | absorbed | Keep (deep-dive colocated with vm-js) |
| `typecheck-ts/fixtures/typescript-libs/5.9.3/README.md` | [crates/typecheck-ts](../crates/typecheck-ts.md#bundled-libraries) | absorbed | Keep (licensing colocation) |
| Agent exploration findings (2026-07-23 session) | [status/health](../status/health.md), [architecture/determinism](../architecture/determinism.md#case-study-the-nameinterner-deadlock) | absorbed | — |
| External engineering-principles prompt (2026-07-23) | [meta/how-to-work](./how-to-work.md) | absorbed | — |

## Not yet absorbed / to watch

- `.github/workflows/*.yaml` — operationally summarized in
  [workflows](../engineering/workflows.md); the YAML remains authoritative for exact CI
  behavior. Re-check the summary when workflows change.
- Crate-level rustdoc (`//!` module docs) — the wiki does not duplicate API docs;
  rustdoc stays authoritative for signatures and doctests. The wiki owns design and
  rationale.
- `justfile`, `version` (release script), guard scripts under `scripts/` — described in
  [workflows](../engineering/workflows.md); source stays authoritative.
