# ecma-rs wiki

The single knowledge base for this repository: architecture, rationale, theory,
operations, status, and history. Governed by [meta/how-to-write.md](./meta/how-to-write.md)
(absorption discipline, evergreen style, update loop) — read that before editing any
page. Work itself is governed by [meta/how-to-work.md](./meta/how-to-work.md).

## Reading order for newcomers

1. [vision.md](./vision.md) — what this project is, the bets it makes, the anchor for
   every design decision.
2. [architecture/overview.md](./architecture/overview.md) — the crates, the data flow,
   and an honest assessment of current vs ideal.
3. [architecture/engine.md](./architecture/engine.md) — how the semantic engine is
   meant to operate (inputs, queries, parallelism, API contract).
4. [status/health.md](./status/health.md) — what is actually broken/verified right now.
5. Then the crate page for whatever you're touching.

## Map

### Meta (how we work)

| Page | Owns |
| --- | --- |
| [meta/how-to-write.md](./meta/how-to-write.md) | Wiki constitution: absorption, evergreen style, page anatomy, the update loop |
| [meta/how-to-work.md](./meta/how-to-work.md) | Engineering doctrine: feedback loops, testing policy, delegation, self-review, repo bindings |
| [meta/sources.md](./meta/sources.md) | Absorption ledger: every pre-wiki doc, where it went, its disposition |

### Strategy and design

| Page | Owns |
| --- | --- |
| [vision.md](./vision.md) | Goal, hypotheses, non-goals, success criteria — the anchor |
| [architecture/overview.md](./architecture/overview.md) | Crate map, data flow, ID/span discipline, dependency graph, structural assessment |
| [architecture/engine.md](./architecture/engine.md) | Target operating model: host inputs, query DAG, parallelism, memory, API contract |
| [architecture/determinism.md](./architecture/determinism.md) | The determinism doctrine, mechanisms per layer, lock discipline, deadlock case study |
| [architecture/diagnostics.md](./architecture/diagnostics.md) | Diagnostic model, severity/exit policy, stable-code registry, how to add codes |
| [theory/compiler-theory.md](./theory/compiler-theory.md) | The CS foundations per layer + the "completing rigorously" doctrine + references |

### Crates

| Page | Covers |
| --- | --- |
| [crates/parse-js.md](./crates/parse-js.md) | Parser, AST design (+ rationale), dialects, conformance runner, `parse-js-cli` |
| [crates/hir-js.md](./crates/hir-js.md) | HIR lowering, content-addressed IDs, SpanMap, type arenas |
| [crates/semantic-js.md](./crates/semantic-js.md) | JS-mode scopes/resolution, TS-mode binder/merging/exports, assoc helpers |
| [crates/types-ts-interned.md](./crates/types-ts-interned.md) | Type store/interning, relation engine, evaluator, fuzzing |
| [crates/typecheck-ts.md](./crates/typecheck-ts.md) | Program/Host API, salsa DB, body checking, bundled libs, `typecheck-ts-cli` |
| [crates/emit-js.md](./crates/emit-js.md) | Emitter backends, ASI machinery, parenthesization rules |
| [crates/minify-js.md](./crates/minify-js.md) | Minifier pipeline, TS erasure, renaming algorithm, lifetimes, CLI/npm, release |
| [crates/optimize-js.md](./crates/optimize-js.md) | IL/CFG/SSA passes, decompiler, typed mode, debugger UI |
| [crates/vm-js.md](./crates/vm-js.md) | VM stack: heap/GC/handles, interpreter, jobs, WebIDL embedding (+ runtime-js, webidl crates) |

### Operations and status

| Page | Owns |
| --- | --- |
| [engineering/workflows.md](./engineering/workflows.md) | Setup, just targets, guard scripts, examples, CI, release flow, conventions |
| [engineering/testing.md](./engineering/testing.md) | Oracle map, conformance/difftsc, test262 (parser + semantic), megatest, fuzzing, benches |
| [status/health.md](./status/health.md) | Dated snapshot of build/test reality and known bugs (as of 2026-07-24) |
| [status/roadmap.md](./status/roadmap.md) | Phased plan with acceptance criteria; decisions needing an owner |
| [graveyard.md](./graveyard.md) | Retired designs, rejected alternatives, completed programs, memorable bugs |

## Relationship to `AGENTS.md`

[`AGENTS.md`](../AGENTS.md) is the **harness-wired agent contract** (architecture
constraints, playbook phases, coding standards). Agents load it; it must not be gutted
casually. This wiki owns living status, crate depth, theory, and engineering ops.
`AGENTS.md` has a [Living docs](../AGENTS.md#living-docs-wiki) table pointing here;
the absorption ledger tracks the relationship in [meta/sources.md](./meta/sources.md).

**Conflict rule** (same as in `AGENTS.md`): architecture constraints in `AGENTS.md`
win until deliberately reconciled; dated status (what builds / what's done) is owned
by [status/health](./status/health.md) and [status/roadmap](./status/roadmap.md).

## Maintenance contract

Every work session ends by reconciling this wiki
([the update loop](./meta/how-to-write.md#the-update-loop-continuous-absorption)):
status pages for changed reality, owning pages for changed designs, graveyard for
abandoned paths, ledger for absorbed sources. The forbidden state is silent
disagreement between wiki and code.
