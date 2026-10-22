# Graveyard

Retired designs, rejected alternatives, failed or superseded approaches, and completed
one-off programs — kept so nobody retries them ignorantly, and so someone *can* retry
them deliberately if the constraints change. Each entry: what it was, why it died, and
what replaced it. (Policy: [how-to-write § rationale](./meta/how-to-write.md#rationale-background-and-the-graveyard).)

## Retired components

### symbol-js

The original scope/symbol layer for the minifier/optimizer era. Died because its shape
contradicted the deterministic-parallel end-state: scopes stored as
`Arc<RwLock<...>>` attached per AST node, and symbol IDs explicitly documented as
"opaque, ephemeral, and non-deterministic" — unusable for stable caching, parallel
checking, or reproducible outputs. Replaced by `semantic-js` (content-addressed
`ScopeId`/`SymbolId`, immutable snapshots, `BTreeMap` iteration, JS + TS modes);
downstream callers migrated from `compute_symbols` to `js::bind_js` + `assoc::js`
readers. The crate was removed from the workspace entirely (not deprecated in place)
to prevent two competing binders from coexisting — per the one-semantics bet
([vision #4](./vision.md#the-hypotheses-falsifiable-bets)). Straggling references
should migrate, never revive the legacy crate.

### types-ts (placeholder crate)

An earlier placeholder type-representation crate. Removed in favor of a single
maintained representation (`types-ts-interned`) explicitly "to avoid drift" — the same
two-brains argument as symbol-js. If a second type representation ever seems
necessary, the burden of proof is on why the interned store can't express the need.

### Legacy AST lowering in optimize-js

The optimizer originally lowered directly from the parse-js AST. Removed in favor of
the single `hir-js` pipeline once HIR existed — two lowering paths meant every
semantics fix had to land twice. The HIR path is now the only path
(`crates/optimize-js.md`).

### module_graph_loader shim (vm-js)

Deprecated (commit `34bd48b`) in favor of the structured `module_loading.rs` /
`module_record.rs` machinery as the VM's module story matured toward spec shape.
Delete the shim when nothing references it.

## Rejected alternatives (design-level)

### Textual compression in the minifier

Aliasing reused well-knowns, deduplicating repeated literals, aliasing hot
properties/methods, `Object.assign` tricks, `typeof`/`instanceof` helper functions,
statement-pattern helpers — all **rejected**, and constant/built-in aliasing was
actually shipped once and **removed in minify-js commit `ff48b8b`**. Reasons
(empirical, preserved from `notes/Textual compression.md`): they complicate and slow
minification; they add runtime indirection that also defeats engine optimizations;
they *worsen* gzip/Brotli output (the compressor already exploits repetition, better);
they pollute scopes and reduce name-minification effectiveness; and they are
correctness-tricky (symbols, execution order/stacks). Retry only with benchmark
receipts on post-compression sizes across a real corpus.

### `const` → `let` minifier rewrite

Declined (2026-07-23, pass-program trap analysis) despite appearing on the historical
minify-js roadmap: reassigning a `const` is an observable runtime `TypeError`, so the
rewrite is only safe with whole-body write-analysis proving no reassignment — and the
size win is largely illusory because gzip/Brotli already crush repeated `const`
tokens (the same empirical argument that killed textual compression, above). Revisit
only alongside a real dataflow pass that needs the write-analysis anyway. Ownership
and trap notes live in [crates/minify-js](./crates/minify-js.md).

### Arena + `&'bump mut` AST

The AST trade study (`notes/AST design rationale.md`, preserved in
[crates/parse-js](./crates/parse-js.md#ast-design-rationale)) explored bump-arena
nodes with mutable references to avoid malloc. Rejected in the shipped design:
mutable references make subtrees non-cloneable and moves awkward
(`mem::take` + poisoned leftovers in the arena), while `RefCell`/`Rc` alternatives
"mostly move lifetime errors from compile time to runtime". Owned `Box<S>` nodes won:
transforms are mostly moves, and field-level move tracking makes them safe and
obvious. Revisit only if parser allocation dominates real profiles.

### Rowan/green-tree syntax layer

Considered (as the rust-analyzer route) and rejected unless fine-grained incremental
*parsing* becomes a requirement: `parse-js` is already high-coverage and fast, and the
incrementality bet is at query granularity (file/def/body), not token granularity.
Introducing a second syntax tree would fork every downstream consumer.

### Per-expression incremental queries

Rejected at design time (AGENTS): modeling "type of expression at node X" as a global
query explodes the dependency graph and kills performance. The unit is
`check_body(BodyId)` producing a side table — bodies parallelize and cache well.
([theory § incrementality](./theory/compiler-theory.md#5-incremental-computation-memoized-function-database)).

### Thread-per-test harness timeouts

Both the parser conformance runner and the typecheck harness explicitly avoid spawning
an OS thread per test case (an earlier easy design): timeouts are cooperative
cancellation flags checked by the parser/checker, plus a small bounded deadline-
enforcement pool; live-tsc timeouts kill the Node runner process so blocked pipe reads
unblock. Cheaper, and it keeps per-test cancellation from poisoning whole runs.

### Manual allowlist for negative-syntax parser tests

The parser conformance runner originally would have needed a hand-maintained list of
"expected TypeScript parse errors". Superseded (2026-01) by consulting TypeScript's
`.errors.txt` baselines directly and treating expected TS1xxx parse errors as passing —
the oracle maintains the list for us (`parse-js/notes/syntax_gaps.md` now tracks only
*real* mismatches, and is empty as of that date).

## Completed scratchpads

### Conditional-types / normalization hardening (planner_scratchpad.md)

A worked program, all tasks complete; absorbed 2026-07 and preserved here because the
*shape* of the solution is load-bearing context for
[types-ts-interned](./crates/types-ts-interned.md):

- Task 40 — `RelationMode::SKIP_NORMALIZE` (break relate↔evaluate normalization
  cycles).
- Task 45 — evaluator conditional-assignability integration
  (`TypeEvaluator::with_conditional_assignability`, defaulting to a `RelateCtx`).
- Task 49 — options-consistency invariant (store options must match checker options).
- Task 55 — indeterminate conditional deferral (free type params ⇒ defer, don't
  guess).
- Task 64 — `any`/`never` conditional special cases.
- Task 71 — distributive `extends` per-member evaluation.
- Task 79 — scope-aware free-type-param detection.
- Task 85 — structural conditional tests.

End state: conditional evaluation uses structural assignability safely via `RelateCtx`
in `SKIP_NORMALIZE` mode; normalization is cache-backed by `EvaluatorCaches`. The
scratchpad file itself is ready for deletion per the
[ledger](./meta/sources.md).

## Historical bugs worth remembering

- **The NameInterner deadlock (2026-07)** — guard held across recursion into the same
  `RwLock`, exposed only under parallel checking on a loaded machine. Kept alive as
  the canonical lock-discipline case study in
  [determinism](./architecture/determinism.md#case-study-the-nameinterner-deadlock);
  listed here because its *lesson* outlives its fix: single-threaded green says
  nothing about parallel correctness, and every guard-across-call is a suspect.
