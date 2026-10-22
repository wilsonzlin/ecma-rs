# Vision

This page is the constant anchor. When a design decision is unclear, re-read this page;
every decision should trace to one of the bets below or be flagged as a new bet that
belongs here. (Absorbed from `AGENTS.md`'s design principles plus the repo's observable
trajectory; last reconciled 2026-07-23.)

## What we are building

**ecma-rs is a single, deterministic JavaScript/TypeScript language engine in Rust —
one semantic substrate with many products.**

Parse once (`parse-js`), lower once (`hir-js`), understand names once (`semantic-js`),
represent types once (`types-ts-interned`) — and let every tool be a view over the same
stable IDs:

- **`typecheck-ts`** — a rigorous, embeddable TypeScript type checker with a query API
  (`Program`), built for programs that need to *ask questions about types*, not just
  print errors: type of every symbol, every expression, every export.
- **`minify-js`** — a fast single-file minifier (published crate + CLI + npm package).
- **`optimize-js`** — an SSA-based optimizer/decompiler, the seed of typed AOT
  compilation.
- **`emit-js`** — a deterministic printer shared by everything that writes JS back out.
- **`vm-js`** (+ `runtime-js`, `webidl`, `webidl-vm-js`) — a from-scratch, spec-shaped
  ECMAScript VM with a precise GC, budgets, and embedder hooks.

The repo is both a standalone toolchain and an embedding target: it is vendored as
`engines/ecma-rs` inside **FastRender** (a browser-engine project), which consumes the
VM via the WebIDL layer and drives the test262 corpus through `test262-semantic`. Design
decisions must serve both consumers: library users on crates.io/npm, and a
deeply-integrated engine embedder.

## Why (the gap we exist to fill)

- **tsc is an oracle, not an engine.** The TypeScript compiler is authoritative but
  slow, single-threaded, non-deterministic in output ordering across environments, and
  awkward to embed from Rust. Downstream Rust tooling (bundlers, AOT compilers,
  analyzers, a browser engine) needs type information *as data* with stable IDs, not a
  CLI that prints strings.
- **Syntax-level tooling plateaued.** Fast Rust/Go parsers and minifiers exist, but
  they stop at scope analysis. The differentiated value is *semantics*: real binding,
  real types, real flow analysis — shared across tools so they compound instead of
  drifting.
- **Browser-grade execution needs ownership of the whole stack.** An engine that will
  live inside FastRender needs a VM whose GC, interruption, and host-embedding story we
  control end to end.

## The hypotheses (falsifiable bets)

1. **Determinism-first pays for itself.** If every derived artifact (IDs, exports,
   diagnostics, reports) is a pure, order-independent function of inputs —
   content-addressed IDs, ordered maps, sorted outputs — then parallelism, caching,
   differential testing, and distributed CI all become trivially trustworthy. The cost
   (stable hashing, canonical ordering everywhere) is bounded and front-loaded.
   *Falsified if*: determinism overhead dominates profiles, or collisions/ordering
   rules leak complexity into every feature.
2. **Coarse-grained queries capture the incrementality that matters.** Per-file /
   per-def / per-body queries (salsa) give near-all of the re-check savings at a small
   fraction of the complexity of per-expression dependency tracking. *Falsified if*:
   IDE-grade latency targets prove unreachable without finer grains.
3. **A 95%-case checker, continuously diffed against tsc, beats a 100% clone.** Match
   `tsc` on the semantics that real code exercises (the "semantic cornerstones" list in
   [theory](./theory/compiler-theory.md#the-typescript-cornerstones)), measure the gap
   with `difftsc`/conformance, and deliberately skip the long tail (exact message
   wording, exotic corner scoring). *Falsified if*: the skipped tail turns out to be
   load-bearing for real projects.
4. **One semantics layer, many tools.** The minifier, optimizer, and checker sharing
   `semantic-js`/`hir-js` eliminates per-tool binder drift and unlocks typed
   minification/optimization later. *Falsified if*: tool-specific needs force the
   shared layer into lowest-common-denominator shape.
5. **Spec-shaped first, fast later (VM).** Implement ECMA-262 abstract operations
   literally (completion records, job queues, spec ops) to get correctness and
   test262 traction, then add performance tiers without changing observable semantics.
   *Falsified if*: the spec-shaped core is too slow even for engine bring-up.

## Non-negotiable design principles

(Absorbed from `AGENTS.md`; the detailed mechanisms live in
[architecture/determinism](./architecture/determinism.md) and
[architecture/engine](./architecture/engine.md).)

1. **Determinism** — same inputs → same outputs, regardless of thread scheduling.
2. **Cycle-safe by construction** — every expand/relate/normalize operation has
   recursion guards, memoization, and an explicit termination story.
3. **Incremental through queries** — revisioned inputs, dependency tracking, coarse
   granularity.
4. **Parallel without shared mutability** — immutable `Arc` snapshots; sharded or
   thread-local caches; never a single global lock.
5. **Two-level architecture** — global (symbols, exports, module graph) vs local
   (per-body flow, inference, narrowing).
6. **Ergonomic public API** — downstream sees `Program`, `FileId`, `DefId`, `TypeId`,
   `Diagnostic`; internals stay opaque.

## Non-goals

Deliberate exclusions, with owners' rationale preserved:

- **Module resolution policy in the core.** The host supplies `resolve(from, spec)`;
  the checker works in bundlers, Bazel-style builds, IDEs, and virtual filesystems
  without carrying Node's resolution algorithm. (A Node-style resolver ships as an
  opt-in `resolve` feature / CLI layer, not in the core.)
- **Project references, watch mode, `.d.ts` emit, language-service protocol** — out of
  scope for the engine; downstream tools can build these on the query API.
- **`--allowJs` JS-inference quirks and exotic JSDoc typing** — deferred.
- **Bundling in the minifier** — single-input minification only; TS is handled by
  erasure, not compilation.
- **Textual compression in the minifier** (aliasing well-knowns, literal dedup, helper
  functions): rejected with data — it hurts gzip/Brotli, costs runtime, pollutes
  scopes, and complicates correctness. See
  [graveyard](./graveyard.md#textual-compression-in-the-minifier).
- **Matching `tsc` message text** — codes and spans matter; wording does not.

## Success criteria

The numbers we hold ourselves to (baseline targets from `AGENTS.md`; current standing
tracked in [status/health](./status/health.md)):

- **Checker correctness**: conformance pass-rate against the upstream TypeScript suite
  trending up with a triaged, manifest-tracked gap list; difftsc parity (codes + spans,
  normalized) on the curated suites; zero unexplained regressions (`--fail-on new`).
- **Checker performance**: ~50k LOC project checked < 500 ms warm on a modern desktop;
  incremental re-check after a local edit < 50 ms for affected bodies; memory bounded
  by design.
- **Minifier**: single-core performance competitive with esbuild on the standard
  benchmark corpus (`bench/`), with correctness gated by round-trip and semantics
  tests.
- **VM**: test262 pass-rate ladder on curated suites trending up; zero
  invariant-violating crashes (VM errors must become catchable JS errors or typed host
  errors).
- **Workspace hygiene**: `cargo check/test --workspace --all-targets` green; guard
  scripts green; deterministic outputs byte-identical across `RAYON_NUM_THREADS=1` vs
  many.

## How to use this page

Cite the bet when making a non-obvious decision ("choosing BTreeMap here per
determinism bet #1"). If a decision serves no bet, either it's local pragmatics (fine)
or it's a new strategic direction — which means this page changes first, not silently.
