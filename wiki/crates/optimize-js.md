# optimize-js

SSA-based optimizer and decompiler: JS in, optimized JS out, via a real compiler
middle-end. Also the seed of typed AOT compilation (optional `typed` feature consuming
the checker). Theory background:
[compiler-theory § SSA](../theory/compiler-theory.md#6-ssa-optimization-optimize-js).

## Pipeline

```
parse (parse-js, dialect Ts — accepts TS so typed pipelines share the parse)
  → hir-js lowering
  → semantics (symbol/: JsSymbols via semantic-js JS mode + VarAnalysis)
  → IL (il/: Inst over Const/Arg operands; s2i/ = source-to-IL)
  → basic blocks + CFG (cfg/)
  → dominator tree (dom/)
  → SSA construction (ssa/: insert_phis at dominance frontiers, rename)
  → optimization passes to fixpoint (opt/)
  → SSA deconstruction (+ phi_simplify)
  → decompilation (decompile/) → parse-js AST → emit-js
```

Public one-shots: `compile_source(source, TopLevelMode, debug) -> Program`,
`program_to_ast(...)`, `program_to_js(&program, &DecompileOptions, EmitOptions)`.
Errors are `Vec<Diagnostic>` (`OPT0001` use-before-declaration, `OPT0002` unsupported
syntax; spans via the shared model). The legacy direct-AST lowering was removed — HIR
is the single path ([graveyard](../graveyard.md#legacy-ast-lowering-in-optimize-js)).

## IL and passes

`il/inst.rs`: instructions over `Arg = Builtin(path) | Const(Const) | Fn(index) |
Var(u32)`; `Const` covers JS primitive constants (`BigInt`, `Bool`, `Null`,
`Num(JsNumber)`, `Str`, `Undefined`). `Builtin` holds dotted paths (e.g.
`Array.prototype.forEach`) as single strings for easy matching. Functions are indexed
and immutable (Const-like). All carry arbitrary-but-canonical `Ord` for deterministic
containers.

Passes (`opt/`), run to fixpoint via `PassResult` change tracking:

- `optpass_dvn` — dominator-order value numbering (GVN-style redundancy elimination).
- `optpass_trivial_dce` — use-count dead code elimination.
- `optpass_impossible_branches` — constant-condition branch folding.
- `optpass_redundant_assigns` — copy/assign cleanup.
- `optpass_cfg_prune` — unreachable/empty block removal.

`eval/` provides the abstract constant evaluation the passes lean on; JS effect
conservatism is the default stance (nearly everything can throw or trigger getters —
prove before folding).

## Decompilation

The inverse problem — structured JS from an optimized CFG — lives in `decompile/`:
`structurer.rs` (CFG → `if`/`while`/`break`/`continue` regions, relooper lineage),
`regalloc.rs` (variable-slot assignment over lexical lifetimes — the model documented
in [minify-js § lexical lifetimes](./minify-js.md#lexical-lifetimes-variable-slot-reuse)),
`names.rs` (identifier synthesis), `il.rs`/`top_level.rs`/`foreign.rs` (IL → AST),
`options.rs` (`DecompileOptions`). Output goes through `emit-js`, so parenthesization/
ASI correctness is inherited, not reimplemented.

## Typed mode

Feature `typed` (off by default) pulls in `typecheck-ts` + `types-ts-interned` for
type-aware experiments without making type checking a hard dependency of minification
pipelines — the dependency edge in the generated graph is this optional one. The
long-term direction (vision bet #4 / AGENTS Phase F): thread type facts into passes
(devirtualization, shape-based property access, const-enum folding beyond erasure).

## Debugger UI (`optimize-js-debugger`)

Developer tool for inspecting optimizer output (CFG, per-pass debug steps, symbols):
Rust axum server (`cargo run -p optimize-js-debugger`, `POST /compile` on :3001) + an
esbuild/React UI (`npm install && npm start` in `optimize-js-debugger/`, tests via
`npm test`, production build to `dist/`). Snapshot mode for CI/scripting:

```bash
cargo run -p optimize-js-debugger -- --snapshot --input tests/fixtures/debug_input.js \
  --mode module --output /tmp/snapshot.json
```

`OptimizerDebug` (`util/debug.rs`) records the per-pass states the UI renders.

## Verification

Deterministic ordering tests (stable symbol/CFG output), unit tests per pass, and the
`megatest/` corpus as stress input ([testing](../engineering/testing.md#megatest-stress-programs)).
The property target per
[theory](../theory/compiler-theory.md#8-completing-the-implementation-rigorously):
semantic equivalence of input vs optimized output on executable corpora (once `vm-js`
can serve as the executing oracle — a genuinely valuable integration waiting on VM
maturity).

## Known issues and directions

- Coverage: `OPT0002` unsupported-syntax diagnostics define the current envelope;
  expanding IL coverage (async/generators/classes edge cases) is tracked work, not
  drift.
- Pass ordering is fixpoint-iterated but not phase-ordered rigorously; fine at current
  pass count, revisit if the pass set grows.
- Overlap with `minify-js`'s planned compression passes — decide the owner per pass
  before implementing ([roadmap](../status/roadmap.md#5-product-programs)).

## Pass ownership vs minify-js

The roadmap "micro-optimization" list (nullish/`typeof`/`undefined` canonicalisation,
`return undefined`→`return`, `if/else return`→conditional, shorthand properties, …)
was decided **per pass** and, as of 2026-07-23, all implemented items landed in
`minify-js` as AST peephole passes, because each is purely syntactic or needs only
`semantic-js` *resolution* (not dataflow). The full decision table and per-item
rationale live in
[minify-js § Pass ownership](./minify-js.md#pass-ownership-minify-js-vs-optimize-js);
this page is the optimize-js-side pointer to avoid re-deciding.

`optimize-js` keeps the transforms that genuinely need the IL/SSA/CFG: value
numbering, dataflow DCE, branch folding, copy cleanup, and CFG pruning (above). The
one roadmap item that is a natural fit here rather than minify-js is **cross-statement
`return`-chain flattening** without an explicit `else` (`if (t) return a; return b;`
→ `return t ? a : b;`), which falls out of the `decompile/structurer` region
analysis; it is not yet claimed. Do not fork the syntactic peepholes into optimize-js
(one-semantics bet, [vision #4](../vision.md#the-hypotheses-falsifiable-bets)).
