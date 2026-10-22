# Compiler theory: the correct way, mapped to this codebase

This page states the computer-science foundations each layer rests on, why those are
the *right* foundations for JS/TS, and what "completing the implementation rigorously"
means in each area. It is the theory companion to
[architecture/engine.md](../architecture/engine.md): engine says *what runs*; this page
says *why it is correct* and names the invariants that keep it correct. When
implementing, cite the relevant section; when a change has no theory home here, that is
a smell — either find the home or extend this page deliberately.

## 1. Parsing: recursive descent is the right call

JavaScript is not LR-friendly. Its grammar is context-sensitive in ways that punish
table-driven parsing:

- **Lexer feedback**: `/` is division or a regex literal depending on parser state;
  template literals nest lexing modes; JSX switches tokenization entirely. Hence
  `lex_next(mode)` with explicit `LexMode` driven by the parser (`parse-js/src/lex/`).
- **Cover grammars**: `(a, b)` is a parenthesized expression *or* arrow parameters;
  `{a}` is a block or object pattern depending on continuation. The spec itself defines
  these as cover productions to be reinterpreted; a hand parser does the natural thing —
  parse the cover form, then reinterpret (see `parse/expr/pat.rs` and the
  `ParenthesizedExpr` assoc marker preserved for downstream syntax-sensitive rules).
- **ASI** (automatic semicolon insertion) requires token-boundary and newline context —
  modeled explicitly via `AsiContext` in `ParseCtx` rather than grammar hacks.
- **TS ambiguities**: `f<T>(x)` (call with type args vs comparison chains), arrow
  return types, `satisfies`/`as` postfix forms — all need bounded lookahead/backtrack
  that recursive descent expresses directly.

Expressions use precedence climbing (Pratt-style) over an operator table
(`parse-js/src/operator.rs`) — the standard way to keep a hand parser's expression core
small and data-driven.

Error strategy: two regimes, deliberately. `Dialect::Ecma` is strict — reject exactly
what the spec rejects (needed for test262-parser's `fail/`/`early/` corpora). TS
dialects prefer TypeScript-style recovery, because the checker wants an AST even for
mildly broken input. **Correctness criterion**: the parser is judged by differential
conformance (TS corpus + test262), not by taste; the gap tracker lives at
`parse-js/notes/syntax_gaps.md`.

Rigor still owed (see [roadmap](../status/roadmap.md)): spec "early errors" are only
partially covered at parse time; several are deferred to binding (e.g. strict-mode
octal via assoc markers — a sound factoring, but each deferred early error must be
owned by *some* layer, and the ownership table should be explicit).

## 2. Name resolution: environments, hoisting, and three namespaces

The binding model is textbook lexical scoping made spec-faithful:

- **Two-phase binding** (`semantic-js::js::declare` then `resolve`) implements
  hoisting correctly by construction: pass one allocates scopes and declares symbols
  (vars/functions hoisted to the nearest closure; lexicals recorded with TDZ), pass two
  resolves uses against the finished environment chain. One-pass binders inevitably
  special-case hoisting; two-phase makes it structural.
- **TDZ** is modeled as a static approximation (a use is `in_tdz` until the binding's
  initialization point in source order) — exactly the right compile-time shape; actual
  TDZ is a runtime property, which is why `bind_js_for_runtime` suppresses TDZ
  diagnostics and lets the VM raise them if execution reaches a violating access.
- **Annex B block functions** get the spec's dual-binding treatment (block binding +
  hoisted var binding, linked so renamers keep them textually consistent) —
  a sloppy-mode legacy that must be modeled, not wished away.
- **Dynamic-scope hazards** (`with`, direct `eval`) are flagged per-scope rather than
  modeled: the honest choice — resolution inside them is undecidable statically, so
  consumers (minifier) must fail closed (disable renaming) rather than guess.
- **TypeScript's three namespaces** (value/type/namespace) are a `bitflags` mask per
  declaration kind, and **declaration merging** is a join: a name's declarations merge
  iff their namespace masks and kinds allow (interface+interface, namespace+value,
  enum merging, …), with deterministic declaration order. This is set-lattice
  thinking, and it keeps merging decidable and order-independent
  (`semantic-js/src/ts/model.rs`).

## 3. Types: what TypeScript's type system actually is

Getting this right matters because TS is *not* an ML-family system, and importing the
wrong theory produces the wrong checker.

- **Structural subtyping over possibly-infinite trees.** Recursive types
  (`interface T { next: T }`) denote regular infinite trees. The correct framework is
  **equi-recursive subtyping** (Amadio–Cardelli): assignability is a **coinductive**
  relation — the *greatest* fixed point — computed by assuming in-progress goals true
  and memoizing. That is precisely the `RelateCtx` design (pair cache + `in_progress`
  set + depth limits in `types-ts-interned/src/relate.rs`): "assume true on cycle" is
  not a hack, it *is* coinduction, and the termination argument is the finiteness of
  reachable `(src, dst, relation, mode)` pairs under memoization.
- **Hash-consing and canonical forms.** Unions/intersections form an
  associative-commutative-idempotent algebra with identities
  (`T | never = T`, `T & unknown = T`), which is what justifies canonicalization
  (flatten, sort by `type_cmp`, dedup) before interning — after which structural
  equality is pointer equality (`TypeId == TypeId`). Interning recursive structures is
  made possible by **not** expanding them: `TypeKind::Ref { def, args }` hashes by
  reference, mirroring how one hash-conses cyclic graphs via named back-edges.
- **Gradual typing.** `any` is the dynamic type: assignability with `any` is
  *consistency*, not subtyping, and consistency is deliberately non-transitive
  (`string ~ any ~ number` must not collapse). `unknown` is the true top, `never` the
  bottom, `void` its own TS-specific creature. These must be explicit cases in the
  relation, parameterized by `strictNullChecks` etc. — semantics switches are
  `CompilerOptions` inputs, never hidden globals.
- **Variance.** Structural relation of generics reduces to member-wise relation with
  polarity: covariant reads, contravariant parameter positions under
  `strictFunctionTypes`, and TypeScript's deliberate **method bivariance** exception —
  an intentional unsoundness for ergonomics that we replicate (mode flag
  `BIVARIANT_PARAMS`). Declared `in`/`out` annotations short-circuit structural
  variance measurement.
- **Type-level computation.** Conditional types are a lazy small-step rewrite system:
  distributive conditionals map over naked-type-parameter unions; evaluation defers on
  indeterminate checks (free type variables) — this deferral is what keeps evaluation
  sound under instantiation, and it must remain **cached and cycle-guarded**
  (`TypeEvaluator` + `EvaluatorCaches`, with the relate↔evaluate cycle broken by
  `RelationMode::SKIP_NORMALIZE`; see the completed conditional-types program in the
  [graveyard](../graveyard.md#completed-scratchpads)). Mapped types are indexed
  products over key sets (`keyof` algebra: `keyof (A|B) = keyof A & keyof B`);
  template-literal types denote regular languages, so matching a string literal
  against one is automaton membership — implemented with explicit state/depth budgets
  (`RelationLimits::max_template_*`) because the naive product construction explodes.
  `infer` positions are one-sided matching (pattern unification against a ground
  type), not full unification.
- **Inference is local, not Hindley–Milner.** TS deliberately avoids global
  unification: subtyping + overloading + conditional types make principal types
  non-existent in general. The correct model is **local type inference**
  (Pierce–Turner) with **bidirectional checking** (synthesize ⇒ / check ⇐, in the
  Dunfield–Krishnaswami tradition): contextual types flow down (lambda parameters,
  object literals), synthesized types flow up, and generic call inference gathers
  variance-directed candidate bounds per type parameter, then picks per TS's rules
  (`check/infer.rs`, `check/instantiate.rs`). Overload resolution is ranked trial
  checking in declaration order — deterministic, with diagnostics explaining rejection
  (`check/overload.rs`).
- **Literal types and widening.** Fresh literal types widen at mutable positions
  (`let` vs `const`), contextual types suppress widening, `as const` freezes —
  a small flow of "freshness" metadata that must be threaded, not recomputed
  (`check/widen.rs`; object-literal freshness drives excess-property checks).

### The TypeScript cornerstones

The behaviors that define "rigorous" for real-world code — each must be implemented or
explicitly documented as unsupported (absorbed from `AGENTS.md`; use as the litmus
checklist): const contexts & `satisfies`; object-literal freshness/excess-property
checks and their suppressions; union/intersection normalization identities; `keyof`
duality; distributive conditionals; indexed access over unions with
`noUncheckedIndexedAccess`; mapped-type modifier propagation and `as` remapping;
`strictFunctionTypes` variance with the method exception; overload selection;
`private`/`protected` nominality (same-declaration origin — implemented via
`RelateHooks::is_same_origin_private_member`); instance vs static sides; `this` typing;
and control-flow narrowing as core language behavior (next section).

**Litmus ladder (started 2026-07-24; widened 2026-07-25):** curated small fixtures +
assertions live at `typecheck-ts/tests/litmus/cornerstone_*` and
`typecheck-ts-harness/fixtures/cornerstones/` (difftsc).

| Cornerstone | Litmus dir / difftsc case | Status |
| --- | --- | --- |
| const contexts & `satisfies` | `cornerstone_const_satisfies` / `const_satisfies` | litmus + difftsc green (TS2322 on property key) |
| freshness / excess-property | `cornerstone_excess_props` / `excess_props` | litmus + difftsc green (TS2353 on property key) |
| CFA narrowing | `cornerstone_cfa_narrowing` / `cfa_narrowing` | litmus + difftsc green (primitive→`String`/`Number` members) |
| distributive conditionals | `cornerstone_distributive_conditionals` / `distributive_conditionals` | litmus + difftsc green |
| `keyof` duality + mapped/`as` | `cornerstone_keyof_mapped` / `keyof_mapped` | litmus + difftsc green |
| overload selection | `cornerstone_overload_resolution` / `overload_resolution` | litmus + difftsc green (TS2769 on arg span) |

Remaining (no litmus yet): union/intersection normalization identities;
indexed access + `noUncheckedIndexedAccess`; mapped modifier propagation edge
cases beyond optional/`as`; `strictFunctionTypes` method bivariance;
`private`/`protected` nominality; instance vs static sides; `this` typing.
Graduate via difftsc baselines (drop xfail on XPASS).

## 4. Flow analysis: abstract interpretation, honestly scoped

Narrowing is a forward dataflow analysis — abstract interpretation over a per-binding
lattice of types:

- **Domain**: for each `FlowKey` (binding or discriminant path like `x.kind`), the
  abstract value is a `TypeId` refining the declared type. Facts come from guards:
  `typeof`, `instanceof`, `in`, literal equality, truthiness, user-defined predicates
  (`x is T`), assertion functions (`asserts x`), discriminant checks
  (`check/flow_narrow.rs` implements each as a fact-transformer producing
  truthy/falsy/assertion fact sets).
- **Join** at merge points is type union — the lattice join. **Kills**: assignment
  resets a key to its declared/widened type; narrowing must never survive a write it
  can't see through.
- **Termination**: the abstract domain reachable from a body's syntax is finite
  (types mentioned + finite narrowing operators), and joins are monotone, so the
  fixpoint terminates; loop analysis re-processes blocks until stable
  (`FlowBodyChecker::process_block` over the CFG from `check/cfg.rs`) with explicit
  budgets as a backstop — the same belt-and-suspenders (mathematical argument + hard
  limit) used in the relation engine.
- **Deliberate unsoundness, inherited on purpose**: TS ignores aliasing between
  narrowed paths and mutation-through-callbacks. We match TS (parity goal), not
  soundness maximalism — divergence from `tsc` here is a bug *even when we'd be
  "more correct"*. Path-sensitivity is bounded (no exponential path splitting; states
  merge at joins), matching both TS behavior and complexity sanity.

## 5. Incremental computation: memoized function database

Salsa (0.18) is the formal core: computations as **pure functions over revisioned
inputs**, with dependency tracking and revision-validation — the Adapton /
"Build Systems à la Carte" model (early cutoff + minimality). The engineering theory
that makes it work here:

- **Granularity is a complexity dial**: per-body queries make invalidation traces
  short and memo tables small; per-expression tracking would trade constant-factor
  wins for asymptotic bookkeeping loss. (Bet #2 in the [vision](../vision.md).)
- **Early cutoff needs stable outputs**: content-addressed IDs and canonical
  orderings mean an edit that doesn't change a def's `DefPath`/type leaves downstream
  queries untouched even though upstream re-ran — determinism and incrementality are
  the same investment ([determinism](../architecture/determinism.md)).
- **Firewalling**: coarse queries whose outputs rarely change (module graph, export
  maps) shield the volatile leaves (bodies) from most edits.

## 6. SSA optimization (`optimize-js`)

Classic Cytron et al. pipeline, correctly ordered: lower to IL (`il/inst.rs`) → basic
blocks → CFG → dominator tree (`dom/`) → φ-insertion at dominance frontiers
(`ssa_insert_phis.rs`) → rename (`ssa_rename.rs`) → optimize → φ-elimination with
copy-coalescing on exit (`ssa_deconstruct.rs`). Passes are the standard monotone set:
dominance-based value numbering (GVN as congruence-closure over the dominator tree,
`optpass_dvn.rs`), trivial DCE (use-count driven), impossible-branch pruning
(constant conditions → CFG simplification), redundant-assign elimination, CFG pruning —
run to a fixpoint via `PassResult` change-tracking. Decompilation back to JS is the
interesting inverse problem: structuring a CFG into `if`/`while`/`break` (relooper
lineage — `decompile/structurer.rs`) plus register allocation over lexical lifetimes
for variable naming (`decompile/regalloc.rs`; the lifetime model is documented in
[crates/minify-js § lexical lifetimes](../crates/minify-js.md#lexical-lifetimes-variable-slot-reuse),
which shares the theory).

JS-specific caveat the pipeline must respect: almost everything can throw and almost
every expression can have effects (getters, valueOf, proxies). Effect conservatism is
the default; `eval/` (abstract evaluation of `Const`s) whitelists what it can prove.

## 7. The VM: spec-shaped semantics, precise GC

- **Spec-shaped interpreter.** ECMA-262 is written as an operational semantics
  (abstract operations + completion records). `vm-js` mirrors it: `spec_ops.rs`,
  `Completion::{Normal, Throw, ...}` (`exec.rs`), environment records distinct from JS
  objects, realms/intrinsics, job queues and microtasks for promises. The payoff is
  auditability — code reviewable against spec steps — and test262 as a direct oracle.
  Performance tiers (bytecode, inline caches, JIT) come *later*, behind the same
  observable semantics ([vision bet #5](../vision.md#the-hypotheses-falsifiable-bets)).
- **GC theory.** Precise, non-moving mark-sweep: handles are `{index, generation}` so
  stale access is *detectable* (`VmError::InvalidHandle`) rather than undefined
  behavior — generation-checking is the classic slot-reuse safety trick. Rooting is
  explicit and dual: RAII stack scopes (`Scope`) for temporaries, persistent roots for
  embedder globals; **handles are not roots** (deliberate, enables weak wrapper
  caches — the WebIDL layer's `WeakGcObject` pattern; see
  [crates/vm-js](../crates/vm-js.md#webidl-host-objects-rooting-rules-and-wrapper-caches)).
  Host data participating in the object graph must trace its JS edges — the classic
  embedder correctness obligation.
- **Cooperative scheduling**: fuel/deadline budgets + interrupt tokens checked at
  `Vm::tick` — the standard embedding answer to untrusted/unbounded JS, chosen over
  preemption for determinism and simplicity.

## 8. Completing the implementation rigorously

The doctrine for finishing (and the test of "done") — each item is a standing rule,
not a phase:

1. **Oracles over intuition.** A checker feature is complete when the relevant
   conformance slice + difftsc agree (codes and spans, normalized), not when its unit
   tests pass. A VM feature is complete when its test262 slice passes. Establish the
   baseline *first* (current pass-rates are unmeasured on this machine — roadmap item
   zero), then ratchet with `--fail-on new` so the number only moves up.
2. **Every recursive algorithm carries its termination story** (guard + memo + comment
   + fuzz where feasible). `fuzz_type_graph`'s invariant — arbitrary cyclic type graphs
   must evaluate/relate without panic or divergence — is the model; body checking and
   the emitter deserve the same treatment.
3. **Properties as tests**: canonicalization idempotence (`canon(canon(t)) == canon(t)`),
   relation coherence (assignable(a,b) stable under canonicalization), parse→emit→parse
   round-trip equality, SSA-in/SSA-out semantic equivalence on megatest programs,
   thread-count invariance of all outputs.
4. **Parity gaps are declared, not discovered.** Deliberate divergences from `tsc` live
   in expectation manifests + a wiki note with rationale; anything else diffing red is
   a bug. The same for spec deviations in the VM.
5. **No feature lands without its semantics switch audited** — which `CompilerOptions`
   affect it, and does its query signature record them?
6. **Order of work follows the dependency lattice**: green workspace → deterministic
   parallel substrate (the deadlock fix) → salsa-first checking → cornerstone-by-
   cornerstone conformance ratchet → performance program. The phased plan with
   acceptance criteria lives in [status/roadmap.md](../status/roadmap.md).

## References

The load-bearing literature, for orientation (choose these over training-data
folklore): Amadio & Cardelli, *Subtyping recursive types* (equi-recursive subtyping);
Pierce & Turner, *Local Type Inference*; Dunfield & Krishnaswami, *Bidirectional
Typing* (survey); Cousot & Cousot, *Abstract Interpretation* (framework behind CFA);
Cytron et al., *Efficiently computing SSA form*; Briggs et al. on value numbering;
Ramalingam & Reps on incremental computation, plus Hammer et al.'s *Adapton* and
Mokhov et al., *Build Systems à la Carte* (salsa's lineage); Siek & Taha, *Gradual
Typing* (the `any` consistency relation); ECMA-262 (the VM's ground truth); the
TypeScript compiler source (vendored as a submodule) as the behavioral oracle where the
spec is silent — TS has no formal spec, which is precisely why difftsc exists.
