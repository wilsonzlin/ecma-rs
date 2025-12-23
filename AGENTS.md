# AGENTS.md — TypeScript Type Checking for ecma-rs (from-scratch “ideal” design)

This document is the **authoritative architecture + implementation playbook** for adding **comprehensive, rigorous TypeScript type checking** to this repository.

Assumptions:
- You have **full ownership** of the entire codebase (parser, symbols, optimizers, minifier, workspace layout).
- **Backwards compatibility is not a constraint.**
- The TypeScript compiler codebase (submodule under `parse-js/tests/TypeScript/`) is a **reference oracle**, not a design template.
- You may **skip/defer** features with poor complexity/value, as long as the resulting checker is **polished, correct, fast**, and covers the **95% case** extremely well.

Primary outcome:
- Downstream Rust code can load a set of TS/JS files, **type-check them**, and **query types** for:
  - every named symbol (values/types/namespaces)
  - every expression (optionally, for AOT compilation / optimization)
  - every property/signature (for structural typing)
  - diagnostics with spans and rich context

Secondary outcomes:
- **Incremental-ready** architecture (query-based, revisioned inputs, dependency tracking).
- **Parallel by design** (safe concurrent checking across files/bodies).
- Predictable performance and memory (interning, canonicalization, bounded caches).

---

## Non-negotiable design principles

1. **Determinism**
   - Same inputs → same outputs, regardless of thread scheduling.
   - Canonicalize sets (union members, object members, overload sets) with stable ordering.

2. **Cycle-safe by construction**
   - Types, symbols, and relations are cyclic in TS; the system must not recurse infinitely.
   - Every “expand/relate/normalize” operation must have:
     - recursion guards
     - memoization
     - explicit “in-progress” markers where needed

3. **Incremental through queries**
   - Build a query database (Salsa-style) where every derived artifact is a pure function of inputs.
   - Prefer *coarse-grained* queries (per file / per def / per body), not per-expression queries.

4. **Parallel without shared mutability**
   - Shared global state should be **immutable** (behind `Arc`) after construction.
   - Mutable caches must be **sharded** or **thread-local**, never a single global lock.

5. **Two-level architecture**
   - **Global**: symbols, exports, type declarations, `.d.ts` libs, module graph.
   - **Local** (per function/class/static init): control flow, contextual typing, inference, narrowing.

6. **Ergonomic public API**
   - Downstream users should not see internal complexity.
   - Provide a small set of stable concepts: `Program`, `FileId`, `DefId`, `TypeId`, `Diagnostic`.

---

## Target architecture (north star)

Pipeline (conceptual):

```
Text (files) ──► AST (parse-js: `Node<T>` + `Loc`)
                              │
                              ├─► HIR lowering (stable DefIds, bodies, modules)
                              │
                              ├─► Binder (scopes, symbols, imports/exports, merging)
                              │
                              └─► Checker (types, relations, inference, flow)
                                        │
                                        └─► Typed IR / side tables + diagnostics
```

Key idea: **`parse-js` AST is the canonical syntax model**, HIR is stable-ish for *definitions*, and type-checking is driven by **incremental queries** (with invalidation at least at the file/def/body granularity, even without incremental parsing).

---

## Workspace layout (recommended)

This project is not “just type checking”; it is a full JS/TS toolchain (parser, semantics, optimizer, minifier, tooling). In the **best long-term end-state** (no backwards-compat constraints, one-shot rebuild), TS type checking should not be “bolted on” to existing semantics. Instead, we should converge the entire repo on a single, deterministic, lock-minimal **semantic foundation** shared by:
- `typecheck-ts` (full TS binder + checker)
- `optimize-js` (value-namespace-only mode)
- `minify-js` (renaming + semantics-aware transforms)

```
ecma-rs/
├── parse-js/                  # existing: TS/JS parser + AST + Loc
├── semantic-js/               # new: unified, deterministic semantics (scopes/symbols/modules/exports); replaces symbol-js
├── optimize-js/               # existing
├── minify-js/                 # existing
├── emit-js/                   # new: deterministic JS emitter/printer (HIR/IR -> JS), shared by minify/opt tooling
├── hir-js/                    # new: lowering from parse-js AST → HIR (DefId/BodyId/ExprId)
├── types-ts/                  # new: pure type representation + interner + relations (no AST refs)
├── typecheck-ts/              # new: checker + diagnostics + public API surface (uses hir-js + semantic-js + types-ts)
├── typecheck-ts-harness/      # new: conformance + differential testing vs tsc (CLI/binary + lib helpers)
├── diagnostics/               # new: shared Diagnostic model + rendering + utilities (used repo-wide)
└── Cargo.toml
```

Notes:
- Keep `parse-js` as the single source of syntax truth; **do not rewrite the parser** (it is already high-coverage and fast).
- Keep type representation **pure** and reusable (no AST references).
- Prefer a **single** semantics layer (`semantic-js`) used by optimizer/minifier/typechecker (one-shot end-state). Do not maintain two competing binders long-term.

## Fit to this repo (integration boundaries)

- **`parse-js`**: the canonical TS/TSX/JS parser + AST. The type checker consumes this AST; **no new syntax tree is required**.
- **`semantic-js`**: the unified semantic foundation (scopes, symbols, module graph, merging, exports). It supersedes `symbol-js` and becomes the semantics API used by all downstream crates.
- **`optimize-js` / `minify-js`**: today they require `compute_symbols()` and should continue to work without a TS type checker. Type checking must be **opt-in** and should not become a mandatory dependency edge for minification.
- **Typed outputs**: for downstream AOT compilation, prefer producing a typed HIR/IR (and location→ID mappings) rather than mutating/annotating the AST in-place.

## Repo-wide modernization (strongly encouraged)

With full ownership (no backwards-compat constraints), prioritize these hygiene fixes early because they prevent long-term drift:

- **Standardize “source text” APIs**
  - Prefer `&str` for TS/JS source (valid UTF-8 is required for correct identifier handling).
  - Avoid having some crates/tests/docs pass `&[u8]` while the parser expects `&str`. Pick one and enforce it via doctests + CI.
- **Make workspace build/test green**
  - Ensure `cargo check --workspace` and `cargo test --workspace` succeed (or document intentionally excluded crates/targets).
  - Treat doc examples as compile-tested (doctests) for public APIs.
- **Deterministic + lock-minimal semantics**
  - Avoid `Arc<RwLock<...>>` as the default representation for scopes/symbols; prefer immutable arenas + `ScopeId`/`SymbolId` indices.
  - Avoid non-deterministic ID allocation (atomics across parallelism) for anything that affects outputs/caches.
- **Single diagnostics story**
  - One `Diagnostic` model (codes + spans + labels + notes) used consistently across parsing, binding, checking, and tooling.
- **Stabilize internal IR boundaries**
  - `parse-js` produces AST; `hir-js` produces stable IDs; all semantic/type/opt passes operate on HIR + side tables.
  - Avoid downstream crates pattern-matching deep AST structures in many places (that leads to drift/rot).

---

## Core data model

### File identity

- `FileId(u32)`: stable within a `Program`.
- `ModuleId(u32)`: module graph node, usually 1:1 with `FileId` unless virtual modules are used.
- `TextRange { start: u32, end: u32 }`: byte offsets in UTF-8 source (TS uses UTF-16 in APIs; we do not).
- `Span { file: FileId, range: TextRange }`: used everywhere in diagnostics.

### Syntax layer (existing, high-coverage)

This repo already has a rigorous TS/TSX/JS parser in `parse-js` producing a typed AST built from:
- `Node<T> { loc: Loc, stx: Box<T>, assoc: NodeAssocData }`
- `Loc(start, end)` as UTF-8 byte offsets

Policy:
- Treat `parse-js` as **done** and as the canonical syntax model.
- Do not introduce a second syntax tree (rowan/green-tree) unless you are explicitly pursuing fine-grained incremental parsing (a separate, optional project).
- When introducing multi-file checking, wrap ranges as `Span { file: FileId, range: TextRange }`.

Integration note:
- `NodeAssocData` already supports attaching thread-safe per-node data (`Any + Send + Sync`) and is used today by `symbol-js` to associate scopes; in the end-state it should carry small IDs/handles produced by `semantic-js`/`hir-js` (not lock-backed scope objects).
- Prefer HIR IDs + side tables for bulk type data; only attach small handles (e.g., `ExprId`, `DefId`) when needed for mapping back to source nodes.

### HIR layer (semantic-friendly)

HIR is a simplified, typed-friendly representation:
- resolves syntax sugar into a small set of node kinds
- assigns **stable-ish IDs** to *definitions* (not every expression)

Key IDs:
- `DefId`: stable identifier for a definition (module item, type alias, interface, class, enum, function, variable, namespace, import binding).
- `BodyId`: identifier for an executable body (function body, initializer, class static block).
- `LocalId`: local within a body (not stable across edits; cached per-body).

Stability strategy:
- `DefId` is derived from a **DefPath**:
  - module path + name + kind + disambiguator (ordinal among same-name defs)
- `BodyId` is derived from the owning `DefId` + body kind.
- If a definition is edited structurally, only dependent queries invalidate.

---

## Incremental query engine (required)

Build a query DB (Salsa-2022 recommended; a custom engine is acceptable only if it supports):
- revisioned inputs
- dependency tracking
- parallel query evaluation
- cancellation (optional) and bounded memory

### Inputs (examples)

- `file_text(FileId) -> Arc<str>`
- `file_kind(FileId) -> FileKind` (TS/TSX/JS/JSX/DTS)
- `module_resolve(from: FileId, spec: Arc<str>) -> Option<FileId>` (provided by host)
- `compiler_options() -> CompilerOptions` (strictness, target, lib set, etc.)

### Derived queries (coarse-grained)

- `parse(FileId) -> Node<TopLevel> + ParseDiagnostics` (via `parse-js`; diagnostics are `SyntaxError`s)
- `hir(FileId) -> HirFile` (includes DefIds, bodies, item map)
- `module_graph(Program) -> ModuleGraph` (imports/exports edges)
- `bind(FileId) -> BoundFile` (scopes, symbols, exports)
- `global_symbols(Program) -> GlobalSymbols` (merged view)

Type checking queries:
- `type_of_def(DefId) -> TypeId` (declared type of a symbol/decl)
- `check_body(BodyId) -> BodyCheckResult` (types side tables + diagnostics)
- `exports_of_module(ModuleId) -> ExportMap`

Critical rule:
- **Do not** model “type of expression at node X” as a global query per node. That creates too many fine-grained dependencies and kills performance.
- Instead: `check_body(BodyId)` performs one pass over a body and produces a side table `ExprId -> TypeId` for that body.

Parallelism:
- `check_body` can run in parallel across bodies/files.
- DB must be `Send + Sync` and use sharded locks internally (or thread-local memoization where possible).

---

## Memory model (no GC, arena + interning)

### Persistent structures (shared, `Arc`)
- parsed ASTs (parse-js `Node<TopLevel>` and children)
- HIR for each file (mostly immutable)
- global symbol tables (immutable snapshots per revision)
- type store (interned, append-only per revision; may be revisioned via DB)

### Ephemeral per-body arena

For `check_body`:
- allocate constraints, flow graphs, temporary vectors in a `bumpalo::Bump`
- free all at end of query

Rationale:
- body checking allocates a lot of short-lived structures (constraints, worklists, narrowed types).
- arena allocation eliminates allocator overhead and improves locality.

### Interning

Use interners for:
- strings (`SymbolName`, property keys, module specifiers)
- types (`TypeId`)
- object shapes / members (`ShapeId` / `ObjectId`)
- template literal fragments (optional)

Interning requirements:
- canonicalize before interning (esp. unions/intersections)
- stable hashing and equality (cycle-safe; see below)

---

## Binder / semantic model

TypeScript has **three namespaces**:
- value namespace
- type namespace
- namespace namespace (a.k.a. “namespace” / “module” space)

Every name resolves in one or more namespaces depending on context.

### Symbols

Represent symbols as stable IDs:
- `SymbolId(u32)` with a kind and namespace mask
- symbols point to one or more `DefId` declarations (for overload sets / merges)

### Declaration merging (supported, but bounded)

Support the high-value merges:
- interface + interface (same name)
- namespace + namespace (same name)
- value + namespace (function/class/enum merged with namespace)

Defer/skip:
- complex cross-file global augmentation
- module augmentation by ambient declarations (unless explicitly requested by host)

Implementation approach:
- binder produces a `SymbolGroup` per name with separate slots for each namespace
- merging is a pure operation producing a canonical merged view (deterministic order)

### Modules / imports / exports

We do **not** hardcode Node/TS module resolution in the checker.
Instead:
- downstream provides a `Resolver` (trait) that maps `(from_file, specifier) -> target_file`
- binder computes module graph + export maps based on resolved edges

This keeps the type checker usable in:
- build systems (Bazel/Buck)
- bundlers
- IDEs
- in-memory virtual files

### Replacing `symbol-js` with `semantic-js` (one-shot end-state)

`symbol-js` is valuable today for optimizers/minifiers, but its current shape is **not** an ideal semantic foundation for rigorous, parallel TS checking:
- it stores scopes as `Arc<RwLock<...>>` and associates full scope objects per AST node
- it uses symbol IDs that are explicitly documented as “opaque, ephemeral, and non-deterministic”

For **deterministic** parallel checking and stable caching, we want semantic IDs that are:
- stable within a `Program`
- deterministic across runs
- cheap to copy (`u32`/`u64` indices)

End-state design:
- Replace `symbol-js` with a new `semantic-js` crate providing an immutable, lock-free semantic layer:
  - stable IDs: `ScopeId(u32)`, `SymbolId(u32)`, `NameId(u32)`
  - arenas: `Vec<ScopeData>`, `Vec<SymbolData>`
  - stable, deterministic ordering for members/exports/overloads
  - attach `ScopeId` (not a lock-backed scope object) to AST nodes via `NodeAssocData` **only when needed**, or keep a side table keyed by `ExprId`/`DefId`
- `semantic-js` supports both:
  - **JS mode** (value namespace only, tuned for optimizer/minifier)
  - **TS mode** (three namespaces + merging + exports + `.d.ts` + module graph)
- `optimize-js`/`minify-js` consume `semantic-js` (JS mode) directly; `typecheck-ts` consumes `semantic-js` (TS mode).

---

## Type representation (`types-ts`)

### Core constraints

- Type equality must be **cheap**: compare `TypeId`.
- Structural comparisons must be **memoized** and cycle-safe.
- Representation must support:
  - unions/intersections
  - literal types
  - object types (members, signatures, indexers)
  - generics and instantiation
  - conditional/mapped/template literal/indexed access types
  - `unique symbol`, `readonly`, variance, `infer`

### Suggested representation

Types are interned into a `TypeStore`:

- `TypeId(u32)` references an interned `TypeKind`
- `TypeKind` is purely semantic (no spans, no AST pointers)

Key idea: **named/recursive types are references**, not expanded structures:
- `TypeKind::Ref(TypeRef)` where `TypeRef` points to a `DefId` + type args
- expansion is lazy and guarded

Object types:
- store as `ObjectId` (interned) pointing to a canonical “shape”
- shapes include:
  - properties (key → type + modifiers)
  - call signatures (overload set)
  - construct signatures
  - index signatures
  - “brand” flags (class instance vs plain object) if needed

Unions/intersections:
- canonicalize members:
  - flatten nested
  - sort by stable key
  - dedup
  - remove identities (`never`, etc.) and collapse where safe
- intern the canonical vector

### Cycles and hashing

Do **not** attempt to fully hash structural expansion of recursive types.
Instead:
- `TypeKind::Ref` hashes by `(DefId, type_args)` only
- structural types hash by their immediate shape ids and member type ids
- expansion uses explicit recursion guards + memoization (relation cache)

This mirrors how real compilers avoid “hash infinite structure.”

---

## Type relations (assignability/subtyping)

TypeScript’s core relation is “assignable to” (not purely subtyping in the PL sense).
We implement a small set of relations:
- `Assignable` (TS assignment compatibility)
- `Comparable` (for `==`/`===`-like comparisons if needed)
- `StrictSubtype` (optional, for diagnostics / narrowing)

### Relation engine requirements

1. **Pair cache**
   - `cache[(source, target, relation, mode)] = Result`
2. **In-progress markers**
   - on recursion, treat as “assume true for now” or use TS’s approach (depends on relation kind)
3. **Normalization on demand**
   - before comparing, normalize only what’s needed (avoid eager expansion)

### Special types semantics (must be explicit)

Decide and document:
- `any`: top/bottom-ish escape hatch (both assignable to/from almost anything)
- `unknown`: top type (everything assignable to it; it’s assignable only to itself/any)
- `never`: bottom type
- `void`: behaves like TS (not Rust `()`)
- `null`/`undefined`: depend on `strictNullChecks`

The checker must be parameterized by `CompilerOptions` that control these semantics.

---

## Type checking algorithm (`typecheck-ts`)

### Overall strategy

- Use **bidirectional typing**:
  - synthesize types (⇒) for expressions where possible
  - check against expected types (⇐) for contextual typing and inference
- Use **body-local inference**:
  - generic inference, contextual typing, and narrowing operate within `check_body`
  - export-level types are computed via `type_of_def`

### Bodies are the unit of work

`check_body(BodyId)` does:
1. build a control-flow representation (CFG/flow graph) for narrowing
2. do a typing pass that produces:
   - `ExprId -> TypeId`
   - `PatId -> TypeId`
   - `SymbolUse -> ResolvedSymbolId`
3. emits diagnostics

This is the unit that parallelizes well and caches well.

### Generic inference (constraints)

Implement inference as a constraint solver:
- gather constraints from:
  - call arguments vs parameter types
  - contextual function types for lambdas
  - destructuring patterns
  - conditional types / `infer` positions
- solve by:
  - collecting candidate types per type parameter
  - computing best common type / union where appropriate
  - respecting variance (in/out) annotations on type params

This should be explicit and testable.

### Overload resolution

Overload resolution must be correct for common code:
- rank candidates by:
  - arity and rest compatibility
  - contextual typing success
  - assignability of arguments to parameters
  - specificity (literal vs widened)
- provide good diagnostics when ambiguous

Defer:
- obscure corner scoring rules that rarely appear in real code, unless they break many tests

---

## Compiler options (semantic switches)

The checker must be parameterized by a `CompilerOptions` input in the query DB. **Changing options is a revisioned input** and must invalidate dependent queries.

Recommended baseline: default to a “strict” preset (similar spirit to TS `--strict`) and let downstream loosen it.

Options that materially affect semantics (non-exhaustive but high-impact):
- **`strictNullChecks`**: `null`/`undefined` treated as distinct types vs absorbed into everything.
- **`noImplicitAny`**: whether unconstrained/unknown inference defaults to `any` is an error.
- **`strictFunctionTypes`**: variance rules for function types (and the TS exceptions for methods/callback positions).
- **`exactOptionalPropertyTypes`**: `x?: T` is not the same as `x: T | undefined`.
- **`noUncheckedIndexedAccess`**: indexed access adds `undefined` unless proven present.
- **`useDefineForClassFields`** and **`strictPropertyInitialization`**: class field definite assignment + initialization checks.
- **`target` / lib set**: influences built-in types (DOM, ES202x) and sometimes syntax lowering.
- **`jsx`** mode + factory settings: affects typing of JSX elements/attributes.

Policy:
- Keep options surface relatively small at first, but **model them explicitly** (no hidden globals).
- Record option dependencies in query signatures so incremental invalidation is correct.

---

## TypeScript semantic cornerstones (must match tsc for “rigorous”)

If we claim “rigorous TS type checking,” these behaviors must be implemented (or explicitly documented as unsupported) because they affect vast amounts of real-world code.

### Widening, literals, and const contexts
- **`const` vs `let`**: `const x = 1` yields literal `1` (often), `let x = 1` widens to `number` (unless context prevents widening).
- **Contextual typing prevents widening**: `let f: (x: "a" | "b") => void = x => { ... }` should contextually type `x`.
- **`as const` / const assertions**: array/object literals become **readonly** with literal members (tuple inference, readonly properties).
- **`satisfies`**: checks assignability to a target type but preserves the expression’s inferred type (does not “force” it to the target).

### Object literals: freshness and excess property checks
- Fresh object literals are subject to **excess property checks** when assigned to non-empty object types.
- These checks are suppressed by:
  - index signatures
  - type assertions
  - intermediate variables (non-freshness)
- Excess property behavior must be deterministic and aligned with TS for common patterns.

### Unions, intersections, and normalization
- Canonicalization must preserve TS semantics:
  - `T | never = T`, `T & unknown = T` (and other identities where correct)
  - flatten nested unions/intersections
  - order members deterministically
- Important TS behavior:
  - `keyof (A | B) = keyof A & keyof B` (common keys only)
  - `keyof (A & B) = keyof A | keyof B`
- Intersection/object merges must be cycle-safe and avoid exponential blowups.

### Conditional types and distributivity
- Conditional types are **distributive** over unions when the checked type is a “naked” type parameter:
  - `T extends U ? X : Y` distributes if `T` is naked.
- Conditional evaluation must be lazy and cached; it is a major performance hotspot in TS.

### Indexed access, mapped types, and key remapping
- `T[K]` with `K` a union is (often) a union of property types (subject to optionality/index signatures).
- Mapped types must handle:
  - key iteration over unions
  - `as` key remapping
  - modifier propagation (`readonly`/`?`) and their removal

### Functions, variance, and overloads
- `strictFunctionTypes` variance should match TS *including its exceptions* (notably method bivariance rules).
- Overload resolution must:
  - pick the best signature deterministically
  - report useful “why none matched / why ambiguous” diagnostics

### Classes and nominal-ish checks
- While TS is structural, **`private`/`protected` members introduce nominal constraints**: compatibility requires originating from the same declaration chain.
- Model instance vs static side distinctly.
- `this` typing:
  - explicit `this` parameters
  - contextual `this` in methods/callbacks

### Control flow narrowing is core language behavior
- CFA is not a “nice to have”; it’s required for correctness in common code:
  - truthiness, `typeof`, `instanceof`, discriminants, `in`, user guards, `asserts`.

Implementation guidance:
- Maintain a curated “semantic litmus test” suite (small files) where each item above has explicit assertions and is diff-tested vs `tsc`.
- If a behavior is intentionally simplified, document it in this file under “Skip/defer” with rationale and a test label.

---

## Control flow analysis (CFA) and narrowing

Narrowing is not optional in TS. Implement early and integrate tightly with `check_body`.

### Representation

Prefer SSA-like tracking of “facts” at program points:
- build a CFG from HIR body
- compute a flow lattice of “type facts” per variable/reference

Narrowing sources (must support):
- `typeof x === "string"`
- `x instanceof C`
- `"prop" in x`
- discriminant checks (`x.kind === "foo"`)
- truthiness (`if (x)`, `x && ...`, `x ? ... : ...`)
- user-defined type guards (`function isFoo(x): x is Foo`)
- assertion functions (`asserts x is Foo`)

Approach:
- store `NarrowedType(var, point) = TypeId`
- lazily compute at uses (or compute forward with a worklist)

Keep it bounded:
- do not attempt path-sensitive exponential analysis; merge states at joins via union.

---

## Diagnostics

Diagnostics must be:
- precise spans (`Span { file, range }`)
- stable error codes (so tooling can depend on them)
- have “related” notes (e.g., candidate overloads)

Recommended structure:
- `Diagnostic { code: &'static str, message: String, primary: Span, labels: Vec<Label>, notes: Vec<String> }`

Design guidelines:
- never panic on bad input; emit diagnostics
- keep messages short; attach detail in notes/labels

---

## Logging, tracing, and internal errors (systematic)

### Logging/tracing

- Use [`tracing`](https://docs.rs/tracing) for all internal instrumentation.
- The **library crates must not install a global subscriber**. Only binaries (harness/CLI) do that.
- Instrument at coarse, high-value boundaries:
  - per-file: parse/bind/check
  - per-body: `check_body(BodyId)`
  - hot algorithms: assignability, instantiation, conditional-type evaluation
- Emit structured fields that make profiling/debugging easy:
  - `file`, `def`, `body`, `type_id`, `cache_hit`, `duration_ms`
- Add a `--trace`/`--profile` mode in `typecheck-ts-harness` to dump per-query timings and cache stats to JSON (for regressions + perf tracking).

### Errors vs diagnostics (contract)

Treat **diagnostics** as the output for user-program errors; reserve `Result::Err` for “the checker cannot proceed” failures.

- **User errors** (type errors, missing imports, invalid overload usage):
  - return `Ok(…)` and **emit diagnostics**
- **Recoverable internal errors** (e.g., host I/O errors, missing file text):
  - return a typed error (`HostError`) *and/or* convert to a diagnostic at the outer orchestration layer
- **Internal compiler errors (ICE)**:
  - do not panic in normal operation
  - if an invariant fails, convert to a diagnostic like:
    - code: `ICE0001`
    - message: “internal error: …”
    - note: include minimal reproduction hints + backtrace when enabled

Suggested structure:
- `enum FatalError { Host(HostError), Cancelled, OutOfMemory, Ice(Ice) }`
- `struct Ice { message: String, context: Vec<(String, String)> }`

---

## Public API (downstream ergonomics)

Expose a minimal, stable API from `typecheck-ts`.

### Host abstraction

Downstream supplies:
- file contents
- module resolution
- compiler options
- optional lib files

Example trait (conceptual):
- `trait Host { fn file_text(&self, file: FileId) -> Arc<str>; fn resolve(&self, from: FileId, spec: &str) -> Option<FileId>; fn options(&self) -> CompilerOptions; }`

### Program and queries

`Program` is the main entry:
- constructed from a `Host` + root files
- builds module graph, binds, checks

Must support:
- `program.check() -> Vec<Diagnostic>`
- `program.type_of_def(def: DefId) -> TypeId`
- `program.type_of_expr(body: BodyId, expr: ExprId) -> TypeId` (via body side tables)
- `program.symbol_at(file: FileId, offset: u32) -> Option<SymbolId>`
- `program.exports_of(file/module) -> ExportMap`

Provide convenient wrappers:
- pretty-print types (`TypeDisplay`)
- serialize query results (`serde`) for downstream caching

---

## Testing strategy (comprehensive)

### 1) Upstream TypeScript test suites

Use the TypeScript submodule as the source of truth:
- parser tests
- binder/name resolution tests
- type checker tests

Use the already-vendored submodule at `parse-js/tests/TypeScript/` as the primary corpus. For speed and stability, maintain a curated subset + optional snapshots under `typecheck-ts-harness/` (and shard/parallelize heavily).

Create a harness that:
- runs tests in parallel
- records pass/fail categories (parse error vs bind error vs type error mismatch)
- supports filtering and sharding

### Running tests (recommended commands)

- **Parser conformance (existing)**:

  - `cargo test -p parse-js --release --test conformance_runner`

  Notes:
  - the current parser runner skips `@filename:` multi-file tests; the typecheck harness must not

- **Type checker conformance (new)**:

  - `cargo run -p typecheck-ts-harness --release -- conformance --filter <glob-or-regex>`
  - `cargo run -p typecheck-ts-harness --release -- conformance --shard 0/16`

  Recommended harness flags:
  - `--json` (machine-readable output)
  - `--update-snapshots` (regenerate baselines for curated suites)
  - `--trace` / `--profile` (enable tracing + per-query timing dumps)

### 2) Differential testing vs `tsc`

When available (CI job with Node):
- run `tsc` on the same inputs
- compare:
  - diagnostics count + codes + spans (allow some normalization)
  - selected inferred types (for a curated subset)

Important:
- don’t attempt to match *exact* message text
- compare structured facts, not strings

### 3) Snapshot baselines (optional, recommended)

For stability and offline tests:
- generate `tsc` baselines (JSON) for a curated subset
- commit those snapshots
- run our checker and compare to snapshots

Baseline format recommendation:
- store **structured JSON**, not raw strings
- include:
  - `diagnostics: [{ code, severity, primary: {file, start, end}, labels: [...] }]`
  - optional: selected `types` facts for curated assertions (e.g. `type_of_symbol`, `type_of_expr`)

### 4) Property testing and fuzzing

- fuzz parser and HIR lowering (must not panic)
- fuzz type normalization and relation engine (must terminate)
- property: canonicalization idempotent (`canon(canon(t)) == canon(t)`)

---

## Performance engineering (make it measurable)

Add benchmarks for:
- parsing (TS/TSX)
- binding large lib sets
- checking real projects (import graph + many bodies)
- assignability stress tests (union/intersection heavy)

Instrumentation:
- per-query timings (Salsa has hooks; otherwise add tracing)
- cache hit rates for:
  - relation cache
  - type interner
  - instantiation cache

Targets (realistic):
- medium project (~50k LOC): < 500ms on a modern desktop CPU (release, warm caches)
- incremental re-check after local edit: < 50ms for affected bodies (warm caches)
- memory bounded by design (LRU for huge caches if needed)

---

## Explicit scope (what we support vs skip)

### Must support (comprehensive core)
- TS syntax + `.d.ts` parsing
- all mainstream type constructs (unions/intersections, generics, conditional/mapped, template literals, indexed access)
- structural object typing (properties, signatures, indexers)
- contextual typing for lambdas and object literals
- overload resolution for common cases
- control-flow narrowing (major patterns)
- declaration merging (high-value merges)

### May simplify (if complexity explodes)
- exact `tsc` error message wording
- rarely-used overload ranking corner cases
- exotic JSDoc-driven typing

### Skip / defer unless explicitly required
- full Node/TS module resolution (caller provides resolver)
- project references, watch mode
- `--allowJs` + JS-specific inference quirks
- emit `.d.ts`
- language-service protocol features (completions, rename) beyond basic symbol_at/type_of queries
- cross-package global augmentation/multi-project merging

---

## Implementation playbook (one-shot end-to-end)

Assume a “one-shot” rebuild with unlimited resources. The phases below are **internal decomposition**, not incremental shipping. The end-state is a coherent toolchain where parsing, semantics, type checking, optimization, and minification share stable IDs, diagnostics, and deterministic behavior.

### Phase A — Repo-wide foundations (non-negotiable)
- Standardize on **UTF-8 `&str`** source APIs across the repo; delete remaining byte-slice public APIs unless there is a compelling, measured reason.
- Introduce `diagnostics` crate and convert existing parse/bind/opt/minify errors to it:
  - `Span { file, range }` everywhere
  - stable codes + labels + notes
- Make the workspace **build/test green**:
  - eliminate drift/rot between crates by stabilizing AST/HIR boundaries
  - enforce `cargo check --workspace` and `cargo test --workspace` in CI
- Add `tracing` instrumentation policy and a `--profile` JSON output mode in `typecheck-ts-harness`.

### Phase B — Unified semantics (`semantic-js`) + stable IDs (`hir-js`)
- Implement `hir-js` lowering from `parse-js` AST:
  - stable-ish `DefId`/`BodyId`, per-body `ExprId`, and location→ID maps
- Implement `semantic-js` (replacing `symbol-js`) with:
  - deterministic, lock-free arenas (`ScopeId`/`SymbolId`)
  - JS mode (value namespace) and TS mode (three namespaces + merges + exports)
  - resolver-driven module graph
- Migrate `optimize-js` and `minify-js` to consume `hir-js` + `semantic-js` (JS mode).

### Phase C — Type system core (`types-ts`)
- Implement `TypeStore` + canonicalization + object shapes + refs
- Implement assignability/relations engine with memoization + recursion guards
- Implement type formatting + debug tooling (human + JSON)

### Phase D — Full TS checker (`typecheck-ts`)
- Implement binder-on-HIR (or reuse `semantic-js` TS mode) + export/import typing
- Implement `type_of_def` and `check_body` with:
  - bidirectional typing
  - generic inference + overload resolution
  - conditional/mapped/template literal/indexed-access types
  - CFA narrowing (major patterns) integrated into body checking
- Expose the public `Program` API and typed side tables suitable for AOT compilation.

### Phase E — Conformance, differential testing, and performance closure (`typecheck-ts-harness`)
- Run upstream TS suites (including multi-file `@filename:` tests).
- Add differential testing vs `tsc` (structured JSON facts).
- Add fuzz/property tests to guarantee termination and canonicalization idempotence.
- Profile and tune:
  - relation cache hit rates
  - instantiation cache
  - per-body allocations and hot paths

### Phase F — Typed optimization/minification (holistic)
- Thread type info into `optimize-js` for type-aware optimizations (optional but high leverage).
- Ensure `minify-js` can:
  - erase TS syntax safely
  - minify identifiers using `semantic-js` without capture
  - print minified JS deterministically via `emit-js` (stable formatting rules + parentheses correctness)

---

## Coding standards for agents

- **No global `RefCell`** or non-`Sync` state in anything that must run in parallel.
- Prefer `Arc`, immutable snapshots, and sharded caches (`DashMap`, `parking_lot` with sharding) where necessary.
- Keep “pure” logic in `types-ts` (no AST references).
- Every recursive algorithm must have:
  - depth limit or visited set
  - memoization
  - a termination story documented in code comments
- Tests are first-class: every bug fix should come with a regression test.


