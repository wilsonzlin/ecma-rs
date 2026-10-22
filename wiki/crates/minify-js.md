# minify-js (+ minify-js-cli, minify-js-nodejs)

The published minifier: extremely fast, single-file JS/TS minification. This is the
workspace's oldest product line (the repo's version/release tooling revolves around
it) and the origin of several design notes now absorbed here. (Absorbed from
`minify-js/README.md`, `notes/Name minification.md`, `notes/Lexical lifetimes.md`,
`notes/Textual compression.md`, 2026-07.)

## Goals (absorbed verbatim in spirit)

- Fully Rust for maximum compatibility with Rust programs and derivatives (FFI, WASM,
  embedded).
- Maximize single-core performance for simple, efficient scaling and easy integration.
- Single-input minification only; **no bundling**. TypeScript is handled by erasing
  type-only syntax, not by compilation.
- Prefer minimal complexity and speed over maximal configurability and last-percent
  compression.

Benchmarks vs esbuild et al. live in `bench/` (charts published per release at
`static.wilsonl.in/minify-js/bench/<version>/`).

## Pipeline

```
parse (parse-js, TS dialects accepted)
  → TS erasure/lowering (ts_erase.rs, ts_lower/)
  → JS binding (semantic-js js mode: scopes, hoisting/TDZ, hazards)
  → usage collection + name assignment + rename application (rename/)
  → emit (emit-js, minified profile; HIR backend, hard-error on unsupported syntax)
```

`minify(top_level_mode, source, output) -> Result<(), Vec<Diagnostic>>` — UTF-8 in,
structured diagnostics out. `TopLevelMode::{Global, Module}` (script vs module
semantics; module exports are never renamed).

**TS erasure** (`ts_erase.rs`, ~4.7k lines): strips type-only syntax and lowers
TS-only *runtime* constructs — `enum`, runtime `namespace`, `import =`/`export =`,
parameter properties — so output is always plain JS. `const enum` follows `tsc`
semantics by default (inline + erase); `TsEraseOptions { const_enum_mode:
ConstEnumMode::Runtime }` keeps runtime enums instead (surfaced in the Node API as
`preserveConstEnums: true`). Erasure diagnostics use `MINIFYTS####`.

**Renaming correctness**: identifier renaming is disabled whenever semantics could
change — scopes flagged by `semantic-js` as containing `with` or direct `eval` calls
(fail-closed, per the hazard-flag design). ES2022 arbitrary module namespace
identifiers (string-literal import/export names) are supported.

## Compression passes (`opt/`, `emit-minify` only)

With the default `emit-minify` feature, `opt::optimize` runs a set of AST-level
peephole passes between binding and renaming. Two pipelines iterate to a fixpoint;
the *post-bind* pipeline **re-binds at the start of every iteration** so
semantics-dependent passes always read fresh `semantic-js` scope/symbol
associations (a pass may synthesise new identifier nodes that carry no assoc until
the next rebind — DCE therefore always sees a rewrite's new uses one iteration
later, which the fixpoint absorbs). All passes **fail closed** in scopes flagged
with `with`/direct-`eval` hazards (and, for `undefined`-sensitive rewrites, in any
descendant of an `eval` scope, since nested closures capture the mutable
environment record).

Current passes:

- `const_fold` — constant evaluation/folding (incl. `typeof <const>`, logical/
  comparison folding).
- `prop_rewrite` — computed-member → dot (`o["a"]`→`o.a`), object-key
  canonicalisation, and object **shorthand** (`{a:a}`→`{a}`). `__proto__` is
  excluded: `{__proto__: x}` sets the prototype, whereas the shorthand/`["__proto__"]`
  forms define a plain own property — the semantics differ, so the shorthand and
  computed-string rewrites bail on that key. Shorthand is applied **post-rename** so
  it uses the final names.
- `stmt_rewrite` — control-flow → expression rewrites: dead-branch folding on
  constant `if` tests (with Annex-B function-declaration and `var`-hoist care),
  `if (t) a(); else b();` → `t?a():b()`, `if (t) a();` → `t&&a()`, and
  **`if (t) return A; else return B;` → `return t?A:B;`** (see traps below).
- `cf_rewrite` — drops a terminating `else` after an unconditional `return`/`throw`/
  `break`/`continue`, and trims unreachable statements after a terminator (preserving
  hoisted `var`/TDZ/Annex-B bindings as needed).
- `sem_rewrite` — resolution-gated rewrites (see traps below): nullish collapses,
  `typeof`/`undefined` canonicalisation, and trailing-`return` trimming.
- `dce` — removes unused declarations/imports (module mode) with side-effect
  preservation; `decl_combine` merges adjacent same-mode `var`/`let`/`const` decls;
  `cleanup` drops empty blocks/decls/statements and **unwraps safe bare blocks**
  (see traps below).

### Implemented micro-optimizations and their correctness traps

The "why" behind each guard (these are the exact traps that make the rewrites
non-trivial):

- **`return undefined;` → `return;`** and **trailing `return;` removal** (`sem_rewrite`).
  ASI-safe. `undefined` must be the unshadowed global (resolved-symbol-free id, and
  not inside/under an `eval` scope). Trimming a *trailing* bare `return;` is sound for
  **every** function kind — normal, async (resolves `undefined`), generator
  (`{value: undefined, done: true}`), getters, setters, and constructors (a bare
  `return;` still yields the constructed `this`, exactly like falling off the end).
  Only the final **direct** statement of a function body is trimmed, so returns that
  guard later code are never touched.
- **`undefined` → `void 0`** (`sem_rewrite`). `void 0` is the unshadowable spelling;
  disabled in `eval`/`with`-tainted scopes where `undefined` could be rebound.
- **`x === null || x === undefined` → `x == null`** and the De Morgan dual
  **`x !== null && x !== undefined` → `x != null`** (`sem_rewrite`). Sound because
  `null == undefined` and neither compares loosely-equal to anything else (ECMA-262
  Abstract Equality). Requires the **same resolved binding** on both sides: matching
  by `SymbolId` (not spelling) restricts this to plain identifiers, because member
  paths like `a.b` have observable getters that must not be read twice. `undefined`
  must be the global.
- **`typeof x === "undefined"` → `x === void 0`** (and the `!==` dual) (`sem_rewrite`).
  **ILLEGAL when `x` is undeclared**: `typeof x` tolerates a completely undeclared `x`
  and yields `"undefined"`, whereas a bare `x === void 0` read throws
  `ReferenceError`. Guarded by requiring a **resolved binding** for `x`. TDZ is
  unaffected (both forms throw for a `let`/`const` in its dead zone). **Only strict**
  input (`===`/`!==`) is rewritten: a loose `typeof x == "undefined"` is left alone,
  since `x == void 0` would also match `null`.
- **Object property shorthand** and **computed-member simplification** (`prop_rewrite`)
  — the `__proto__` trap above.
- **`if/else return` → conditional** (`stmt_rewrite`). `if (t) return A; else return B;`
  ≡ `return t ? A : B;` (t evaluated once, one branch value returned). Branches are
  recursed first, so `else if (…) return …` chains collapse **bottom-up** into a
  single nested ternary. Only value-bearing returns fold — a bare `return;` branch is
  declined (we never synthesise a `void 0` operand), and single-statement blocks
  around a return are transparent (they carry no block-scoped declarations).
- **Block unwrapping** (`cleanup`). A bare `{ … }` is spliced into its parent
  statement list (and a single-statement block in `if`/`while`/`with`/label position
  is replaced by that statement) only when safe:
  - **no** block-scoped declarations in the block's direct body (`let`/`const`/`class`/
    `using`/`await using`, including under a label — labels create no scope);
  - **no** function declarations (Annex B block functions hoist differently from a
    bare `function` as an `if` body in sloppy mode — never turn
    `if (c) { function f(){} }` into `if (c) function f(){}`);
  - **no** leading string-literal `ExpressionStatement` when unwrapping into a list
    (blocks have no Directive Prologue, but splicing a leading `"use strict"` into a
    function/script body would promote it into that prologue and can flip
    sloppy→strict). Parenthesized string literals are never directives and do not
    trip this guard. `var` is allowed (function-scoped; unwrap does not change its
    binding contour).

## Pass ownership (minify-js vs optimize-js)

Decision rule (from the one-semantics bet, [vision #4](../vision.md#the-hypotheses-falsifiable-bets)):
**purely syntactic, semantics-preserving-by-construction** rewrites live in
`minify-js` (AST peephole); **dataflow/CFG-dependent** transforms live in
`optimize-js` (IL/SSA). Per-candidate calls from the roadmap micro-optimization list:

| Candidate | Owner | Rationale |
|---|---|---|
| `return undefined`→`return` / trailing `return;` | minify-js | ASI-safe syntactic rewrite; no dataflow. |
| `undefined`→`void 0` | minify-js | Syntactic canonicalisation (unshadowable spelling). |
| `x===null\|\|x===undefined`→`x==null` (+ `&&`/`!==` dual) | minify-js | Local pattern rewrite; only needs binder *resolution* (same `SymbolId`), not flow. |
| `typeof x==="undefined"`→`x===void 0` | minify-js | Local rewrite gated on a resolved binding; no flow. |
| shorthand properties `{a:a}`→`{a}` | minify-js | Syntactic; applied post-rename. |
| `const`→`let` | **declined** (would be minify-js) | See below. |
| block unwrapping | minify-js | Syntactic cleanup; fail-closed on lexicals / Annex-B function decls / leading string literals (directive promotion). |
| `if/else return`→conditional | minify-js | Local, semantics-preserving-by-construction AST rewrite. optimize-js's decompiler *also* emits ternaries as a byproduct of CFG structuring, but the explicit peephole belongs here. Cross-statement return-*chains without an explicit else* (`if(t)return a; return b;`) are the natural optimize-js/structurer case, not yet claimed. |

### Declined / deferred

- **`const`→`let` (declined, fail-closed).** Reassigning a `const` is a runtime
  `TypeError` (observable), so converting to `let` silently turns a throwing program
  into a non-throwing one. Doing it *safely* requires whole-body write-analysis to
  prove the binding is never reassigned, and — per the same evidence behind the
  rejected [textual-compression](#rejected-textual-compression) policy — gzip/Brotli
  already compress repeated `const` keywords to near-nothing, so the post-compression
  win is negligible. Retry only with a measured post-compression benchmark. (Exported
  `const` is an additional, lesser trap: `export const` is a read-only live binding.)

## Name minification algorithm

(Absorbed from `notes/Name minification.md`.) The core idea — compute, per scope, the
set of names *inherited* (used-but-not-declared here), so assignment can give each
symbol the shortest name not colliding with anything it must coexist with:

- For each symbol usage, walk scopes from the use site up to and including the
  declaring scope; mark the symbol as **inherited** on every scope strictly below the
  declaration.

Worked examples preserved:

```js
// Inherited: bar, baz, top0, top1, top2.
let foo;
foo; bar; baz; top0;
{
  // Inherited: foo, baz, top1, top2.
  let bar;
  foo; bar; baz; top1;
  {
    // Inherited: foo, bar, top2.
    let baz;
    foo; bar; baz; top2;
  }
}
```

After minification the same structure becomes maximally short while avoiding captures —
the note's second ("obfuscated") example shows the assignment *outcome*: outermost
declarations get the shortest names, and each scope's inherited set constrains reuse:

```js
// Inherited: e, d, c, b, a.
let f;
f; e; d; c;
{
  // Inherited: f, d, b, a.
  let e;
  f; e; d; b;
  {
    // Inherited: f, e, a.
    let d;
    f; e; d; a;
  }
}
```

Implementation:
`rename/{collect_usages, assign_names, apply_renames}`; without the `emit-minify`
feature a `rewrite_source` path patches the original text instead of re-emitting.

## Lexical lifetimes (variable slot reuse)

(Absorbed from `notes/Lexical lifetimes.md` — design notes for declaration-merging /
slot-reuse optimizations; partially future work, and the same lifetime model
`optimize-js`'s decompiler register allocation uses.) The load-bearing observations:

- Assignments behave like fresh variables that optimally reuse a slot; analyzing
  lifetimes both shrinks var decls and exposes pointless unused assignments.
- **Loops**: if a variable's first in-loop appearance is an unconditional assignment
  before any use, it is loop-local (safe to clobber/reuse); otherwise its lifetime
  must extend to the loop end — first-appearance-as-use means the value crosses
  iterations, and reusing its slot would corrupt it.
- Compound assignments (`+=`, `??=`) are use-then-assign; plain `=` is assign (RHS may
  still use).
- **Destructuring** may be worth unpacking into individual assignments once names are
  minified (shorthands rarely survive renaming anyway), which also enables hoisting
  splits: `var {foo: [bar, {baz}]} = obj` → `var a = obj.foo, b = a[0], …`.
- **Nested closures make lifetimes infinite** — any capture (including class property
  initializers, which re-evaluate per construction) pins the variable forever; no slot
  reuse.
- **Branches**: the optimal grouping is global but per-branch solutions must stay
  locked; the pragmatic rule adopted — take the *maximum* lifetime across branches
  (suboptimal, simple, correct).
- Lifetime values are ordinal only — meaningful by comparison, not magnitude.

The stack-based numbering scheme (the note's full algorithm, preserved here since the
source note was deleted 2026-07-23):

- For each symbol assignment (IdentifierPattern): increment top of stack, and start a
  new lifetime on the symbol if its existing lifetime end is before.
- For each symbol usage (IdentifierExpr) not in a loop: increment top of stack.
- For each symbol usage (IdentifierExpr) in a loop, check the current lifetime's end:
  - same level (an unconditional assignment occurred earlier in the same loop) →
    increment top of stack;
  - otherwise, don't modify the stack — use the current loop's *end* lifetime as its
    lifetime.
- For each conditional: increment top of stack; push a fresh `0` per branch.
- For each loop: increment top of stack; push `0` before entering (marked in-loop);
  increment top again after exiting — so a loop has two lifetime values, start and end.

Worked puzzles preserved from the note (useful as future test fixtures for the pass):

```js
function foo() {
  var a, b = f(a), c = 2;

  a = 1;
  f(a);

  if (true) {
    let d = 1;
    a = 2;
    var e = 2;
  } else {
    a = 4;
    e = 3;
  }

  if (true) {
    e = 4;
    return;
  }
  f(e);

  for (;;) {
    var x = 2;
    a = a + 1;
    b++;
    c = 2;
  }

  f(b);
}
```

```js
// Assignments start new lifetimes.
var a, b;

a = a + (b = 2 * 4) // Lifetimes don't overlap: can technically become `a = a + (a = 2 * 4)`.

a = (b = 2 * 4) + a // Lifetimes overlap: can't be reduced to one (absent reordering tricks).
```

```js
// Without assignment-starts-lifetime, `x` would live pointlessly long across the calls.
x = 1;
foo();
bar();
baz();
x = 2;
```

```js
// Mental puzzle (nested loops/conditionals interacting with the loop rule).
if (foo) {
  for (;;) {
    if (bar) {
      for (;;) {
        x = 1;
      }
      x = 1;
    }
    x = 1;
  }
  x = 1;
}
```

```js
// Nested-closure usages are unknowable → infinite lifetime.
var x = 1;
(() => {
  if (Math.random() < 0.5) {
    x = 2;
  } else {
    setInterval(() => {
      x++;
    }, 1000);
  }
})();
var y = 2;
```

## Rejected: textual compression

(Absorbed from `notes/Textual compression.md`; also in the
[graveyard](../graveyard.md#textual-compression-in-the-minifier).) No aliasing of
well-knowns, no literal dedup, no `Object.assign` tricks, no `typeof`→helper
rewrites, no statement-pattern helper functions. Reasons, preserved: much more
expensive/complex minification; runtime cost via indirection that also defeats engine
optimizations; **almost always worsens gzip/Brotli** (the compressor already does
this job better); pollutes scope and weakens name minification; tricky correctness
(symbols, execution order). Constant/built-in aliasing was actually shipped once and
**removed** in minify-js commit `ff48b8b` — the empirical receipt behind the policy.

## Delivery surfaces

### CLI (`minify-js-cli`)

Stdin or `--input`, stdout or `--output`; `--mode global|module`; `--json` for a
versioned envelope (`{schema_version: 1, mode, output | diagnostics}`); human mode
renders diagnostics to stderr with 1 context line; `--color`/`--no-color` (default:
auto by TTY). Exit 0/1 per the
[severity policy](../architecture/diagnostics.md#diagnostic-vs-fatal-error). Invalid
UTF-8 is rejected early with a host diagnostic. Prebuilt binaries per release:
`static.wilsonl.in/minify-js/cli/<version>/<platform>/minify-js`.

### Node.js bindings (`minify-js-nodejs`)

Published to npm as `@minify-js/node`. Neon bindings: `minify(topLevelType: "global"|"module", src: string|Buffer, options?)
→ Buffer`; options include `dialect` and `preserveConstEnums`. Errors throw with
rendered diagnostics plus a structured `diagnostics` property.

### Release flow

The root `version` script (Node) bumps `minify-js`/`-cli`/`-nodejs` versions in
lockstep, rewrites README URLs, runs the full test suite, commits, tags `v<version>`,
publishes `minify-js` to crates.io (CLI and Node bindings are `publish = false`;
Node package ships via npm workflows), and pushes with tags. CI workflows `cli.yaml`
and `nodejs.yaml` build the distributable artifacts.

## Roadmap (absorbed "In progress" list from the README)

**Implemented** (see [Compression passes](#compression-passes-opt-emit-minify-only)
above for the passes and their traps): constant evaluation and folding;
unreachable/unused/redundant code removal (`dce`, `cf_rewrite`, `cleanup`);
declaration combining (`decl_combine`); `if`→conditional/logical rewrites and
**`if/else return` chains → conditional expressions** (`stmt_rewrite`); unwrap
string-literal computed members and **shorthand properties** (`prop_rewrite`);
**`x === null || x === undefined` → `x == null`** (and the `&&`/`!==` dual);
**`typeof x === "undefined"` → `x === void 0`**; **`return undefined` → `return`**
(and trailing-`return` trimming); `undefined` → `void 0` canonicalisation;
**safe bare-block unwrapping** (`cleanup`; lexical / Annex-B / directive-prologue
traps above).

**Declined / deferred**: `const` → `let` (declined, fail-closed —
[see above](#declined--deferred)). `void x` → `x, undefined` is subsumed by the
`undefined`→`void 0` canonicalisation direction already shipped (the classic size
win is spelling `undefined` as `void 0`, which the emitter path does; rewriting
`void <expr>` into a comma sequence is generally *longer* and was not pursued).

**Still open**: declaration reordering; single-use declaration inlining; explicit
errors on illegal code (duplicate declarations/exports); hoisting `let`/`const`;
paren unwrapping; cross-statement return-chains without an explicit `else`. Note the
overlap with `optimize-js` — the deeper (dataflow/CFG-dependent) of these belong to
the optimizer per the one-semantics bet; see
[Pass ownership](#pass-ownership-minify-js-vs-optimize-js) and coordinate before
implementing in both places ([roadmap](../status/roadmap.md#5-product-programs)).
