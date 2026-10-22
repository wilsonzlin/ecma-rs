# semantic-js

The unified semantics layer: scopes, symbols, and exports, defined once so the
minifier, optimizer, and type checker agree on the same model
([vision bet #4](../vision.md#the-hypotheses-falsifiable-bets)). It is the sole
semantics crate; the legacy `symbol-js` was removed entirely
([graveyard](../graveyard.md#symbol-js)). Two public modes live side by side —
deliberately in one crate so they cannot drift. (Absorbed from `semantic-js/README.md`
and crate docs, 2026-07.)

## JS mode (`semantic_js::js`)

Lexical scope tree + identifier resolution in the value namespace, for JS-only tooling
(`minify-js`, `optimize-js`, VM binding).

**Pipeline**: `declare()` walks a mutable AST, allocates `ScopeId`s/`SymbolId`s, and
attaches the enclosing `ScopeId` to every node's `NodeAssocData` (declarations also get
`DeclaredSymbol`); `resolve()` then resolves identifier expressions/patterns to their
nearest declaration, attaching `ResolvedSymbol { symbol, in_tdz }`. `bind_js` runs
both and returns `(JsSemantics, Vec<Diagnostic>)` with sorted `BIND####` diagnostics.
`bind_js_for_runtime` is the VM entry point: same binding, but **TDZ diagnostics
suppressed** — TDZ violations are runtime `ReferenceError`s that depend on which paths
execute, so a VM must bind-and-run and raise them only on actual violating access.

**Top-level modes** (`TopLevelMode`): `Module` (module scope acts as the `var`
closure); `Global` — top-level declarations intentionally *not* bound as renameable
symbols (tooling/minifiers model globals externally); `Script` — top-level declarations
bound (for runtimes needing resolvable top-level symbols). `FromStr` accepts
`global|script|module` case-insensitively (CLI plumbing).

**Scope model** (`ScopeKind`): `Global`, `Module`, `Class`, `StaticBlock` (its own
`var` scope — `var` does not leak out of `static {}`), `NonArrowFunction`,
`ArrowFunction`, `Block`, `FunctionExpressionName` (the dedicated scope holding a named
function expression's own name). Closure = module/function/arrow; var-scope = closure +
static block.

**Spec fidelity carried in the model**:

- Hoisting: `var`/function bindings hoist to the nearest var scope and are listed in
  `ScopeData::hoisted_bindings` (downstream passes model implicit `undefined` init).
- TDZ: lexical declarations recorded in `tdz_bindings`; uses marked `in_tdz` until
  initialization.
- **Annex B block functions** (sloppy scripts): a block-level function declaration
  introduces *two* bindings — block-scoped plus (when not shadowed by a lexical) a
  hoisted var binding — linked via `JsSemantics::annex_b_function_decls` so renamers
  keep their text consistent. In `Global` mode the hoisted twin may be synthetic
  (present in `symbols` but not in the global scope table) so minifiers treat the
  block binding as pinned.
- Dynamic-scope hazards: scopes containing `with` or a direct `eval(...)` call are
  flagged (`is_dynamic`, `has_direct_eval`); consumers must fail closed (no renaming).

**Determinism**: `ScopeId`/`SymbolId`/`NameId` are content-addressed (file id, scope
ancestry, decl kind, spans); scope tables are `BTreeMap<NameId, SymbolId>`; iterate via
`iter_symbols_sorted`/`scope_symbols`. Stability is relative to caller inputs — change
`FileId`s or spans and IDs change (by design).

### JS-mode early-error diagnostics (`BIND####`)

`declare()` is the owner of the scope-dependent ECMA-262 **early errors** (the ones the
parser can't decide context-free). The test262 parser harness now runs JS-mode binding
on the `early/` corpus so these are enforced against the conformance suite (see
[testing](../engineering/testing.md) and `test262/src/main.rs`). Codes emitted:

| Code | Rule (ECMA-262) |
| --- | --- |
| `BIND0001` | Duplicate lexical / catch-param declaration (§14.3.1, §14.15.1). |
| `BIND0002` | Conflicting lexical vs `var`/block-function declarations (§14.2.1). |
| `BIND0003` | TDZ use (runtime `ReferenceError`; **not** an early error — suppressed by `bind_js_for_runtime` and by the test262 harness). |
| `BIND0004` | Declaration in a single-statement context (§14.4). |
| `BIND0005` | `eval`/`arguments` in a strict binding position (§14.x). |
| `BIND0006` | Duplicate parameter names in strict / non-simple / arrow lists (§15.1). |
| `BIND0007` | `with` in strict mode (§14.11.1). |
| `BIND0008` | `delete` of an unqualified identifier in strict mode (§13.5.1.1). |
| `BIND0009`–`BIND0011` | Legacy octal / leading-zero literal / octal escape in strict mode (§12.9.x) — consumes the parser's `LegacyOctal*` assoc markers. |
| `BIND0012` | Invalid escape in an untagged template (§12.9.6). |
| `BIND0013` | Strict-mode reserved word as identifier (§13.1.1). |
| `BIND0014` | `new.target` outside a valid binding (§13.3.12). |
| `BIND0015` | **New (2026-07-23):** `const` (and `using`/`await using`) binding missing an initializer, outside a `for-in`/`for-of` head (§14.3.1). |
| `BIND0016` | **New (2026-07-23):** `let` used as a lexically bound name — `let`/`const`/`for`-head; sloppy `var let` stays legal (§14.3.1). |
| `BIND0017` | **New (2026-07-23):** duplicate `__proto__` colon-form data properties in an object literal; shorthand/method/accessor/computed keys excluded (§B.3.1). |
| `BIND0018` | **New (2026-07-23):** duplicate `ExportedNames` in a Module — list duplicates, declaration+list clashes, multiple `default` (§16.2.1.1). Primary span on the duplicate; secondary label on the first occurrence. |
| `BIND0019` | **New (2026-07-23):** local `export { … }` / `export { x as y }` whose `ExportedBindings` name is not a module-level binding (§16.2.1.1). Re-exports (`from`) are exempt. |
| `BIND0020` | **New (2026-07-24):** undeclared private name — `AllPrivateIdentifiersValid` / `AllPrivateNamesValid` (§12.10.5 / ScriptBody early errors). Tracks per-class PrivateBoundIdentifiers (outer names visible in nested classes); rejects `#x in y` / `obj.#x` when `#x` is not in the enclosing class name list. |

**Module-graph early errors (JS mode, 2026-07-23)** — `declare` now tracks module
`ExportedNames` / `ExportedBindings` while walking import/export statements and
`export` flags on declarations (module `TopLevelMode` only). Validation of
undeclared local export refs runs at end of `declare` against the module scope.
Duplicate import bindings remain `BIND0001` (imports are lexical). These are true
early errors: `bind_js_for_runtime` keeps them (only `BIND0003` TDZ is suppressed).
Evidence: V8/`node --check` rejects `export const a = 1; export {a}` (declaration
export and export list both contribute the name `a` to `ExportedNames`). The
test262 `early-module-export` cluster (31 ids) is un-manifested.

**Resolved over-strictness (2026-07-23)** — JS-mode `declare` was wrongly rejecting
legal sloppy scripts from the test262 pass corpus (11 → 0 BIND false positives;
verified by `semantic-js/tests/pass_corpus_bind.rs`). Escaped-directive detection
now uses the parse-js `StringLiteralContainsEscapes` marker (same day, evening)
instead of the Loc-length proxy. The test262 harness now also binds `pass/` and
`pass-explicit/` (same day) so binder over-strictness cannot regress unnoticed.

| Bug | Rule / § | Fix |
| --- | --- | --- |
| Escaped `'use\x20strict'` enabled strict | Directive Prologue / Use Strict Directive §11.2.1, §14.1.1 — only the unescaped raw literals `"use strict"` / `'use strict'` count | `is_use_strict_directive_literal`: cooked SV `"use strict"` **and** absence of parse-js `StringLiteralContainsEscapes` assoc marker (replaced the Loc-length==12 proxy on 2026-07-23). |
| Sloppy accessor/method params `yield`/`eval` rejected | §13.1.1 / §15.1.1 — strict-only (object methods are **not** automatically strict; ClassBody is) | Stop pushing `strict=true` for `Method`/`Getter`/`Setter`; keep UniqueFormalParameters via `next_func_unique_params` so `{ a(b,b){} }` still errors. |
| `yield` “leaked” into nested non-generator accessors/methods inside generators | §15.5.1 — yield restrictions scope to the generator's own params/body; nested non-generator functions reset the context | Same fix: accessors/methods inherit enclosing strictness only, so `yield` remains a legal IdentifierReference in sloppy nested getters/setters/methods. |

Also fixed while clearing the corpus: Annex B if-body `function` in a catch
(`try {} catch (a) { if(1) function a(){} }`) must not conflict with the catch
parameter the way a StatementList `function a(){}` does.

**Switch CaseBlock LexicallyDeclaredNames (2026-07-24)** — `switch` already
allocated a shared `ScopeKind::Block` for all case/default clauses. The remaining
gap was Annex B.3.2 over-application: in sloppy scripts, *all* block-level
`FunctionDeclaration` flavors (including `async` / `function*` / async generators)
took the Annex B path with `span: None`, so CaseBlock duplicates never raised
`BIND0001`/`BIND0002`. Fix: only *ordinary* FunctionDeclarations use Annex B;
Generator / Async / AsyncGenerator declarations are always block-lexical (same as
strict). Evidence: unit tests `switch_caseblock_*` in `js/tests.rs`; test262
`language/statements/switch/syntax/redeclaration/**` (63 ids) cleared via the
semantic harness binding path (below).

**Semantic harness early-error delivery (2026-07-24)** —
`test262-semantic`'s `VmJsExecutor` now runs `bind_js_for_runtime` (Ecma script)
before `exec_script_source`. Negative `phase: parse` tests use `$DONOTEVALUATE()`,
so runtime CaseBlock instantiation never runs; binder diagnostics must surface as
parse-phase `SyntaxError`. Cleared with this wiring + the Annex B fix: switch
CaseBlock redeclaration (63), labelled function-in-statement-position (9,
`PS0018`/`BIND0004`), `for` head bound-names-in-stmt (2, `BIND0002`), and async
formals/body duplicate (2, `BIND0002`). Residual early-SyntaxError xfails in
`language-core.toml` are mostly escaped `await`/`yield` identifiers and a few
ASI/label edges (parser-owned). Private-field `in` grammar (`PS0029`) and
undeclared private names (`BIND0020`, including block `invalid-names-*`) cleared
2026-07-24.

## TS mode (`semantic_js::ts`)

Module-graph binder over lowered HIR: `bind_ts_program(roots, resolver, hir_provider)`
(+ `_with_cancellation`) walks `ts::HirFile`s (built from `hir-js` output via
`ts/from_hir_js.rs`), producing `TsProgramSemantics`: a program-wide `SymbolTable`
(stable `SymbolId`/`DeclId`), per-file `ExportMap`s (`BTreeMap` by name), merged global
symbol groups, and ambient-module export/symbol maps addressable by specifier string.

**Namespaces and merging** — the three TypeScript namespaces are a bitmask
(`Namespace: VALUE | TYPE | NAMESPACE`); each `DeclKind` declares its mask (class =
value+type, enum = value+type, namespace = value+namespace, import = all three unless
type-only). `SymbolGroup`s hold one symbol per namespace or a single merged symbol when
kinds allow combining; interface and namespace merging are multiple declarations on one
symbol ordered by deterministic `order`. Type-only exports filter value/namespace bits
before insertion.

**Diagnostics** (stable codes; the TS-numbered ones deliberately mirror `tsc`):
`BIND1001` duplicate export · `BIND1002` unresolved import/export · `BIND1003`
unsupported export-assignment expression / exports in script · `BIND1004` duplicate
import binding · `BIND1006` conflicting `export as namespace` · `TS2300` duplicate
identifier · `TS2395` merged declarations must be all-exported or all-local · `TS2434`
namespace before merged class/function · `TS2309` `export =` mixed with other exports.

**Scope of TS mode** (explicit, absorbed from README): module-level declaration
merging and import/export graphs. It does **not** bind statement bodies (local/lexical
analysis lives in `ts/locals.rs` — `TsLocalSemantics`, used by the checker), and
`export =` supports entity-name references (identifier/property chains, synthesized as
an `export=` entry matching TypeScript's internal name) — other `export =` expressions
are rejected with a diagnostic. Module augmentation / global merging semantics are
still incomplete relative to `tsc`
([roadmap](../status/roadmap.md#3-correctness-program)).

## Reading attachments (`semantic_js::assoc`)

Helpers to read IDs out of `NodeAssocData` without exposing internals:
`assoc::js::{scope_id, declared_symbol, resolved_symbol}` and TS-side counterparts in
`assoc::ts`. The pattern — IDs in assoc slots, arenas behind the semantics value — is
the crate's API discipline: downstream never holds live scope objects.

## Examples

`examples/semantic-js/README.md` mirrors the crate-doc doctest: bind, walk with a
derive-visitor `VisitorMut` collecting `(name, scope, symbol)` triples, assert
resolution round-trips, iterate scopes deterministically. Runnable:

```bash
cargo run -p semantic-js --example js_mode_basic
cargo test -p semantic-js --doc
```

## Known issues and directions

- TS-mode gaps above (augmentation, general `export =`).
- JS-mode module early errors for `ExportedNames` / undeclared `ExportedBindings`
  are **landed** (`BIND0018`/`BIND0019`); remaining `early/` xfail clusters are
  elsewhere (dup block functions, escaped-name duplicates, catch/`for` var
  conflict, regex `u`-flag, miscellaneous `fail/`).
- `with`/`eval` remain hazard flags, not resolution modeling — permanent policy, not a
  gap: fail-closed is the correct treatment
  ([theory § name resolution](../theory/compiler-theory.md#2-name-resolution-environments-hoisting-and-three-namespaces)).
- Fuzzing entry (`fuzz.rs`, feature `fuzzing`) exercises bind/resolve without panic;
  extend it when adding binding forms.
