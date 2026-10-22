# emit-js

The deterministic printer: `parse-js` AST *or* `hir-js` structures → UTF-8 JS/TS text.
The single place in the workspace that knows how to write JavaScript, shared by the
minifier, the optimizer's decompiler, and tooling. Its correctness obligations are the
sneaky ones: token-boundary whitespace, ASI hazards, and parenthesization.

## Entry points

```rust
emit_top_level(FileId, &Node<TopLevel>, EmitOptions) -> EmitResult<String>   // AST backend
emit_top_level_diagnostic(...) -> Result<String, Diagnostic>                 // EMIT#### on failure
emit_hir_file(&LowerResult, EmitOptions) / emit_hir_file_diagnostic(...)     // HIR backend
emit_hir_body(...)                                                           // single body
```

Plus granular exports for embedding: statement/expression/pattern/JSX emitters for both
backends (`emit_js_stmt`, `emit_expr`, `emit_ts_stmt`, `emit_type_expr`,
`ts_type_to_string`, string-literal/template escaping helpers, …).

`Emitter`/`EmitOptions` control mode (`EmitMode`), whitespace, quote style
(`QuoteStyle`), and statement separation (`StmtSepStyle`); `EmitOptions::minified()` is
the minifier profile. The emitter is *boundary-aware*: emitting token fragments inserts
the minimum whitespace needed to avoid re-tokenization hazards (`a + +b`, keywords vs
identifiers, etc.).

## Two backends, one policy

Both an AST backend (`stmt.rs`/`expr*.rs`/`pat.rs`/`jsx.rs`/`ts_stmt.rs`/`ts_type.rs`)
and a HIR backend (`hir.rs`, `js_*.rs`) exist. Policy (absorbed from `minify-js`):
**production output comes from the HIR backend**, and unsupported syntax is a hard
error — never a silent fallback to the AST printer, so backend drift can't hide. The
AST backend remains for tooling, tests (parity checks force-fail the HIR path to
compare outputs), and the migration period; long-term it shrinks.

## ASI (automatic semicolon insertion) machinery

`asi.rs` + `stmt_start.rs` implement the analysis needed to omit/insert separators
safely in minified output: classify how a statement *starts* (`StmtStartToken` — does
it begin with `(`, `[`, `` ` ``, `/`, `+`, `-`?) and how the previous one *ends*
(`StmtLeafEnd`, `stmt_tail_is_expression_like`), then choose a `Separator` between
them (`separator_between`, `separator_after_last`). Expression statements that would
be misparsed get wrapped (`expr_stmt_needs_parens`). This is the code that makes
newline-free output correct.

## Parentheses beyond precedence

`precedence.rs` handles operator precedence/associativity; the cases *outside*
standard precedence rules are the documented trap list (absorbed from
`notes/Parentheses.md`, 2026-07):

**When a comma would not be a comma expression** — parenthesize comma expressions in:
call arguments (`fn(a, (1, 2))`), variable initializers
(`let x = 1, y = (2, 3), z = 4`), arrow-function expression bodies
(`() => (1, 2)` — the body slot has lower precedence), array/object literal members
(`[1, (2, 3)]`, `{a: 1, b: (2, 3)}`).

**When an expression would be misparsed as a statement** — parenthesize at statement
start: object destructuring assignment without declaration (`({p: v} = {})`), object
literals as arrow bodies (`() => ({a: 1})`), function/class expressions that would
read as declarations (IIFE: `(function decl() {})()`).

**`new` and optional chaining (ECMA-262)** — settled 2026-07-23:

- A `new` callee is a `MemberExpression`. An `OptionalExpression` is not, so an
  optional chain in the callee must be parenthesized: `new (a?.b)`,
  `new (a?.())`, `new (a?.[b])`, `new (a?.b)()`. Plain call callees likewise:
  `new (f())()` (otherwise `new f()()` is `(new f())()`).
- `OptionalChain` also cannot follow a bare `NewExpression`: `(new a)?.()` is
  valid, `new a?.()` is a SyntaxError (parse-js `PS0017`). The emitter still
  parenthesizes synthetic ASTs that encode those illegal source shapes.
- Shared helpers live in `precedence.rs`
  (`needs_parens_before_optional_chain`, `new_callee_needs_parens`); AST
  (`expr.rs` / `expr_js.rs`) and HIR (`hir.rs`) both use them. Coverage:
  `tests/expr_roundtrip_matrix.rs` (`parenthesizes_new_*`; illegal sources use
  constructed-AST emit asserts).

Precedence *constants* (`PRIMARY/CALL_MEMBER/POSTFIX/ARROW_PRECEDENCE` in
`expr_js.rs` / `js_expr.rs`) mirror the `OPERATORS` table by hand and are
guarded by `debug_assert_eq!` — the 2026-07-26 `as`/`satisfies` level
insertion shifted every operator up one and the debug assert caught the
staleness (fixed 2026-07-30; keep them in sync when touching
`PRECEDENCE_LEVELS`). Related emit-vs-parse alignment (same day): bare
function-type params print as `name: any` (tsc TS7051 grammar: a bare
identifier is a *name*; `parse-js` regression
`tests/regressions/bare_fn_type_param.rs`).

## Diagnostics

Failures return `EMIT####` diagnostics (`EmitError`/`EmitErrorKind` → best-effort span
from `Loc`) rather than panics — emitters are reachable from user input via the
minifier, so the [error doctrine](../architecture/diagnostics.md#diagnostic-vs-fatal-error)
applies fully.

## Verification

Unit tests per construct plus round-trip matrices (`tests/expr_roundtrip_matrix.rs`:
emit → reparse → assert canonical form — the harness that caught the `new a?.()` bug).

**Megatest emit-text fixpoint** (`tests/megatest_fixpoint.rs`, CI-named step):

```bash
cargo test -p emit-js --test megatest_fixpoint
```

For each `megatest/*.js` that parses: AST emit (minified + canonical) must
re-parse and re-emit to an identical string; HIR emit is checked the same way
where supported. Intentional non-participants (delete a skip when the gap closes):

| File | Path | Reason |
| --- | --- | --- |
| `vdom.js`, `weird.js` | parse | object-literal `get:`/`set:` properties fail to parse (getter/setter ambiguity) |
| `reactive_pipeline.js`, `static_analysis.js`, `stream_processing.js`, `task_scheduler.js` | HIR emit only | lowering leaves `ExprKind::Missing`; emit fails closed |

Remaining expansion: fuzz corpora; AST↔HIR parity under the same fixpoint once HIR
gaps close.

## Known issues and directions

- `new` / optional-chain parenthesization: fixed on both sides (parse-js `PS0017` +
  emitter defensive parens; see “Parentheses beyond precedence”). Keep the
  `parenthesizes_new_*` matrix green when touching emit.
- The AST backend / HIR backend duality carries a standing parity obligation until the
  AST backend is retired — parity tests must stay alive as long as both exist.
- Comment/trivia preservation is out of scope today (minifier doesn't need it); if a
  formatter product ever appears, that's a separate design conversation, not a patch.
