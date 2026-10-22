# parse-js

The parser: UTF-8 source text → typed AST (`Node<TopLevel>`), for JS / JSX / TS / TSX /
`.d.ts`, plus a strict ECMAScript mode. Treated as the workspace's **done, canonical
syntax model** — high-coverage and fast; do not introduce a second syntax tree (the
rowan/green-tree route was considered and rejected unless fine-grained incremental
parsing becomes a real requirement; see
[graveyard](../graveyard.md#rejected-alternatives-design-level)).
Published crate (`parse-js` on crates.io, version tracked in its `Cargo.toml`).

Theory background: [compiler-theory § parsing](../theory/compiler-theory.md#1-parsing-recursive-descent-is-the-right-call).

## Entry points and options

```rust
parse(source: &str) -> SyntaxResult<Node<TopLevel>>                    // Ts + Module defaults
parse_with_options(source, ParseOptions { dialect, source_type })
parse_with_options_cancellable(source, opts, cancel: Arc<AtomicBool>)  // for harnesses
```

`Dialect` = `Js | Jsx | Ts | Tsx | Dts | Ecma`. `Ecma` disables TypeScript-style
recovery entirely — conformance suites (test262) must see spec-exact rejection.
Dialect capability queries live on the enum (`allows_jsx`,
`allows_angle_bracket_type_assertions` — angle-bracket assertions are Ts/Dts-only since
they collide with JSX). `SourceType` = `Script | Module` (script mode rejects
`import`/`export`). Cancellation is cooperative: the parser checks the flag during
lexing/parsing and unwinds with a `ParseCancelled` payload converted to
`SyntaxErrorType::Cancelled`.

## AST design

Every node is:

```rust
Node<S> { loc: Loc, stx: Box<S>, assoc: NodeAssocData }
```

- `Loc(start, end)` — UTF-8 byte offsets. Deliberately *not* guaranteed to be a real
  source range: transforms create synthetic nodes, and some locations are best-effort.
- `stx: Box<S>` — one heap allocation per node, giving owned, movable subtrees.
- `assoc: NodeAssocData` — a type-keyed map (`TypeId → Box<dyn Any + Send + Sync>`,
  smallvec-backed) letting downstream passes attach data without changing the AST
  type: scope IDs (`semantic-js`), parenthesization markers, strict-mode-relevant
  literal provenance, UTF-16 string payloads.
- Traversal is derived: `#[derive(Drive, DriveMut)]` (derive-visitor, patched in
  `third_party/`) generates visitors; enums wrap each variant in `Node<T>` so visitors
  can see nodes, not just payloads.
- Serialization (feature `serde`): variant-tagged (`$t`) JSON; `serde-loc` adds
  location envelopes; `LocatedNode` wraps a node to force location output.

### Assoc markers worth knowing

These carry spec-correctness through the pipeline (all in `ast/node.rs`):

- `ParenthesizedExpr` — parentheses are not AST nodes; this marker preserves them for
  syntax-sensitive rules (exponentiation operand restrictions, directive prologues).
- `LegacyOctalNumberLiteral`, `LeadingZeroDecimalLiteral`, `LegacyOctalEscapeSequence`
  — strict-mode early errors deferred to semantic passes, with spans.
- `StringLiteralContainsEscapes` — raw string literal body contained any
  EscapeSequence or LineContinuation (`\`); used by the binder for Directive
  Prologue / Use Strict Directive (§11.2.1, §14.1.1) without needing source text.
- `LiteralStringCodeUnits`, `TemplateStringParts` — exact UTF-16 code units (raw +
  cooked, cooked optional per `GetTemplateObject`) because ECMAScript strings can hold
  unpaired surrogates that Rust `String` cannot; the VM consumes these.
- `InvalidTemplateEscapeSequence` — untagged-template escape errors (tagged templates
  legalize them with `undefined` cooked values).

### AST design rationale

(Absorbed from `notes/AST design rationale.md`, 2026-07 — a trade study from the
minifier era; kept because its conclusions still govern the tree's shape.)

The requirements: a node type carrying `Loc` + syntax; mutation during transforms;
subtree *moves* (transforms are almost always moves, not copies). The options weighed:

- **Arena + `&'bump mut` references**: avoids malloc, but mutable references are
  non-cloneable, so subtree moves require `mem::take/replace/swap` leaving dummy nodes
  in the arena that must never be touched again; deep-clone requires manual visitor
  work anyway.
- **`RefCell`/`Rc` trees**: cheap handles, but significant runtime cost and — the
  killer — they mostly *move lifetime errors from compile time to runtime*.
- **Owned boxed nodes** (chosen): `stx: Box<S>` with field-level moves tracked by the
  compiler; `map_stx`/`into_stx`/`wrap`/`take` provide the transform vocabulary.
  Costs malloc per node; buys safe, obvious ownership.

The note's arena variant was the historical direction; the shipped design settled on
owned boxes. If parser allocation ever dominates profiles, revisit with bump-arena +
owned-value-in-arena (not `&mut`-references) — and re-read that note first.

## Parser internals

- **Lexer** (`lex/mod.rs`): mode-driven (`LexMode`) for regex-vs-division, templates,
  and JSX; produces `Token { typ: TT, loc, preceded_by_line_terminator }` — the
  newline flag is what ASI and restricted productions consume.
- **`ParseCtx`** (`parse/mod.rs`): a small copied context (pattern rules, `top_level`,
  `in_namespace`, `AsiContext`) passed by value; altered by `with_*` copies rather than
  mutation, so nested parses can't leak state back out.
- **Expressions**: precedence climbing over `operator.rs` tables (`MULTARY_OPERATOR_MAPPING`);
  patterns parsed via cover grammar + reinterpretation.
- **TS grammar**: complete type-expression surface (`ast/type_expr.rs`: conditional,
  mapped with `as` remapping, template-literal, indexed access, `infer`, variance
  annotations, predicates…) and TS statements (`ast/ts_stmt.rs`: interfaces, aliases,
  enums, namespaces/modules, `declare global`, ambient decls, `import/export =`,
  `export as namespace`).
- Numbers: `num.rs` (`JsNumber`, fast-float); JSX: `ast/expr/jsx.rs`.

## Conformance and the syntax gap tracker

The conformance runner (`src/bin/conformance_runner.rs`, feature `conformance-runner`)
drives the vendored TypeScript repo's test corpus:

```bash
git submodule update --init --recursive --depth=1 parse-js/tests/TypeScript
cargo run -p parse-js --features conformance-runner --bin conformance_runner
```

It enforces a per-test timeout (default 10 s) via cooperative cancellation — no
thread-per-test. Since 2026-01 it consults TypeScript's `.errors.txt` baselines and
treats *expected* TS parse errors (TS1xxx) as passing, which eliminated the manual
allowlist for negative-syntax tests; a reported failure now means a real mismatch
(too-permissive or a genuine gap). The living gap list is
`parse-js/notes/syntax_gaps.md` — empty as of 2026-01, by policy updated whenever a
conformance run finds a real mismatch. Known limitation inherited by the type-checker
harness instead: this runner skips `@filename:` multi-file tests
(`typecheck-ts-harness` handles them).

## CLI (`parse-js-cli`)

Debugging tool: file or stdin → versioned JSON AST envelope
(`{ schema_version: 1, options, ast }`); `--dialect` (else inferred from extension:
`.js/.jsx/.ts/.tsx/.d.ts`; stdin defaults to `ts`), `--source-type` (default module),
`--json-errors` for machine-readable diagnostics, `--timeout-secs`. Non-JSON failures
render human diagnostics to stderr, exit non-zero.

## Statement `Loc` and terminating semicolons

Convention (aligned with the TypeScript compiler and `hir-js` SpanMap expectations):
**statement spans include the terminating semicolon**; under ASI the span ends at the
last token of the statement (no trailing trivia beyond that token).

Resolved (2026-07-23):

- **`debugger;`**: consumes `;` inside the statement `with_loc` (previously left `;` as
  a separate `EmptyStmt`).
- **Labeled `break L;` / `continue L;`**: same rule — `;` is consumed into the
  Break/Continue node (was leaving a spurious `EmptyStmt`; unlabeled path already did).
- **ASI at EOF for `break`/`continue`**: EOF is an ASI boundary alongside `}` / line
  terminator (ECMA-262 §12.10 rule 2). `while(1)break` at end-of-input is accepted.
  Audit of adjacent restricted productions: `return` had the identical EOF gap (optional
  expression) and was fixed the same way; statement-list loops also stop at EOF so an
  incomplete `function f(){return` fails on the missing `}` rather than a spurious
  expression parse. `throw` requires an operand so bare `throw` at EOF correctly
  errors; `yield` already ends via the expression ASI path that includes EOF.

## `new.target` early error

`new.target` is an early SyntaxError unless a `new.target` binding exists — non-arrow
function / method body, or class field / static-block initialiser (ECMA-262; TS17013).
**Arrows inherit** that binding from an enclosing non-arrow context; an arrow alone
does not create one. Fixed 2026-07-23 (a prior change that allowed arrows had
overshot by incrementing `new_target_allowed` on every arrow). Enforced in `Dialect::Ecma`
only; Ts/Js dialects still accept outer `new.target` for recovery (tsc also errors, but
TS17013 is not in the conformance runner’s expected-parse-error allowlist, so rejecting
in Ts would break recovery-oriented corpus parsing).

Follow-up (same day, test262 triage): default-parameter initialisers evaluate in the
function/method binding environment, so `new.target` (and `super()` in derived
constructors) must be allowed while parsing parameters — not only the body. Helpers
`with_non_arrow_func_bindings` / `with_method_bindings` wrap parameter parsing.

Resolved (2026-07-23, evening — arrow/`new.target` interaction): the two same-day
fixes interact only through flag lifecycle. Arrows correctly **do not** modify
`new_target_allowed` (they inherit). Parameter helpers correctly **save/restore**
that flag around defaults. The VM-visible `PS0002` (“expected expression operand”)
was not a clobbered flag on nested arrows (those already parsed); it was
arrow-vs-grouping speculation **backtracking after `=>`**, swallowing the real
Ecma early error (`new.target` outside a binding) and retrying `()` as an empty
grouping. Fix: once `=>` is consumed, commit to the arrow and propagate body
errors (`arrow_parse_committed`). Invariant to prevent recurrence: **arrows never
modify `new_target_allowed`; parameter binding scopes must save/restore, not
reset.** Regression tests: `tests/regressions/new_target_arrow_inheritance.rs`.
Note: hosts that reparse arrow *snippets* as top-level `(snippet)` (e.g. vm-js)
still see the legitimate Ecma rejection unless they reparse inside a synthetic
non-arrow function binding.

Follow-up (2026-07-27 — bare function-type params): `(x) => T` in a type
position binds `x` as a parameter name with synthetic `any` when followed by
`,`/`)` (was restored and parsed as a type reference → false TC2008 in the
checker). Regression: `tests/regressions/bare_fn_type_param.rs`.

Follow-up (2026-07-30 — template line-terminator normalization): cooked
template values now normalize CR and CRLF to a single LF (ECMA-262 §12.9.6);
previously a CRLF inside a template cooked to two code units (`\r\n`), so a
template spanning a Windows line break mismatched `"…\n…"` string-literal
annotations (`stringLiteralTypesWithTemplateStrings01.ts`).

Follow-up (2026-07-30 — concise body vs comma): an arrow concise body is an
*AssignmentExpression* (ECMA-262 §14.2 ConciseBody), so a top-level comma
belongs to the enclosing sequence: `(f = x => x, "_")` is `f = (x => x)` then
`"_"`, not `f = (x => (x, "_"))`. The body now parses with
`expr_with_min_prec(2, …)` (above `Comma`, same idiom as `class_heritage`)
instead of a full comma-expression. The mis-parse also changed runtime
semantics (`f` would return the sequence tail, not the body value). Cleared
`privateNameComputedPropertyName2/4` against tsc; regression:
`typecheck-ts/tests/private_name_shadow_fields.rs`.

Follow-up (2026-07-26 — nested arrow commit + private index recovery):
- `arrow_func_expr` **save/restores** `arrow_parse_committed` so a successful
  nested `(a) => …` inside a speculated parameter list cannot sticky-commit the
  outer speculation. Unblocks
  `[(getX = (a: A) => a.#x, "_")]()` (parenthesized comma AssignmentExpression
  in a computed key). Regression:
  `tests/regressions/private_name_parse_recovery.rs`.
- Soft `report_soft` dedupes consecutive same-start diagnostics (tsc
  `parseErrorAtCurrentToken`). Type postfix `[` that is not `is_start_of_type`
  (notably `PrivateMember`) recovers as array `T[]` with soft **PS0013** `]`
  expected; var-declarator lists soft-expect `,` / **PS0031**↔**TS1134** for
  junk (`C[#bar] = 3`). Harness maps `PS0031` → **TS1134**.

## Optional chain from `new` (PS0017)

Resolved (2026-07-23): reject optional chains that feed or follow a bare `new`
expression — **all dialects**, hard parse error `PS0017`
(`SyntaxErrorType::InvalidOptionalChainFromNew`; message mentions “optional chain”
and “new”; mirrors TS1209).

ECMA-262 productions:
- `new`'s callee is a `MemberExpression`; an `OptionalExpression` is not, so
  `new a?.b` / `new a?.[b]` / `new a?.()` / `new a.b?.c()` are SyntaxErrors.
- `OptionalChain` may follow `MemberExpression` / `CallExpression`, but not a bare
  `NewExpression` (no Arguments): `new a?.()` is illegal; `(new a)?.()` and
  `new a()?.b` are legal.
- Parenthesized chains remain legal: `new (a?.b)`, `new (a?.())`, and
  `new (a?.b).c()` (optional chain stays inside `PrimaryExpression`; further
  `.c` / Arguments attach as ordinary `MemberExpression`).

See also [emit-js](emit-js.md#parentheses-beyond-precedence) (emitter still
parenthesizes synthetic ASTs that encode these shapes).

## Known issues and directions

- Early-error ownership table (parser vs binder vs VM) should be made explicit
  ([roadmap](../status/roadmap.md#3-correctness-program)).
- Benchmarks: `benches/baseline_performance.rs` (criterion) — keep it in profiles when
  touching the lexer.

## test262 parser conformance (gap tracker)

Last run: **2026-07-23** (`reports/test262-parser-post-yieldparams.json`), after
pass-corpus binding + `yield`-in-params. Prior baselines:
`reports/test262-parser-post-passbind.json` / `post-failfix.json` (100
manifested), `reports/test262-parser-post-early.json` (176 manifested).

| Metric | Post-failfix | Post-yieldparams |
| --- | ---: | ---: |
| total | 5363 | 5363 |
| unexpected mismatches | **0** | **0** |
| manifested (expected) mismatches | 100 | **67** |

The blanket `fail/**` / `early/**` xfails are gone, replaced by precise per-cluster
manifest entries (each names the Early Error rule + ECMA-262 § + owning layer).
`--fail-on new` exits 0. Parser `fail/` clusters burned down **95 → ~25** remaining
(regex-u deferred + miscellaneous `fail-other`); `early/` update-operand (4) also
moved to matches via the same update-operand fix.

**Harness split (spec-faithful).** The runner treats `fail/` as "must fail to *parse*"
(parser only) and `early/` as "parses, then rejected by a static-semantics early
error." Because the parser alone can't decide scope-dependent rules, the harness
runs `semantic_js::js::bind_js` on `early/`, `pass/`, and `pass-explicit/`
(script→`Script`, module→`Module` top-level mode), counting any non-TDZ `BIND####`
error as a rejection (`test262/src/main.rs`). On `pass`/`pass-explicit` a bind
error is a harness failure (catches binder over-strictness); binder false
positives were cleared 2026-07-23 (see
[semantic-js](semantic-js.md#js-mode-early-error-diagnostics-bind)).

**Ownership (parser vs binder) for the remaining clusters:**

| Cluster | Owner | Status |
| --- | --- | --- |
| duplicate lexical/var/param decls, strict-mode rules, `new.target`, `with`, octal, `delete` | binder (`BIND0001`–`0014`) | enforced (via harness `early/` binding) |
| Switch CaseBlock LexicallyDeclaredNames / VarDeclaredNames (§14.12.1) | binder (`BIND0001`/`BIND0002`) | **landed 2026-07-24** — Annex B only for ordinary `function`; async/generator stay lexical; semantic harness binds before exec |
| labelled `function` in single-statement position (`if`/`for`/`while`/…) | parser `PS0018` + binder `BIND0004` | **cleared in language-core 2026-07-24** (semantic harness surfaces them) |
| `const` without initializer, `let` as lexical name, duplicate `__proto__` | binder (`BIND0015`–`0017`) | **landed 2026-07-23** |
| duplicate/undefined module exports & imports | binder (module graph) | **resolved 2026-07-23** — JS-mode `declare` now tracks `ExportedNames`/`ExportedBindings` (`BIND0018`/`BIND0019`, §16.2.1.1); details in [semantic-js](./semantic-js.md) |
| `yield` in formal parameters (generator context) | parser | **landed 2026-07-23** (`for_formal_parameters`) |
| escaped `await`/`yield` as IdentifierName in async/generator contexts | parser | **landed 2026-07-24** — `identifier_string_value` decode; StringValue used for [Await]/[Yield] and strict reserved words; module negative-parse path in `test262-semantic` |
| strict RegExp `u`-flag pattern grammar | regex validation | deferred (needs pattern grammar, not just flags) |
| remaining `fail-other` (arrow-as-callee, labelled generator, sloppy `\8`/`\9`, …) | parser | manifested |

### Resolved (2026-07-23) — pass-corpus gaps from triage

- **CoverInitializedName** (ECMA-262 ObjectLiteral cover / ObjectAssignmentPattern):
  parse `IdentifierReference Initializer` in object literals; reinterpret via
  `lit_to_pat`; early-error any remaining `CoverInitializedName` marker on
  `LitObjExpr` members (`({a = 1});` still rejects). Tests:
  `tests/regressions/cover_grammar_and_targets.rs`.
- **Parenthesized SimpleAssignmentTarget** (IsValidSimpleAssignmentTarget of
  ParenthesizedExpression): look through `ParenthesizedExpr` for Id / Member /
  ComputedMember; still reject parenthesized Array/Object patterns and non-simple
  targets (`(a+b)=1`, `(this)=1`, `([a])=1`).
- **Nested AssignmentRestElement** (`[...[a]]`, `[...{a}]`): `lit_to_pat` allows
  nested Array/Object patterns in array rest; object rest stays simple-target-only;
  trailing-comma-after-rest marked and rejected on pattern conversion.
- **`for (let in …)`** (sloppy IdentifierReference): `let`+`in` is not a lexical
  declaration; `let`+`of` is a declaration only when a second `of`/`in` follows
  (binding name `of`); bare `for (let of x)` is an early error.
- **Escaped Use Strict Directive**: directive check uses raw source
  (`"use strict"` / `'use strict'` only); `'use\x20strict'` does not enable strict
  mode, so `with` remains legal in sloppy scripts. Parser also attaches
  `StringLiteralContainsEscapes` on every `LitStrExpr` (and string property keys)
  whose raw body contains `\`, so `semantic-js` can apply the same rule without a
  Loc-length proxy (landed 2026-07-23, evening).

### Resolved (2026-07-23, evening — parser `fail/` rejection clusters)

Landed in `Dialect::Ecma` with dedicated `PS####` codes and accept/reject regression
tests in `tests/regressions/fail_cluster_rejections.rs`:

| Cluster | § | Code | Notes |
| --- | --- | --- | --- |
| Declaration in single-statement position | §14 Statement vs StatementListItem; B.3.3 / B.3.1 | `PS0018` | Rejects `let`/`const`/`class`/`function` in if/while/for/with/do/label bodies. Annex B: sloppy script still allows **non-async, non-generator** `FunctionDeclaration` in `if` clauses and as a labelled item; modules / `'use strict'` reject. **`let`+LT caveat (fixed 2026-07-23):** see next subsection. |
| BindingPattern needs Initializer | §14.3.1 / §14.3.2 | `PS0019` | `let [a]` / `var {a}` reject; `let [a] = b` and **for-in/of** `for (let [a] of x)` remain legal (iteration value supplies the binding). |
| Unterminated MultiLineComment | §12.4 | `PS0020` | Lexer emits `Invalid` spanning `/*`…EOF; parser maps to `PS0020`. |
| Rest parameter rules | §15.1 | `PS0021` | Rest must be last, no initializer, no trailing comma after rest; arrow speculation does not swallow this error into grouping. |
| ComputedPropertyName comma | §13.2.5 | (via expr min-prec) | AssignmentExpression only (`min_prec` above Comma); `({[(a,b)]:0})` still OK. |
| ClassHeritage LHS | §15.7 | `PS0024` | Rejects `extends a+b` / `!a` / bare comma; parenthesized `(a+b)` is PrimaryExpression hence legal. `new super()` rejected; `new super.x` (SuperProperty) kept legal. |
| NumericLiteral + IdentifierStart | §12.9.3 | `PS0022` | Lexer marks number `Invalid` when IdentifierStart follows; `3 in x` with space OK. |
| HTML-like comments in modules | §B.1.1 | `PS0023` | `Lexer::allow_html_comments` cleared for `SourceType::Module`; scripts still accept `<!--` / `-->`. |
| Untagged template legacy octal | §12.9.6 | `PS0025` | Always illegal in untagged templates (all modes); tagged templates keep undefined cooked. |
| UpdateExpression operand | §13.4 | `PS0026` | Simple assignment target only; also rejects `a++\`tpl\``. |
| Mixed `??` with `&&`/`||` | ShortCircuitExpression | `PS0027` | Unparenthesized mix rejected (test262 `coalesce/cannot-chain-*`). |
| Optional chain + tagged template | OptionalChain early error | `PS0028` | `a?.fn\`tpl\`` / `a?.\`tpl\`` rejected; `(a?.fn)\`tpl\`` ok. |
| Bare / nested private `in` | RelationalExpression[+In] `PrivateIdentifier in ShiftExpression` | `PS0029` | `#id` is not a PrimaryExpression; only `#id in ShiftExpression` (and `. #id` / `?. #id`) are legal. Rejects `#a in #b in c`, `for (#id in …)`, `!#id in x`, bare `#id;`. Legal: `#id in this`, `(#id in this) in x`, `yield #id in o`. |
| Escaped `await`/`yield` bindings | BindingIdentifier [Await]/[Yield]; Identifier StringValue | `PS0002` | `\u0061wait` / `yi\u0065ld` rejected in async/generator bodies (refs + labels); strict `yi\u0065ld` label/binding; module `aw\u0061it:` label. Decoder: `Parser::identifier_string_value`. |
| for-of LHS starting with `let` | §14.7.5 | `PS0002` | `for (let.a of 0)` rejects; `for (let.a in 0)` OK. |
| Function body ASI in for-header | AsiContext | (ASI) | Nested function bodies always `AsiContext::Statements` so `for ((function(){ throw "x" })();;)` parses (test262 `for/S12.6.3_A2*`). |
| Spaced optional call/computed | OptionalChain | — | `fn ?. (…)` / `fn ?. [i]` after bare `?.` (not only fused `?.(` / `?.[`). |
| Duplicate `default` / do-while `;` / static `await` / `let`+`await` | §14.12 / do-while / ClassStaticBlock / LexicalDeclaration | `PS0002` | Early-error burn-down 2026-07-24 eve. |

### Resolved (2026-07-23, evening — `let`+newline ASI vs PS0018)

PS0018 initially treated every `let`/`using` followed by `{` / `[` / BindingIdentifier as
a LexicalDeclaration head in Statement position. That over-rejected legal sloppy
code from test262 `pass` / semantic corpus:

- `language/statements/{if,while,for,labeled}/let-{block,identifier}-with-newline.js`

**Pinned rule** (ECMA-262 + V8/`node --check` agreement):

1. **LexicalDeclaration** (`LetOrConst BindingList`, §14.3.1) has **no**
   `[no LineTerminator here]` between `let` and the binding. At
   **StatementListItem**, `let\nx = 1`, `let\n[a] = []`, and `let\n{a} = {}` are
   declarations (ASI does not split them).
2. **ExpressionStatement** (§14.11) forbids only the two-token lookahead
   `let [` — not `let {` and not `let BindingIdentifier`. There is also no
   `[no LineTerminator here]` inside that `let [` lookahead token pair, so
   `let\n[` is still forbidden as ExpressionStatement.
3. **Statement** (if/while/for/with/do body, LabelledItem) does **not** include
   Declaration. So:
   - `if (c) let x;` / `if (c) let {}` / `if (c) let[a]=…` → **PS0018**
   - `if (c) let\nx;` / `if (c) let\n{}` → **legal**: ASI ends ExpressionStatement
     `let;` (IdentifierReference); `x = …` / `{}` are the **next** statement after
     the `if` (or after the labelled item). Same for `while` / `for` bodies and
     `L: let\n…`.
   - `if (c) let\n[a]=…` → still **PS0018** (`let [` cannot be ExpressionStatement,
     so the only remaining parse is the disallowed LexicalDeclaration).
4. Strict mode / modules still reject IdentifierReference `let` as a reserved word;
   the corpus cases are `flags: [noStrict]` scripts.

Fix: `peek_disallowed_in_statement_position` only flags `let`/`using` + `{`|BindingIdentifier
when **not** preceded by LineTerminator; `let [` stays flagged regardless of LT.
`stmt_in_statement_position` then routes the ASI case to `expr_stmt` (because
`stmt()` correctly keeps StatementListItem `let\nx` as a declaration). Tests:
`tests/regressions/let_newline_asi_statement_position.rs` and neighbours in
`fail_cluster_rejections.rs`.

**VM-manifest handoff:** un-manifest all eight ids in
`test262-semantic/manifests/language-core.toml` (they were added as parser-gap
xfails for this bug).

**Stopped / deferred:**

- **RegExp `u`/`v` pattern grammar** (`fail-regex-u-flag`, 4 cases) — needs unicode-mode
  pattern validation beyond flag lexing; left manifested.
- **Sloppy `\8`/`\9` string escapes** and other `fail-other` leftovers — Annex B still
  allows NonOctalDecimalEscape in non-strict strings (Node agrees); corpus `fail/`
  expects reject without Annex B. Not forced here.
- Binder module-export clusters — out of the yield-params pass (module graph).

### Resolved (2026-07-23, evening — yield-in-params + harness pass-bind)

- **`StringLiteralContainsEscapes` assoc marker** on `LitStrExpr` / string property
  keys whose raw body contains `\`; binder Use Strict Directive check consumes it
  (replaces Loc-length==12 proxy). See [semantic-js](semantic-js.md).
- **Harness binds `pass/` + `pass-explicit/`** (not only `early/`) so binder
  over-strictness is a permanent harness failure (`test262/src/main.rs`; report
  `reports/test262-parser-post-passbind.json`).
- **`yield` in FormalParameters / ArrowParameters** (ECMA-262 §15.5.1, §15.1.1):
  `ParsePatternRules::for_formal_parameters` clears `yield_expr_allowed` /
  `await_expr_allowed` for parameter lists while leaving body rules intact.
  Covers generator params, nested generator params, generator methods, and arrows
  nested inside generators (33 `early/` cases). Tests:
  `tests/regressions/yield_in_formal_parameters.rs`. Legal neighbours kept:
  sloppy `function f(yield){}`, nested non-generator `function inner(a = yield)`,
  generator bodies.

Still manifested (see the per-cluster manifest and the ownership table above):

- Template/string literal edge cases (pre-existing regex xfail, pass corpus).
- `early/` binder-owned module export/import rules + residual early clusters
  (dup block-function, escaped-dup-binding, catch-var-conflict, early-other).
- Deferred RegExp `u`-flag pattern grammar + remaining `fail-other` misc.
