//! Parser-owned fail/ cluster rejections (ECMA-262 early SyntaxErrors).
//!
//! Each illegal form cites the relevant section; neighbouring legal forms must
//! keep parsing.

use parse_js::error::SyntaxErrorType;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn ecma_module() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Module,
  }
}

fn assert_reject(src: &str) {
  assert!(
    parse_with_options(src, ecma_script()).is_err(),
    "expected reject: {src:?}"
  );
}

fn assert_reject_code(src: &str, code: &str) {
  let err = parse_with_options(src, ecma_script()).expect_err(&format!("expected reject: {src:?}"));
  assert_eq!(err.typ.code(), code, "src={src:?} err={err:?}");
}

fn assert_reject_module(src: &str) {
  assert!(
    parse_with_options(src, ecma_module()).is_err(),
    "expected module reject: {src:?}"
  );
}

fn assert_accept(src: &str) {
  parse_with_options(src, ecma_script()).unwrap_or_else(|err| {
    panic!("expected accept {src:?}, got {err:?}");
  });
}

fn assert_accept_module(src: &str) {
  parse_with_options(src, ecma_module()).unwrap_or_else(|err| {
    panic!("expected module accept {src:?}, got {err:?}");
  });
}

#[test]
fn decl_in_single_statement_position_ecma_14() {
  // §14 Statement vs StatementListItem — lexical / class / function (non-Annex-B).
  assert_reject_code("if (1) let x = 10;", "PS0018");
  assert_reject_code("if(true) const a = 1;", "PS0018");
  assert_reject_code("while(true) let a", "PS0018");
  assert_reject_code("while(true) const a", "PS0018");
  assert_reject_code("for (;;) const x = 10;", "PS0018");
  assert_reject_code("for(;;) function a(){}", "PS0018");
  assert_reject_code("while (1) function foo(){}", "PS0018");
  assert_reject_code("for(a in b) function c(){}", "PS0018");
  assert_reject_code("for(a of b) function c(){}", "PS0018");
  assert_reject_code("with(true) let a", "PS0018");
  assert_reject_code("with(true) function a(){}", "PS0018");
  assert_reject_code("with(true) class a {}", "PS0018");
  assert_reject_code("a: let a", "PS0018");

  // Strict mode: Annex B.3.3 does not apply.
  assert_reject("'use strict'; if (true) function a(){}");
  assert_reject_module("if (true) function a(){}");

  // Legal neighbours.
  assert_accept("if (x) { let y; }");
  assert_accept("if (x) var y;");
  assert_accept("while (x) { const z = 1; }");
  assert_accept("for (;;) { function f(){} }");
  // Annex B.3.3 — sloppy script allows FunctionDeclaration in if clauses.
  assert_accept("if (true) function a(){}");
  assert_accept("if (true) function a(){} else function b(){}");
  // Annex B.3.1 — labelled FunctionDeclaration in sloppy script.
  assert_accept("label: function a(){}");

  // `let` + LineTerminator + `{`|BindingIdentifier is ExpressionStatement + ASI
  // (§14.11 lookahead is only `let [`; LexicalDeclaration has no LT restriction, but
  // Declaration is not a Statement). Same shapes as test262 `*-let-*-with-newline`.
  assert_accept("if (false) let\n{}");
  assert_accept("if (false) let\nx = 1;");
  assert_accept("while (false) let\n{}");
  assert_accept("while (false) let\nx = 1;");
  assert_accept("for (; false; ) let\n{}");
  assert_accept("for (; false; ) let\nx = 1;");
  assert_accept("if (false) {\n    L: let\n    {}\n}");
  assert_accept("if (false) {\n    L: let\n    x = 1;\n}");
  assert_accept("if (false) let;");
  assert_accept("L: let\nx = 1;");
  // StatementListItem: `let`+LT still LexicalDeclaration.
  assert_accept("let\nx = 1;");
  assert_accept("let\n[a] = [];");
  assert_accept("let\n{a} = {};");
  // ExpressionStatement forbids `let [` even across LT → still PS0018.
  assert_reject_code("if (false) let\n[a] = [];", "PS0018");
  assert_reject_code("if (false) let {}", "PS0018");
}

#[test]
fn destructuring_declaration_needs_initializer_ecma_14_3() {
  // §14.3.1 / §14.3.2 — BindingPattern requires Initializer.
  assert_reject_code("let []", "PS0019");
  assert_reject_code("let [x]", "PS0019");
  assert_reject_code("var [a];", "PS0019");
  assert_reject_code("var {a};", "PS0019");
  assert_reject_code("var {a:a};", "PS0019");
  assert_reject_code("for(let [a];;);", "PS0019");
  assert_reject_code("for (let [a = 1];;) {}", "PS0019");

  assert_accept("let [a] = b;");
  assert_accept("var {a} = b;");
  assert_accept("for (let [a] = b;;) {}");
  assert_accept("for (let [a] of b);");
  assert_accept("for (let {} in 1);");
  assert_accept("for (var [a,b] in c);");
  assert_accept("let a;");
  assert_accept("var a;");
}

#[test]
fn unterminated_multiline_comment_ecma_12_4() {
  assert_reject_code("/*", "PS0020");
  assert_reject_code("/*hello", "PS0020");
  assert_reject_code("/**", "PS0020");
  assert_reject_code("/*\n\n*", "PS0020");
  assert_accept("/* ok */");
  assert_accept("/** ok */ 1");
}

#[test]
fn rest_parameter_rules_ecma_15_1() {
  assert_reject_code("function x(...a = 1){}", "PS0021");
  assert_reject_code("function f(a, ...b = 0){}", "PS0021");
  assert_reject_code("(function(...a, b){})", "PS0021");
  assert_reject_code("function f(a, ...b, c){}", "PS0021");
  assert_reject_code("(...a, b) => {}", "PS0021");
  assert_reject_code("(...a, ...b) => 0", "PS0021");

  assert_accept("function f(...a){}");
  assert_accept("function f(a, ...b){}");
  assert_accept("(...a) => 0");
  assert_accept("(a, ...b) => {}");
}

#[test]
fn computed_key_no_comma_ecma_13_2_5() {
  assert_reject("({[a,b]:0})");
  assert_reject("void { [1, 2]: 3 };");
  assert_reject("(class {[a,b](){}})");
  assert_accept("({[a]:0})");
  assert_accept("({[(a,b)]:0})");
  assert_accept("(class {[a](){}})");
}

#[test]
fn class_heritage_must_be_lhs_ecma_15_7() {
  assert_reject_code("class A extends a + b {}", "PS0024");
  assert_reject_code("(class extends !a {})", "PS0024");
  assert_reject("(class extends a,b {})");
  assert_reject("class A extends B { constructor() { new super(); } }");

  assert_accept("class A extends B {}");
  assert_accept("class A extends a.b {}");
  assert_accept("class A extends a() {}");
  assert_accept("class A extends new B {}");
  assert_accept("(class extends (a + b) {})");
  // SuperProperty is a valid NewExpression callee; only bare/call super is illegal.
  assert_accept("class a { b() { new super.c; } }");
  assert_accept("class a extends b { c() { new super.d(); } }");
}

#[test]
fn numeric_literal_then_identifier_ecma_12_9_3() {
  assert_reject_code("3in[]", "PS0022");
  assert_reject_code("3in []", "PS0022");
  assert_reject_code("0x3in[]", "PS0022");
  assert_accept("3 in []");
  assert_accept("0x3 in []");
  assert_accept("3e1");
}

#[test]
fn html_comments_script_only_annex_b_1_1() {
  assert_reject_module("<!--");
  assert_reject_module("-->");
  assert_reject_module("function a(){\n<!--\n}");
  assert_reject_module("function a(){\n-->\n}");

  // Script mode: Annex B HTML-like comments are insignificant.
  assert_accept("<!--\n");
  assert_accept("-->\n");
  assert_accept("function a(){\n<!--\n}");
  assert_accept_module("function a(){ /* ok */ }");
}

#[test]
fn template_legacy_octal_always_illegal_ecma_12_9_6() {
  assert_reject_code("`\\07`", "PS0025");
  assert_reject_code("`\\1`", "PS0025");
  assert_reject_code("`\\00`", "PS0025");
  assert_reject_code("`\\37`", "PS0025");
  assert_reject_code("'use strict'; `${test}\\02`;", "PS0025");
  // Tagged templates still allow invalid escapes (cooked undefined).
  assert_accept("tag`\\07`");
  assert_accept("`\\0`");
  assert_accept("`\\x41`");
}

#[test]
fn update_operand_must_be_simple_ecma_13_4() {
  assert_reject_code("1++", "PS0026");
  assert_reject_code("1--", "PS0026");
  assert_reject_code("++1", "PS0026");
  assert_reject_code("--1", "PS0026");
  assert_reject("a++``");
  assert_accept("a++");
  assert_accept("++a");
  assert_accept("a.b++");
  assert_accept("a[b]--");
}

#[test]
fn nullish_cannot_mix_with_logical_and_or() {
  // ECMA-262 ShortCircuitExpression — test262 coalesce/cannot-chain-*.
  assert_reject_code("0 && 0 ?? true", "PS0027");
  assert_reject_code("0 || 0 ?? true", "PS0027");
  assert_reject_code("true ?? 0 && 0", "PS0027");
  assert_reject_code("true ?? 0 || 0", "PS0027");
  assert_accept("0 && (0 ?? true)");
  assert_accept("(0 && 0) ?? true");
  assert_accept("true ?? (0 && 0)");
  assert_accept("(true ?? 0) && 0");
  assert_accept("a ?? b ?? c");
  assert_accept("a && b || c");
}

#[test]
fn escaped_await_yield_forbidden_in_async_generator_bodies() {
  // BindingIdentifier / IdentifierReference / LabelIdentifier [Await]/[Yield].
  assert_reject("async function(){ var \\u0061wait; }");
  assert_reject("async function(){ void \\u0061wait; }");
  assert_reject("async function(){ \\u0061wait: ; }");
  assert_reject("function*(){ var yi\\u0065ld; }");
  assert_reject("function*(){ void yi\\u0065ld; }");
  assert_reject("function*(){ yi\\u0065ld: ; }");
  // Strict reserved words also key off StringValue (test262 value-yield-strict-escaped).
  assert_reject("'use strict'; yi\\u0065ld: 1;");
  assert_reject("'use strict'; var yi\\u0065ld;");
  // Module: `await` is reserved at the goal-symbol level (escaped label).
  assert_reject_module("aw\\u0061it: 1;");
  assert_accept("async function f(){ var yield; }"); // non-generator async: Yield unset
  assert_accept("function f(){ var \\u0061wait; }"); // non-async script: Await unset
  assert_accept("async function f(){ await 1; }");
  assert_accept("function* f(){ yield 1; }");
  assert_accept("yi\\u0065ld: 1;"); // non-strict script: yield label ok when Yield unset
}

#[test]
fn optional_chain_cannot_be_tagged_template() {
  // ECMA-262 OptionalChain early errors — test262 optional-chaining/early-errors-tail-*.
  assert_reject_code("a?.fn`hello`", "PS0028");
  assert_reject_code("null?.fn`hello`", "PS0028");
  assert_reject_code("a?.b.c`hello`", "PS0028");
  assert_reject_code("a?.()`hello`", "PS0028");
  assert_reject_code("a?.`hello`", "PS0028");
  assert_accept("a.fn`hello`");
  assert_accept("(a?.fn)`hello`");
  assert_accept("a?.fn");
}

#[test]
fn for_of_lhs_must_not_start_with_let() {
  assert_reject("for(let.a of 0);");
  assert_accept("for(let.a in 0);");
  assert_accept("for(a.b of 0);");
}

#[test]
fn do_while_rejects_semicolon_between_body_and_while() {
  // test262 asi/S7.9_A9_T8 — `do {}; while (false)` is not a DoWhileStatement.
  assert_reject("do {};\nwhile (false)");
  assert_accept("do {} while (false);");
  assert_accept("do ;\nwhile (false);");
  assert_accept("do foo();\nwhile (false);");
}

#[test]
fn switch_rejects_duplicate_default_clause() {
  // test262 statements/switch/S12.11_A2_T1
  assert_reject("switch (0) { default: break; default: break; }");
  assert_accept("switch (0) { case 0: break; default: break; }");
}

#[test]
fn class_static_block_forbids_await_label_and_ref() {
  // test262 labeled/static-init-invalid-await + identifier-resolution sibling.
  assert_reject("class C { static { await: 0; } }");
  assert_reject("class C { static { await; } }");
  assert_accept("class C { static { let x = 1; } }");
}

#[test]
fn let_newline_await_no_asi_in_async_function() {
  // test262 async-function/let-newline-await-in-async-function — `await` still
  // starts LexicalDeclaration grammatically; no ASI before it; then rejects.
  assert_reject("async function f(){ let\nawait 0; }");
  assert_accept("async function f(){ let\nx = 0; }");
  assert_accept("async function f(){ let x; await 0; }");
}

#[test]
fn syntax_error_type_codes_are_stable() {
  assert_eq!(
    SyntaxErrorType::DeclarationInSingleStatementPosition.code(),
    "PS0018"
  );
  assert_eq!(
    SyntaxErrorType::BindingPatternRequiresInitializer.code(),
    "PS0019"
  );
  assert_eq!(
    SyntaxErrorType::UnterminatedMultilineComment.code(),
    "PS0020"
  );
  assert_eq!(SyntaxErrorType::InvalidRestParameter.code(), "PS0021");
  assert_eq!(
    SyntaxErrorType::NumericLiteralFollowedByIdentifier.code(),
    "PS0022"
  );
  assert_eq!(SyntaxErrorType::HtmlCommentInModule.code(), "PS0023");
  assert_eq!(SyntaxErrorType::InvalidClassHeritage.code(), "PS0024");
  assert_eq!(
    SyntaxErrorType::LegacyOctalEscapeInTemplate.code(),
    "PS0025"
  );
  assert_eq!(SyntaxErrorType::InvalidUpdateOperand.code(), "PS0026");
  assert_eq!(
    SyntaxErrorType::MixedNullishLogicalOperators.code(),
    "PS0027"
  );
  assert_eq!(
    SyntaxErrorType::OptionalChainTaggedTemplate.code(),
    "PS0028"
  );
  assert_eq!(SyntaxErrorType::InvalidPrivateIdentifier.code(), "PS0029");
}

#[test]
fn private_identifier_in_expression_ecma_12_10() {
  // RelationalExpression[+In]: PrivateIdentifier in ShiftExpression.
  // Nested `#a in #b in c` is illegal (RHS must be ShiftExpression).
  assert_reject_code(
    "class C { #field; constructor() { #field in #field in this; } }",
    "PS0029",
  );
  // Bare PrivateIdentifier is not a PrimaryExpression / assignment target.
  assert_reject_code("#x;", "PS0029");
  assert_reject_code("class C { #field; m() { for (#field in []) ; } }", "PS0029");
  assert_reject_code(
    "class C { #field; m() { return !#field in this; } }",
    "PS0029",
  );
  assert_reject_code(
    "class C { #field; m(o) { return void #field in o; } }",
    "PS0029",
  );

  // Legal neighbours.
  assert_accept("class C { #field; constructor() { #field in this; } }");
  assert_accept("class C { #field; m() { (#field in this) in this; } }");
  assert_accept("class C { #field; m() { return #field in this < 1; } }");
  assert_accept("class C { #field; *m(o) { yield #field in o; } }");
  assert_accept("class Outer { #x; m() { class Inner { n(o) { return #x in o; } } } }");
  assert_accept("class C { #f; m(o) { o.#f; } }");
}

#[test]
fn for_triple_allows_call_of_function_expr_in_init() {
  assert_accept(
    r#"for((function(){throw "NoInExpression"})(); ;(function(){throw "SecondExpression"})()) { throw "Statement"; }"#,
  );
  assert_accept(r#"for((function(){throw "x"})();;) { break; }"#);
  assert_accept(r#"for((function(){})();;) ;"#);
}

#[test]
fn optional_call_allows_whitespace_before_arguments() {
  assert_accept("fn?.(1,2)");
  assert_accept("fn ?. (1, 2)");
  assert_accept("fn ?. (...[1,2])");
  assert_accept("fn ?. [0]");
}
