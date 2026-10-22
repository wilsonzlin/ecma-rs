//! YieldExpression disallowed in FormalParameters / ArrowParameters (§15.5.1, §15.1.1).
//!
//! Generator (and nested-arrow-in-generator) parameter lists must not contain
//! `yield` as a YieldExpression. Sloppy non-generator `function f(yield){}` and
//! generator *bodies* remain legal.

use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn assert_reject(src: &str) {
  assert!(
    parse_with_options(src, ecma_script()).is_err(),
    "expected reject: {src:?}"
  );
}

fn assert_accept(src: &str) {
  parse_with_options(src, ecma_script()).unwrap_or_else(|err| {
    panic!("expected accept {src:?}, got {err:?}");
  });
}

#[test]
fn yield_expression_in_generator_formal_parameters() {
  // Direct generator FormalParameters.
  assert_reject("function *a(b = yield){}");
  assert_reject("function* a(b = yield c){}");
  assert_reject("function* a(b = yield* c){}");
  assert_reject("!function*(b = yield){}");
  assert_reject("!function*([b = yield]){}");
  assert_reject("!function*({b = yield}){}");
  assert_reject("!function*({[yield]: b}){}");

  // Nested generator FormalParameters inside an outer generator.
  assert_reject("function* a(){ function* b(c = yield){} }");
  assert_reject("function* a(){ function* b(c = yield d){} }");
  assert_reject("function* a(){ function* b([c = yield]){} }");
  assert_reject("function* a(){ function* b({c = yield}){} }");
  assert_reject("function* a(){ function* b({[yield]: c}){} }");

  // Generator methods.
  assert_reject("({ *b(c = yield){} });");
  assert_reject("function* a(){ ({ *b(c = yield){} }); }");
  assert_reject("function* a(){ ({ *b({[yield]: c}){} }); }");
}

#[test]
fn yield_expression_in_arrow_params_inside_generator() {
  // ArrowParameters inherit [Yield] from the enclosing generator; Contains
  // YieldExpression is an early SyntaxError.
  assert_reject("function* a(){ (b = yield) => 1; }");
  assert_reject("function* a(){ (b = yield c) => 1; }");
  assert_reject("function* a(){ (b = yield* c) => 1; }");
  assert_reject("function* a(){ ([b = yield]) => 1; }");
  assert_reject("function* a(){ ({b = yield}) => 1; }");
  assert_reject("function* a(){ ({[yield]: b}) => 1; }");
}

#[test]
fn legal_yield_neighbours() {
  // Sloppy non-generator: `yield` is a BindingIdentifier / IdentifierReference.
  assert_accept("function f(yield){}");
  assert_accept("function f(a = yield){}");
  assert_accept("(yield) => 1;");
  assert_accept("(a = yield) => 1;");

  // Generator body may use YieldExpression; nested non-generator may use
  // `yield` as an identifier in sloppy mode.
  assert_accept("function* g(){ var yield_ok = 1; yield 1; }");
  assert_accept("function* g(){ function inner(a = yield){ return a; } }");
  assert_accept("function* g(){ (a) => a; }");
  assert_accept("function* g(){ yield; }");
}
