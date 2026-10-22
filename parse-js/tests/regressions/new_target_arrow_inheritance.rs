//! `new.target` binding vs arrow transparency (ECMA-262).
//!
//! Spec: `new.target` is an early SyntaxError unless evaluated in a context with a
//! `new.target` binding — non-arrow function / method code, or class field /
//! static-block initialisers (§13.3.12 MetaProperty, plus static semantics for
//! function code). Arrow functions are transparent: they inherit an enclosing
//! binding and must not create one.
//!
//! Dialect: `Dialect::Ecma` enforces the early error; Js/Ts keep recovery acceptance
//! of outer `new.target` (see wiki `parse-js` § `new.target`).

use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn js_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

fn ts_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

fn assert_ecma_ok(src: &str) {
  parse_with_options(src, ecma_script()).unwrap_or_else(|err| {
    panic!("expected Ecma to accept {src:?}, got {err:?}");
  });
}

fn assert_ecma_err(src: &str) {
  let err =
    parse_with_options(src, ecma_script()).expect_err(&format!("expected Ecma to reject {src:?}"));
  let msg = format!("{err:?}");
  assert!(
    msg.contains("new.target"),
    "expected a new.target early-error diagnostic for {src:?}, got {err:?}"
  );
}

fn assert_recovery_ok(src: &str) {
  parse_with_options(src, js_script()).unwrap_or_else(|err| {
    panic!("expected Js recovery to accept {src:?}, got {err:?}");
  });
  parse_with_options(src, ts_script()).unwrap_or_else(|err| {
    panic!("expected Ts recovery to accept {src:?}, got {err:?}");
  });
}

#[test]
fn arrow_inside_function_inherits_new_target_binding() {
  // (a) Arrows inside non-arrow function code inherit the binding.
  assert_ecma_ok("function f() { () => new.target }");
  assert_ecma_ok("function f() { (() => new.target)(); }");
  assert_ecma_ok("function f() { const g = () => new.target; }");
  assert_ecma_ok("function f() { return (() => new.target)(); }");
}

#[test]
fn arrow_in_default_parameter_is_function_code() {
  // (b) Parameter initialisers evaluate in the function binding environment.
  assert_ecma_ok("function f(g = () => new.target) {}");
  assert_ecma_ok("function f(g = (h = new.target) => h) {}");
  assert_ecma_ok("(function f(g = () => new.target) {})");
}

#[test]
fn top_level_arrow_new_target_rejected_in_ecma_accepted_in_js_ts() {
  // (c) No enclosing non-arrow binding at top level.
  assert_ecma_err("() => new.target");
  assert_ecma_err("(() => new.target)");
  assert_ecma_err("(() => new.target);");
  assert_recovery_ok("() => new.target");
  assert_recovery_ok("(() => new.target);");
}

#[test]
fn nested_function_provides_binding_not_outer() {
  // (d) Innermost non-arrow function supplies the binding.
  assert_ecma_ok("function f() { function g() { () => new.target } }");
  assert_ecma_ok("function f() { function g() { (() => new.target)(); } }");
}

#[test]
fn method_and_constructor_contexts_and_default_param_regression() {
  // (e) Methods / class fields; keep default-param `new.target` / `super()` working.
  assert_ecma_ok("class C { m() { () => new.target } }");
  assert_ecma_ok("class C { m() { (() => new.target)(); } }");
  assert_ecma_ok("class C { x = () => new.target; }");
  assert_ecma_ok("class C extends B { constructor(x = new.target) { super(); } }");
  assert_ecma_ok("class C extends B { constructor(x = () => new.target) { super(); } }");
  assert_ecma_ok("class B {} class A extends B { constructor(c = super()) {} }");
  assert_ecma_ok("({ m(b = new.target){} })");
}
