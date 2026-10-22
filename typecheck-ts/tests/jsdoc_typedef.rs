//! JSDoc `@typedef` / `@template` checking under checkJs.
//!
//! Builds on `@type` / `@param` / `@returns`: file-scope `@typedef` names
//! resolve in later tags, including `@property` object shapes and CommonJS
//! qualified names (`exports.Foo`, nameless typedef on `exports.Foo = …`).
//! `@template` registers function/class type parameters when there is no TS
//! type-parameter list; class templates attach to construct signatures for
//! `new` call-site inference.

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileKey, Host, HostError, MemoryHost, Program};

struct JsHost {
  inner: MemoryHost,
}

impl JsHost {
  fn new(options: CompilerOptions) -> Self {
    Self {
      inner: MemoryHost::with_options(options),
    }
  }

  fn insert(&mut self, key: FileKey, source: &str) {
    self.inner.insert(key, source);
  }
}

impl Host for JsHost {
  fn file_text(&self, file: &FileKey) -> Result<std::sync::Arc<str>, HostError> {
    self.inner.file_text(file)
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    self.inner.resolve(from, specifier)
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.inner.compiler_options()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    let kind = self.inner.file_kind(file);
    assert_eq!(kind, FileKind::Js, "fixture paths should be .js");
    kind
  }
}

fn js_program(source: &str) -> Program {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.no_implicit_any = false;
  options.check_js = Some(true);
  let mut host = JsHost::new(options);
  let key = FileKey::new("mod.js");
  host.insert(key.clone(), source);
  Program::new(host, vec![key])
}

fn has_code(diagnostics: &[typecheck_ts::Diagnostic], code: &str) -> bool {
  diagnostics.iter().any(|d| d.code.as_str() == code)
}

#[test]
fn jsdoc_typedef_alias_bad_initializer_reports_ts2322() {
  let program = js_program(
    r#"
/**
 * @typedef {number} Num
 */
/** @type {Num} */
var x = "no";
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from @typedef alias vs string initializer; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_typedef_alias_good_initializer_is_silent() {
  let program = js_program(
    r#"
/**
 * @typedef {number} Num
 */
/** @type {Num} */
var x = 1;
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert!(
    mismatches.is_empty(),
    "number should satisfy @typedef Num; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_typedef_object_property_bad_call_arg_reports_mismatch() {
  let program = js_program(
    r#"
/**
 * @typedef {Object} Opts
 * @property {string} x
 * @property {number} [y]
 *
 * @param {Opts} opts
 */
function foo(opts) {}
foo({ x: 1 });
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::ARGUMENT_TYPE_MISMATCH.as_str())
      || has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2345/TS2322 for bad @typedef object property; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_typedef_object_property_good_call_is_silent() {
  let program = js_program(
    r#"
/**
 * @typedef {Object} Opts
 * @property {string} x
 *
 * @param {Opts} opts
 */
function foo(opts) {}
foo({ x: "ok" });
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str()
    })
    .collect();
  assert!(
    mismatches.is_empty(),
    "good @typedef object arg should be silent; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_typedef_used_via_type_tag_on_var_reports_ts2322() {
  let program = js_program(
    r#"
/**
 * @typedef {Object} Point
 * @property {number} x
 * @property {number} y
 */
/** @type {Point} */
var p = { x: 1, y: "no" };
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 for bad @typedef object initializer; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_template_param_not_assignable_to_concrete_return_reports_ts2322() {
  // Relate treats naked type params as only assignable to any/unknown, so
  // `@returns {string}` + `return x` (x: T) is a real TS2322 once `@template`
  // is registered (without it, `{T}` lowered to `any` and the return was ok).
  let program = js_program(
    r#"
/**
 * @template T
 * @param {T} x
 * @returns {string}
 */
function f(x) {
  return x;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 returning type param T as string; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_template_identity_return_is_silent() {
  let program = js_program(
    r#"
/**
 * @template T
 * @param {T} x
 * @returns {T}
 */
function id(x) {
  return x;
}
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert!(
    mismatches.is_empty(),
    "returning param T should satisfy @returns {{T}}; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_typedef_exports_qualified_name_resolves() {
  let program = js_program(
    r#"
/**
 * @typedef {string} exports.Foo
 */
/** @type {exports.Foo} */
var x = 1;
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 for number vs exports.Foo string typedef; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_typedef_exports_qualified_name_good_is_silent() {
  let program = js_program(
    r#"
/**
 * @typedef {string} exports.Foo
 */
/** @type {exports.Foo} */
var x = "ok";
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert!(
    mismatches.is_empty(),
    "string should satisfy exports.Foo; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_nameless_typedef_on_exports_assign_resolves_short_and_qualified() {
  let program = js_program(
    r#"
/**
 * @typedef {string}
 */
exports.Foo = {};
/** @type {exports.Foo} */
var x = 1;
/** @type {Foo} */
var y = 2;
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert!(
    mismatches.len() >= 2,
    "expected TS2322 for both exports.Foo and Foo; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_nameless_typedef_on_bare_exports_reports_ts2694() {
  let program = js_program(
    r#"
var exports = {};
/**
 * @typedef {string}
 */
exports.SomeName;
/** @type {exports.SomeName} */
const myString = 'str';
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "expected TS2694 for bare exports.SomeName typedef host; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_template_call_site_infers_and_rejects_bad_assignment() {
  // Identity @template: call-site should instantiate T from the argument so
  // assigning the result to a string is TS2322 when the arg is a number.
  let program = js_program(
    r#"
/**
 * @template T
 * @param {T} x
 * @returns {T}
 */
function id(x) {
  return x;
}
/** @type {string} */
var s = id(1);
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from instantiated @template return vs string; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_template_class_constructor_instantiation_rejects_cross_instance_assign() {
  let program = js_program(
    r#"
/** @template T */
class Foo {
  /** @param {T} x */
  constructor(x) {
    this.a = x;
  }
}
var f = new Foo(1);
var g = new Foo(false);
f.a = g.a;
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 assigning Foo<boolean>.a to Foo<number>.a; got {diagnostics:?}"
  );
}
