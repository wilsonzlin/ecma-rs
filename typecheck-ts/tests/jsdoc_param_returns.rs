//! JSDoc `@param` / `@returns` checking under checkJs.
//!
//! Extends the `@type` first slice: function declarations/expressions take
//! `@returns {T}` as the expected return type and `@param {T} name` as the
//! parameter type when there is no TypeScript annotation.

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
fn jsdoc_returns_bad_return_reports_ts2322() {
  let program = js_program(
    r#"
/**
 * @returns {number}
 */
function f() {
  return "no";
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from @returns vs string return; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_returns_good_return_is_silent() {
  let program = js_program(
    r#"
/**
 * @returns {number}
 */
function f() {
  return 1;
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
    "number return should satisfy @returns {{number}}; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_returns_on_function_expression_reports_ts2322() {
  let program = js_program(
    r#"
/**
 * @returns {number}
 */
var f = function () {
  return "no";
};
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 for @returns on function expression; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_param_bad_assignment_reports_ts2322() {
  let program = js_program(
    r#"
/**
 * @param {number} x
 */
function f(x) {
  /** @type {string} */
  var s = x;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 assigning number param to string; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_param_good_use_is_silent() {
  let program = js_program(
    r#"
/**
 * @param {number} x
 * @returns {number}
 */
function f(x) {
  return x;
}
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
    "good @param/@returns should be silent; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_param_bad_call_arg_reports_ts2345() {
  let program = js_program(
    r#"
/**
 * @param {number} x
 */
function f(x) {}
f("no");
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::ARGUMENT_TYPE_MISMATCH.as_str())
      || has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2345/TS2322 for bad call arg vs @param; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_nested_param_opts_x_bad_call_reports_mismatch() {
  let program = js_program(
    r#"
/**
 * @param {object} opts
 * @param {number} opts.x
 */
function f(opts) {}
f({ x: "no" });
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::ARGUMENT_TYPE_MISMATCH.as_str())
      || has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected mismatch for opts.x: number vs string; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_nested_param_opts_x_good_call_is_silent() {
  let program = js_program(
    r#"
/**
 * @param {object} opts
 * @param {number} opts.x
 */
function f(opts) {
  return opts.x;
}
f({ x: 1 });
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::JSDOC_QUALIFIED_PARAM_MISSING_PARENT.as_str()
    })
    .collect();
  assert!(
    mismatches.is_empty(),
    "nested @param opts.x should type opts as {{ x: number }}; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_nested_param_without_top_level_object_reports_ts8032() {
  let program = js_program(
    r#"
/**
 * @param {number} xyz.p
 */
function g(xyz) {
  return xyz.p;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(
      &diagnostics,
      codes::JSDOC_QUALIFIED_PARAM_MISSING_PARENT.as_str()
    ),
    "expected TS8032 for xyz.p without @param {{object}} xyz; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_nested_param_deep_without_intermediate_reports_ts8032() {
  let program = js_program(
    r#"
/**
 * @param {object} xyz
 * @param {number} xyz.bar.p
 */
function g(xyz) {
  return xyz.bar.p;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(
      &diagnostics,
      codes::JSDOC_QUALIFIED_PARAM_MISSING_PARENT.as_str()
    ),
    "expected TS8032 for xyz.bar.p without @param {{object}} xyz.bar; got {diagnostics:?}"
  );
  let diag = diagnostics
    .iter()
    .find(|d| d.code.as_str() == codes::JSDOC_QUALIFIED_PARAM_MISSING_PARENT.as_str())
    .unwrap();
  assert!(
    diag.message.contains("xyz.bar.p") && diag.message.contains("xyz.bar"),
    "message should name the qualified path and parent; got {}",
    diag.message
  );
}

#[test]
fn jsdoc_unmatched_root_param_reports_ts8024() {
  // Upstream jsdocParamTagTypeLiteral: root `@param unrelated` with no matching
  // function parameter (nested opts.x sugar must remain silent).
  let program = js_program(
    r#"
/**
 * @param {Object} notSpecial
 * @param {string} unrelated
 */
function normal(notSpecial) {
  notSpecial;
}

/**
 * @param {Object} opts1
 * @param {string} opts1.x
 */
function foo1(opts1) {
  opts1.x;
}
"#,
  );
  let diagnostics = program.check();
  let unused: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::JSDOC_PARAM_TAG_UNUSED.as_str())
    .collect();
  assert_eq!(
    unused.len(),
    1,
    "expected exactly one TS8024 for unrelated; got {diagnostics:?}"
  );
  assert!(
    unused[0].message.contains("'unrelated'"),
    "message should name unrelated; got {}",
    unused[0].message
  );
}

#[test]
fn jsdoc_unmatched_param_on_multi_declarator_reports_ts8024() {
  // Upstream checkJsdocParamOnVariableDeclaredFunctionExpression: JSDoc on a
  // multi-declarator `var` is visible to every function initializer; the second
  // has no parameter `s`.
  let program = js_program(
    r#"
/**
 * @param {string} s
 */
var one = function (s) { }, two = function (untyped) { };
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::JSDOC_PARAM_TAG_UNUSED.as_str()),
    "expected TS8024 for @param s vs function(untyped); got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_matched_root_param_is_silent_for_ts8024() {
  let program = js_program(
    r#"
/**
 * @param {string} s
 */
function f(s) {
  return s;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    !has_code(&diagnostics, codes::JSDOC_PARAM_TAG_UNUSED.as_str()),
    "matched @param should not emit TS8024; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_unmatched_y_with_destructured_obj_reports_ts8024() {
  // Upstream jsdocParamTag2 bad2.
  let program = js_program(
    r#"
/**
 * @param {string} y
 * @param {{a: string, b: string}} obj
 */
function bad2(x, {a, b}) {}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::JSDOC_PARAM_TAG_UNUSED.as_str()),
    "expected TS8024 for @param y; got {diagnostics:?}"
  );
}
