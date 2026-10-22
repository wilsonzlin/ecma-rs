//! JSDoc inline object / function type literals under checkJs.
//!
//! Extends `@type` / `@param` / `@returns`: braced object shapes (`{a: string}`)
//! and function types (`function(string): number`, `(s: string) => void`) lower
//! into interned object / callable types for assignability and contextual typing.

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

fn js_program_strict_implicit_any(source: &str) -> Program {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.no_implicit_any = true;
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
fn jsdoc_inline_object_type_bad_initializer_reports_ts2322() {
  let program = js_program(
    r#"
/** @type {{ a: string }} */
var x = { a: 1 };
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from inline object @type; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_inline_object_type_good_initializer_is_silent() {
  let program = js_program(
    r#"
/** @type {{ a: string, b?: number }} */
var x = { a: "ok" };
"#,
  );
  let diagnostics = program.check();
  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert!(
    mismatches.is_empty(),
    "good inline object should be silent; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_inline_object_param_bad_call_reports_mismatch() {
  let program = js_program(
    r#"
/**
 * @param {{ x: string }} opts
 */
function foo(opts) {}
foo({ x: 1 });
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::ARGUMENT_TYPE_MISMATCH.as_str())
      || has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2345/TS2322 for bad inline object param; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_closure_function_type_contextual_param_reports_ts2322() {
  let program = js_program(
    r#"
/** @type {function(string): void} */
const f = (value) => {
  value = 1;
};
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from contextual string param vs number; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_ts_arrow_function_type_on_decl_reports_ts2322() {
  let program = js_program(
    r#"
/** @type {(s: string) => void} */
function g(s) {
  s = 1;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from @type arrow signature on function decl; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_function_type_bad_call_arg_reports_mismatch() {
  let program = js_program(
    r#"
/**
 * @param {function(string): number} fn
 */
function call(fn) {
  return fn("ok");
}
call((n) => n);
call((n) => 1);
"#,
  );
  // First call: callback returns string, expected number → mismatch.
  // Second call: ok.
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::ARGUMENT_TYPE_MISMATCH.as_str())
      || has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected mismatch for callback returning string; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_function_type_suppresses_implicit_any_on_params() {
  let program = js_program_strict_implicit_any(
    r#"
/** @type {function(string): void} */
const f = (value) => {
  value;
};
"#,
  );
  let diagnostics = program.check();
  assert!(
    !has_code(&diagnostics, codes::IMPLICIT_ANY.as_str()),
    "contextual @type function params should not be implicit any; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_ts_arrow_function_type_on_decl_no_implicit_any() {
  let program = js_program_strict_implicit_any(
    r#"
/** @type {(s: string) => void} */
function g(s) {
  s = 1;
}
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected TS2322; got {diagnostics:?}"
  );
  assert!(
    !has_code(&diagnostics, codes::IMPLICIT_ANY.as_str()),
    "expected no TC3000 when @type types the param; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_new_construct_signature_accepts_class() {
  let program = js_program_strict_implicit_any(
    r#"
/**
 * @param {function(new: { length: number }, number): number} c
 * @return {function(new: { length: number }, number): number}
 */
function id2(c) { return c; }
class C {
  /** @param {number} n */
  constructor(n) { this.length = n; }
}
var y = id2(C);
var z = new y(12);
z.length;
"#,
  );
  let diagnostics = program.check();
  let bad: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::TYPE_MISMATCH.as_str()
        || d.code.as_str() == "TC2000"
    })
    .collect();
  assert!(
    bad.is_empty(),
    "class with length should satisfy new: {{length:number}}; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_new_construct_signature_rejects_wrong_instance() {
  let program = js_program_strict_implicit_any(
    r#"
/**
 * @param {function(new: { length: number }, number)} c
 */
function id2(c) {}
/**
 * @constructor
 * @param {number} n
 */
function E(n) { this.not_length_on_purpose = n; }
id2(E);
"#,
  );
  let diagnostics = program.check();
  assert!(
    has_code(&diagnostics, codes::ARGUMENT_TYPE_MISMATCH.as_str())
      || has_code(&diagnostics, codes::TYPE_MISMATCH.as_str()),
    "expected mismatch for wrong instance shape; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_new_construct_signature_constructs() {
  let program = js_program_strict_implicit_any(
    r#"
/**
 * @param {function(new: { length: number }, number)} dref
 * @return {{ length: number }}
 */
function construct(dref) { return new dref(33); }
/**
 * @constructor
 * @param {number} n
 */
function D(n) { this.length = n; }
var z3 = construct(D);
z3.length;
"#,
  );
  let diagnostics = program.check();
  let bad: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == "TC2000" || d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str()
    })
    .collect();
  assert!(
    bad.is_empty(),
    "new: + @constructor should construct; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_this_param_function_type_accepts_callback() {
  // Use an object `this` type so the fixture does not depend on lib `String`.
  let program = js_program_strict_implicit_any(
    r#"
/**
 * @param {function(this: { length: number }, number): number} c
 * @return {function(this: { length: number }, number): number}
 */
function id1(c) { return c; }
var x = id1(function (n) { return this.length + n });
"#,
  );
  let diagnostics = program.check();
  // Filter lib noise.
  let bad: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::TYPE_MISMATCH.as_str()
    })
    .collect();
  assert!(
    bad.is_empty(),
    "this: string callback should be accepted; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_function_type_with_literal_unions() {
  let program = js_program(
    r#"
/** @type {function ("a" | "b", 1 | 2): 3 | 4} */
var f = function (ab, onetwo) { return ab === "a" ? 3 : 4; };
"#,
  );
  let diagnostics = program.check();
  let bad: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert!(
    bad.is_empty(),
    "literal union function type should accept matching body; got {diagnostics:?}"
  );
}
