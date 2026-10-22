//! JSDoc `@type` checking under checkJs (first slice).
//!
//! parse-js does not attach comments to AST nodes, so the checker scans source
//! text for a leading `/** … */` before a declaration and treats `@type {…}`
//! as the declared type when there is no TypeScript annotation.

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

#[test]
fn jsdoc_type_bad_initializer_reports_ts2322() {
  let program = js_program(
    r#"
/** @type {number} */
var x = "no";
"#,
  );
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 from JSDoc @type vs string initializer; got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_type_good_initializer_is_silent() {
  let program = js_program(
    r#"
/** @type {number} */
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
    "number initializer should satisfy @type {{number}}; got {mismatches:?} (all: {diagnostics:?})"
  );
}

#[test]
fn jsdoc_type_same_line_bad_initializer_reports_ts2322() {
  let program = js_program(r#"/** @type {number} */ var x = "no";"#);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 for same-line JSDoc @type; got {diagnostics:?}"
  );
}
