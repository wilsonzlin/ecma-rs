//! checkJs / CommonJS ambient globals.
//!
//! Under allowJs+checkJs, tsc treats `require` / `module` / `exports` as ambient
//! values only when a `.js` file sets `commonJsModuleIndicator` (public
//! `exports.foo =`, `module.exports =`, or `require(...)`). Private access
//! like `exports.#nope` does not seed `exports`. `globalThis` is always a
//! checker-synthesized global. These tests lock that without claiming typed
//! Node `require` signatures.

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileKey, Host, HostError, MemoryHost, Program};

/// Host that forces `.js` keys to [`FileKind::Js`] (MemoryHost already infers
/// this from the extension; this keeps the intent explicit for the fixture).
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
    assert_eq!(
      kind,
      FileKind::Js,
      "fixture paths should be .js so CommonJS ambients are seeded"
    );
    kind
  }
}

#[test]
fn check_js_commonjs_globals_are_not_unresolved() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.no_implicit_any = false;
  options.check_js = Some(true);
  let mut host = JsHost::new(options);
  let key = FileKey::new("mod.js");
  host.insert(
    key.clone(),
    r#"
var fs = require("fs");
module.exports = { fs: fs };
exports.ready = true;
var g = globalThis;
"#,
  );
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  let unresolved: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::CANNOT_FIND_NAME.as_str()
        || d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str()
    })
    .collect();
  assert!(
    unresolved.is_empty(),
    "require/module/exports/globalThis should resolve as ambients in .js; got {unresolved:?} (all: {diagnostics:?})"
  );
}

#[test]
fn ts_files_still_report_unresolved_require() {
  // Boundary: CommonJS ambients are JS-file-scoped. A `.ts` file without
  // `@types/node` should still get TS2304 for bare `require`.
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);
  let key = FileKey::new("mod.ts");
  host.insert(key.clone(), "const fs = require(\"fs\");\n");
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics.iter().any(|d| {
      d.code.as_str() == codes::CANNOT_FIND_NAME.as_str() && d.message.contains("require")
    }),
    "expected TS2304 for require in .ts without Node types; got {diagnostics:?}"
  );
}

#[test]
fn exports_private_access_does_not_seed_commonjs_exports() {
  // Mirrors conformance `privateNameJsBadAssignment.js`: `exports.#nope = 1`
  // is not an ExportsProperty assignment, so tsc leaves `exports` unbound.
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.no_implicit_any = false;
  options.check_js = Some(true);
  let mut host = JsHost::new(options);
  let key = FileKey::new("privateNameJsBadAssignment.js");
  host.insert(key.clone(), "exports.#nope = 1;\n");
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  let unresolved_exports: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::CANNOT_FIND_NAME.as_str() && d.message.contains("exports")
    })
    .collect();
  assert_eq!(
    unresolved_exports.len(),
    1,
    "expected TS2304 Cannot find name 'exports'; got {diagnostics:?}"
  );
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "TS18016"),
    "expected TS18016 on private access; got {diagnostics:?}"
  );
}

#[test]
fn public_exports_assignment_seeds_exports_ambient() {
  // Boundary: a public `exports.foo =` *does* set the CommonJS indicator.
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.no_implicit_any = false;
  options.check_js = Some(true);
  let mut host = JsHost::new(options);
  let key = FileKey::new("mod.js");
  host.insert(key.clone(), "exports.ready = true;\n");
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  let unresolved: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::CANNOT_FIND_NAME.as_str()
        || d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str()
    })
    .collect();
  assert!(
    unresolved.is_empty(),
    "public exports.foo= should seed exports ambient; got {unresolved:?} (all: {diagnostics:?})"
  );
}

#[test]
fn bare_exports_ident_without_cjs_indicator_is_ts2304() {
  // No require / module.exports / public exports.prop= → unresolved.
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.check_js = Some(true);
  let mut host = JsHost::new(options);
  let key = FileKey::new("mod.js");
  host.insert(key.clone(), "var x = exports;\n");
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics.iter().any(|d| {
      d.code.as_str() == codes::CANNOT_FIND_NAME.as_str() && d.message.contains("exports")
    }),
    "bare exports without CJS indicator must be TS2304; got {diagnostics:?}"
  );
}

#[test]
fn js_file_without_check_js_is_parse_only() {
  // tsc `allowJs` without `checkJs`: the `.js` file is parsed but produces no
  // semantic diagnostics — not even TS2304/TS2307 (verified vs tsc 5.9).
  // Mirrors conformance `es6/computedProperties/computedPropertyNames52.ts`.
  let options = CompilerOptions::default();
  let mut host = JsHost::new(options);
  let key = FileKey::new("mod.js");
  host.insert(
    key.clone(),
    "var x = missing_name;\nimport { y } from \"./does-not-exist\";\nx = y;\n",
  );
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert_eq!(
    diagnostics,
    Vec::new(),
    "no-checkJs .js file must be parse-only; got {diagnostics:?}"
  );
}

#[test]
fn js_file_without_check_js_keeps_parse_errors() {
  // Parse/grammar diagnostics survive the checkJs gate (tsc reports e.g.
  // TS1005 in allowJs-only JS files).
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = JsHost::new(options);
  let key = FileKey::new("mod.js");
  host.insert(key.clone(), "const x = ;\n");
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str().starts_with("PS") || d.code.as_str() == "TS1005"),
    "parse error must survive the checkJs gate; got {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .all(|d| d.code.as_str().starts_with("PS") || d.code.as_str() == "TS1005"),
    "only parse diagnostics may survive the checkJs gate; got {diagnostics:?}"
  );
}
