//! JSDoc `@this {…}` under checkJs (tsc `jsdoc/inferThis.ts`): an explicit
//! `@this` tag wins over the class-derived `this` type inside the annotated
//! function's body, so `@template T` + `@this {T}` + `@return {T}` type-checks
//! `return this;` against `T` (not against the class instance/static type).

mod common;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileKey, Host, HostError, MemoryHost, Program};

struct JsHost {
  inner: MemoryHost,
}

impl JsHost {
  fn new() -> Self {
    let mut options = CompilerOptions::default();
    options.no_default_lib = true;
    options.no_implicit_any = false;
    options.check_js = Some(true);
    let mut inner = MemoryHost::with_options(options);
    inner.add_lib(common::core_globals_lib());
    Self { inner }
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

  fn lib_files(&self) -> Vec<typecheck_ts::lib_support::LibFile> {
    self.inner.lib_files()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    self.inner.file_kind(file)
  }
}

const INFER_THIS: &str = r#"export class C {
    /**
     * @template T
     * @this {T}
     * @return {T}
     */
    static a() {
        return this;
    }

    /**
     * @template T
     * @this {T}
     * @return {T}
     */
    b() {
        return this;
    }
}

const a = C.a();
a;

const c = new C();
const b = c.b();
b;
"#;

#[test]
fn this_tag_types_this_as_the_template_param() {
  let mut host = JsHost::new();
  let key = FileKey::new("a.js");
  host.inner.insert(key.clone(), INFER_THIS);
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "inferThis shape should check clean (tsc parity); got {diagnostics:?}"
  );
}

#[test]
fn this_tag_mismatch_still_reports() {
  // `@this` types `this`, it does not silence unrelated return checks:
  // returning a string against `@return {T}`-as-`this` mismatch surfaces.
  let src = r#"class D {
    /**
     * @template T
     * @this {T}
     * @return {number}
     */
    m() {
        return "s";
    }
}
"#;
  let mut host = JsHost::new();
  let key = FileKey::new("d.js");
  host.inner.insert(key.clone(), src);
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 for `return \"s\"` against @return {{number}}; got {diagnostics:?}"
  );
}
