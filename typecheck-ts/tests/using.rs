use diagnostics::TextRange;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, LibName, ScriptTarget};
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn using_accepts_disposable_initializer() {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  options.libs = vec![
    LibName::parse("es5").expect("es5 lib"),
    LibName::parse("esnext.disposable").expect("esnext.disposable lib"),
  ];
  let mut host = MemoryHost::with_options(options);

  let file = FileKey::new("main.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
class D {
  [Symbol.dispose](): void {}
}

using x = new D();
"#
      .to_string(),
    ),
  );

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn using_rejects_non_disposable_initializer() {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  options.libs = vec![
    LibName::parse("es5").expect("es5 lib"),
    LibName::parse("esnext.disposable").expect("esnext.disposable lib"),
  ];
  let mut host = MemoryHost::with_options(options);

  let file = FileKey::new("main.ts");
  host.insert(file.clone(), Arc::from("using x = 123;".to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::INVALID_USING_INITIALIZER.as_str()),
    "expected invalid using initializer diagnostic, got {diagnostics:?}"
  );
}

#[test]
fn await_using_requires_async_context() {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  options.libs = vec![
    LibName::parse("es5").expect("es5 lib"),
    LibName::parse("esnext.disposable").expect("esnext.disposable lib"),
  ];
  let mut host = MemoryHost::with_options(options);

  let file = FileKey::new("main.ts");
  let source = r#"
class AsyncD {
  async [Symbol.asyncDispose](): PromiseLike<void> {}
}

function bad() {
  await using x = new AsyncD();
}
"#;
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let diag = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::AWAIT_USING_REQUIRES_ASYNC_CONTEXT.as_str())
    .unwrap_or_else(|| panic!("expected TS2852 diagnostic, got {diagnostics:?}"));

  let start = source.find("await using").expect("await using in source") as u32;
  let end = start + "await".len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

#[test]
fn await_using_allowed_in_async_function() {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  options.libs = vec![
    LibName::parse("es5").expect("es5 lib"),
    LibName::parse("esnext.disposable").expect("esnext.disposable lib"),
  ];
  let mut host = MemoryHost::with_options(options);

  let file = FileKey::new("main.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
class AsyncD {
  async [Symbol.asyncDispose](): PromiseLike<void> {}
}

async function ok() {
  await using x = new AsyncD();
}
"#
      .to_string(),
    ),
  );

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}
