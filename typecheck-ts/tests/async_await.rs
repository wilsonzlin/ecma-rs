use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn promise_lib() -> LibFile {
  LibFile {
    key: FileKey::new("core_promise.d.ts"),
    name: Arc::from("core_promise.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
interface Promise<T> {
  then(onfulfilled: (value: T) => any): any;
}
"#,
    ),
  }
}

#[test]
fn async_function_returns_promise_and_await_unwraps() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  host.add_lib(promise_lib());
  let file = FileKey::new("a.ts");
  let source = r#"
async function foo() { return 1; }
async function bar() { const x = await foo(); return x; }
export const p = foo();
export const q = bar();
"#;
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let p_ty = exports
    .get("p")
    .and_then(|entry| entry.type_id)
    .expect("type for export p");
  assert_eq!(program.display_type(p_ty).to_string(), "Promise<number>");
  let q_ty = exports
    .get("q")
    .and_then(|entry| entry.type_id)
    .expect("type for export q");
  assert_eq!(program.display_type(q_ty).to_string(), "Promise<number>");

  let x_offset = source.find("return x").expect("return x offset") as u32 + "return ".len() as u32;
  let x_ty = program
    .type_at(file_id, x_offset)
    .expect("type of x reference");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn async_return_annotation_checked_against_awaited() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  host.add_lib(promise_lib());
  let file = FileKey::new("a.ts");
  let source = "export async function foo(): Promise<number> { return 1; }";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}
