use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn export_assignment_synthesizes_default_export() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);
  host.add_lib(LibFile {
    key: FileKey::new("lib.d.ts"),
    name: Arc::from("lib.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(""),
  });

  let module = FileKey::new("m.ts");
  host.insert(
    module.clone(),
    Arc::from(
      "function foo(x: number): number { return x; }\n\
       export = foo;\n",
    ),
  );

  let program = Program::new(host, vec![module.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let module_id = program.file_id(&module).expect("module file id");
  let exports = program.exports_of(module_id);
  let default_entry = exports.get("default").expect("default export");
  let default_ty = default_entry.type_id.expect("type for default export");
  let rendered = program.display_type(default_ty).to_string();
  assert_ne!(
    rendered, "unknown",
    "default export type should not be unknown"
  );
  assert!(
    rendered.contains("=>"),
    "expected callable default export type, got {rendered}"
  );
}

#[test]
fn export_as_namespace_injects_global_binding() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);

  host.add_lib(LibFile {
    key: FileKey::new("umd.d.ts"),
    name: Arc::from("umd.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      "export as namespace UMD;\n\
       export const foo: number;\n",
    ),
  });

  // Regression: `export as namespace` without any other imports/exports should
  // still force module semantics so the binder can inject the global binding.
  host.add_lib(LibFile {
    key: FileKey::new("only_namespace.d.ts"),
    name: Arc::from("only_namespace.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("export as namespace OnlyNS;\n"),
  });

  let root = FileKey::new("main.ts");
  host.insert(root.clone(), Arc::from("/* noop */"));

  let program = Program::new(host, vec![root]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let globals = program.global_bindings();
  assert!(
    globals.contains_key("UMD"),
    "expected UMD global binding from export as namespace"
  );
  assert!(
    globals.contains_key("OnlyNS"),
    "expected OnlyNS global binding from export as namespace"
  );
}

#[test]
fn export_assignment_allows_export_as_namespace() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);

  host.add_lib(LibFile {
    key: FileKey::new("umd_export_assignment.d.ts"),
    name: Arc::from("umd_export_assignment.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      "declare function Foo(x: number): number;\n\
       export = Foo;\n\
       export as namespace Foo;\n",
    ),
  });

  let root = FileKey::new("main.ts");
  host.insert(root.clone(), Arc::from("/* noop */"));

  let program = Program::new(host, vec![root]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let globals = program.global_bindings();
  assert!(
    globals.contains_key("Foo"),
    "expected Foo global binding from export as namespace"
  );
}
