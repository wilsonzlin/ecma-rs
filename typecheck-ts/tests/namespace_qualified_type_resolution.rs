use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn resolves_jsx_namespace_members_in_type_positions() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  host.add_lib(LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      "declare namespace JSX { interface Element {} interface IntrinsicElements { div: {} } }",
    ),
  });

  let entry = FileKey::new("entry.ts");
  host.insert(
    entry.clone(),
    "let el: JSX.Element;\nlet intrinsic: JSX.IntrinsicElements;",
  );

  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected JSX qualified types to resolve, got {diagnostics:?}"
  );
}

#[test]
fn resolves_nested_namespace_members_in_type_positions() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  host.add_lib(LibFile {
    key: FileKey::new("namespaces.d.ts"),
    name: Arc::from("namespaces.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("declare namespace A { namespace B { interface C {} } }"),
  });

  let entry = FileKey::new("entry.ts");
  host.insert(entry.clone(), "let value: A.B.C;");

  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected nested namespace qualified types to resolve, got {diagnostics:?}"
  );
}
