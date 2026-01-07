use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn compiler_options_types_includes_ambient_type_packages() {
  let mut options = CompilerOptions::default();
  options.types = vec!["example".to_string()];
  options.no_default_lib = true;

  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  let entry = FileKey::new("entry.ts");
  let types = FileKey::new("example.d.ts");

  host.insert(entry.clone(), Arc::from("const value = example;"));
  host.insert(types.clone(), Arc::from("declare const example: string;"));
  host.link(entry.clone(), "example", types);

  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
}
