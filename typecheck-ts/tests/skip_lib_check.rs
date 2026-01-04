use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn skip_lib_check_suppresses_dts_type_diagnostics() {
  let lib_key = FileKey::new("broken.d.ts");
  let entry_key = FileKey::new("entry.ts");
  let lib_source = "declare const value: MissingType;";

  let build_program = |skip_lib_check: bool| {
    let mut options = CompilerOptions::default();
    options.no_default_lib = true;
    options.skip_lib_check = skip_lib_check;
    let mut host = MemoryHost::with_options(options);
    host.add_lib(LibFile {
      key: lib_key.clone(),
      name: Arc::from("broken.d.ts"),
      kind: FileKind::Dts,
      text: Arc::from(lib_source),
    });
    host.insert(entry_key.clone(), "/* noop */");
    Program::new(host, vec![entry_key.clone()])
  };

  let program = build_program(false);
  let lib_id = program
    .file_id(&lib_key)
    .expect("broken .d.ts file should be loaded");
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.primary.file == lib_id
        && diag.code.as_str() == codes::UNRESOLVED_TYPE_REFERENCE.as_str()),
    "expected unresolved type reference diagnostic from .d.ts when skip_lib_check is disabled, got {diagnostics:?}"
  );

  let program = build_program(true);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected .d.ts diagnostics to be suppressed when skip_lib_check is enabled, got {diagnostics:?}"
  );
}
