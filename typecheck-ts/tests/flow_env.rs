use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind as LibFileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn flow_env_prefers_local_shadowing_globals() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);

  let lib_key = FileKey::new("lib.d.ts");
  host.add_lib(LibFile {
    key: lib_key.clone(),
    name: Arc::from("lib.d.ts"),
    kind: LibFileKind::Dts,
    text: Arc::from("declare const undefined: undefined;"),
  });

  let file = FileKey::new("entry.ts");
  let source = "function f() { let undefined = 123; return undefined; }";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );

  let file_id = program.file_id(&file).expect("file id");
  let def_f = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("f"))
    .expect("function definition");
  let body = program.body_of_def(def_f).expect("function body");

  let result = program.check_body(body);
  assert!(
    result.diagnostics().is_empty(),
    "body diagnostics: {:?}",
    result.diagnostics()
  );

  let return_ty = result
    .return_types()
    .first()
    .copied()
    .expect("return type present");
  assert_eq!(program.display_type(return_ty).to_string(), "number");
}
