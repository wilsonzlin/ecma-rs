mod common;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn infers_const_type_param_as_readonly_literal_object() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  host.insert(
    file.clone(),
    r#"
function asConst<const T>(value: T): T {
  return value;
}

export const inferred = asConst({ a: 1, b: "ok" });
"#,
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let inferred = exports
    .get("inferred")
    .expect("expected inferred export")
    .type_id
    .expect("expected inferred type");

  assert_eq!(
    program.display_type(inferred).to_string(),
    "{ readonly a: 1; readonly b: \"ok\" }"
  );
}
