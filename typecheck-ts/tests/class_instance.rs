use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, PatId, Program};

#[test]
fn class_instance_type_from_declaration() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let source = r#"class Greeter { greet(): string { return "hi"; } }
let g: Greeter = new Greeter();
const s = g.greet();
"#;
  let file = FileKey::new("entry.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .all(|d| d.severity != diagnostics::Severity::Error),
    "diagnostics: {:?}",
    diagnostics
  );

  let file_id = program.file_id(&file).expect("file id");
  let defs = program.definitions_in_file(file_id);
  let s_def = defs
    .iter()
    .copied()
    .find(|d| program.def_name(*d).as_deref() == Some("s"))
    .expect("s def");
  assert_eq!(
    program.display_type(program.type_of_def(s_def)).to_string(),
    "string"
  );
  let s_body = program.body_of_def(s_def).expect("s body");
  let body_result = program.check_body(s_body);
  let pat_ty = body_result
    .pat_type(PatId(0))
    .map(|ty| program.display_type(ty).to_string());
  assert_eq!(pat_ty.as_deref(), Some("string"));
  let offset = source.find("s =").expect("offset of s") as u32;
  let ty = program.type_at(file_id, offset);
  let ty = ty.expect("type at s");
  assert_eq!(program.display_type(ty).to_string(), "string");
}
