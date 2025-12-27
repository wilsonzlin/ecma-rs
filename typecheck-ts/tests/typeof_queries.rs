use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn typeof_queries_in_libs_resolve_value_types() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("entry.ts");
  let source = "const t = window.document.title;";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id for entry");
  let offset = source.find("title").expect("title property offset") as u32;
  let ty = program
    .type_at(file_id, offset)
    .expect("type of window.document.title");
  assert_eq!(program.display_type(ty).to_string(), "string");
}
