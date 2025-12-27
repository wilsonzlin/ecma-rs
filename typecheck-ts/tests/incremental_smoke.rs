use std::sync::Arc;

use typecheck_ts::{parse_call_count, reset_parse_call_count, FileKey, MemoryHost, Program};

#[test]
fn incremental_smoke() {
  reset_parse_call_count();
  let mut host = MemoryHost::new();
  let file = FileKey::new("file0.ts");
  host.insert(file.clone(), "export const value: number = 1;");

  let mut program = Program::new(host.clone(), vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty());

  reset_parse_call_count();
  let file_id = program.file_id(&file).unwrap();
  program.set_file_text(file_id, Arc::from("export const value: string = 1;"));
  let diagnostics = program.check();
  assert!(
    !diagnostics.is_empty(),
    "modified program should surface diagnostics"
  );
  assert!(
    parse_call_count() > 0,
    "changed sources should trigger parsing work"
  );

  let exports = program.exports_of(file_id);
  let value_ty = exports.get("value").and_then(|e| e.type_id).unwrap();
  assert_eq!(program.display_type(value_ty).to_string(), "string");
}
