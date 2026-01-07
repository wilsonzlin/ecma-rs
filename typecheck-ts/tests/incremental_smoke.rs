use std::sync::Arc;

use typecheck_ts::lib_support::CompilerOptions;
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

#[test]
fn incremental_parsing_reuses_unchanged_files() {
  // Disable bundled libs so the parse counter only reflects the source files.
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  reset_parse_call_count();
  let mut host = MemoryHost::with_options(options);
  let file0 = FileKey::new("file0.ts");
  let file1 = FileKey::new("file1.ts");
  host.insert(file0.clone(), "export const a = 1;");
  host.insert(file1.clone(), "export const b = 2;");

  let mut program = Program::new(host, vec![file0.clone(), file1.clone()]);
  let _ = program.check();
  assert_eq!(
    parse_call_count(),
    2,
    "initial check should parse both files"
  );

  reset_parse_call_count();
  let file0_id = program.file_id(&file0).expect("file0 id");
  program.set_file_text(file0_id, Arc::from("export const a: string = 1;"));
  let _ = program.check();
  assert_eq!(
    parse_call_count(),
    1,
    "incremental check should only parse the changed file"
  );
}
