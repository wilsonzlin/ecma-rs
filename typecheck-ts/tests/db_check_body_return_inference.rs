use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn db_check_body_infers_unannotated_function_return() {
  let mut host = MemoryHost::default();
  let source = "function f() { return 1; }\nconst x = f();\n";
  let file = FileKey::new("entry.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let body = program.file_body(file_id).expect("file body");

  // `Program::check_body()` goes through the DB-backed `BodyCheckContext` snapshot; this should
  // include inferred return types for unannotated functions so `f()` is not `unknown`.
  let result = program.check_body(body);
  let call_offset = source.rfind("f()").expect("call offset") as u32 + 1;
  let (_expr, ty) = result.expr_at(call_offset).expect("expr at f() call");

  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered == "number" || rendered == "1",
    "expected inferred return type for f() to be number (or literal 1), got {rendered}"
  );
}

