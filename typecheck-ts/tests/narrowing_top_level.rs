use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, PatId, Program};

#[test]
fn narrows_top_level_body() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("main.ts");
  let src = r#"
let x: string | null = "value";
if (x) {
  const y = x;
}
"#;
  host.insert(key.clone(), Arc::from(src));

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let body = program.file_body(file_id).expect("top-level body");
  let result = program.check_body(body);

  let offset = src.find("y = x").expect("span for y") as u32;
  let pat_idx = result
    .pat_spans()
    .iter()
    .position(|span| span.start <= offset && offset < span.end)
    .expect("pattern span for y");
  let y_ty = result.pat_type(PatId(pat_idx as u32)).expect("type for y");
  let display = program.display_type(y_ty).to_string();

  assert!(
    (display == "string" || display.starts_with('\"')) && !display.contains("null"),
    "expected narrowed string for y, got {display}"
  );
}
