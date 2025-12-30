use std::sync::Arc;

use typecheck_ts::{ExprId, FileKey, MemoryHost, Program};

#[test]
fn narrows_initializer_body() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("main.ts");
  // Initializer bodies (including class field initializers when lowered) should
  // benefit from flow-based refinement so member accesses reflect narrowing.
  let src = r#"
const maybe: { value: string } | null = { value: "ok" } as { value: string } | null;
const from_init = maybe ? maybe.value : "fallback";
"#;
  host.insert(key.clone(), Arc::from(src));

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("from_init"))
    .expect("from_init def");
  let body_id = program.body_of_def(def).expect("initializer body");
  let target_start = src.find("maybe.value").expect("member access span") as u32;
  let target_end = target_start + "maybe.value".len() as u32;

  let result = program.check_body(body_id);
  let expr_idx = result
    .expr_spans()
    .iter()
    .position(|span| span.start <= target_start && target_end <= span.end)
    .expect("member expression span");
  let expr = ExprId(expr_idx as u32);
  let ty = result
    .expr_type(expr)
    .expect("type for config.value expression");

  assert_eq!(program.display_type(ty).to_string(), "string");
}
