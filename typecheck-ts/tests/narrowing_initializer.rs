use std::sync::Arc;

use hir_js::lower_from_source;
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
  let lowered = lower_from_source(src).expect("lower");
  host.insert(key.clone(), Arc::from(src));

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let body_id = lowered
    .defs
    .iter()
    .find_map(|def| {
      (lowered.names.resolve(def.name) == Some("from_init"))
        .then_some(def.body)
        .flatten()
    })
    .expect("initializer body");
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
