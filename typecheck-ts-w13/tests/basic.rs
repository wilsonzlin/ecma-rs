use once_cell::sync::Lazy;
use typecheck_ts::check::check_body;
use typecheck_ts::TypeDatabase;

#[test]
fn basic_inference_and_diagnostics() {
  static SOURCE: Lazy<String> = Lazy::new(|| {
    [
      "let a = 1;",
      "let b: string = \"ok\";",
      "function add(x: number, y: number) { return x + y; }",
      "let c = add(a, b);",
    ]
    .join("\n")
  });

  let mut db = TypeDatabase::new();
  let body_id = db.add_body_from_source(&SOURCE).expect("parse failed");
  let result = check_body(&mut db, body_id);

  assert!(!result.expr_types.is_empty());
  assert_eq!(result.diagnostics.len(), 1, "expected a call diagnostic");
  assert_eq!(result.diagnostics[0].code, "TYPE_MISMATCH");
}
