use typecheck_ts::codes;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn merges_flow_and_main_diagnostics() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("flow.ts");
  host.insert(
    file.clone(),
    r#"
      export function f(): number {
        const value: number = "oops";
        let x: number;
        return x;
      }
    "#,
  );

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let body_id = program
    .exports_of(file_id)
    .get("f")
    .and_then(|entry| entry.def)
    .and_then(|def| program.body_of_def(def))
    .expect("function body");
  let result = program.check_body(body_id);

  let mut codes_seen: Vec<_> = result
    .diagnostics()
    .iter()
    .map(|d| d.code.as_str())
    .collect();
  codes_seen.sort();

  assert!(
    codes_seen.contains(&codes::TYPE_MISMATCH.as_str()),
    "main checker diagnostics should be retained: {codes_seen:?}"
  );
  assert!(
    codes_seen.contains(&codes::USE_BEFORE_ASSIGNMENT.as_str()),
    "flow diagnostics should be merged even when main diagnostics exist: {codes_seen:?}"
  );
}
