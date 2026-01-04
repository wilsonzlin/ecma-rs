use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn callback_inference_works_through_spread_array_literal() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
function mapRest<T, U>(items: T[], fn: (value: T) => U, ...rest: any[]): U[] {
  return [] as any;
}

const numbers = [1, 2, 3];
const rest: any[] = [];
export const incremented = mapRest(numbers, ...[(n) => n + 1], ...rest);
"#,
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let entry = exports.get("incremented").expect("export incremented");
  let ty = entry.type_id.expect("type for incremented");
  assert_eq!(program.display_type(ty).to_string(), "number[]");
}
