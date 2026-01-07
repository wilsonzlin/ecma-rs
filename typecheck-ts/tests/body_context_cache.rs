use typecheck_ts::{FileKey, MemoryHost, Program, QueryKind};

#[test]
fn body_context_is_cached_across_multiple_body_checks() {
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(
    key.clone(),
    r#"
export function a() { return 1; }
export function b(): number { return 2; }
"#,
  );
  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let mut a_body = None;
  let mut b_body = None;
  for def in program.definitions_in_file(file_id) {
    let Some(name) = program.def_name(def) else {
      continue;
    };
    match name.as_str() {
      "a" => a_body = program.body_of_def(def),
      "b" => b_body = program.body_of_def(def),
      _ => {}
    }
  }
  let a_body = a_body.expect("a body");
  let b_body = b_body.expect("b body");

  let _ = program.check_body(a_body);
  let _ = program.check_body(b_body);

  let stats = program.query_stats();
  let builds = stats
    .queries
    .get(&QueryKind::BuildBodyContext)
    .map(|stat| stat.total)
    .unwrap_or(0);
  assert_eq!(builds, 1);
}
