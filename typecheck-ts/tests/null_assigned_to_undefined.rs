use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn assign_to_undefined_is_ts2539_and_typeof_undefined_null_is_ts2322() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var x = undefined = null;
var y: typeof undefined = null;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.to_string()).collect();
  assert!(
    codes.iter().any(|c| c == "TS2539"),
    "expected TS2539 for undefined=null, got {diags:?}"
  );
  assert!(
    !codes.iter().any(|c| c == "TS2304"),
    "typeof undefined must resolve, got {diags:?}"
  );
  assert_eq!(
    codes.iter().filter(|c| *c == "TS2322").count(),
    1,
    "expected one TS2322 for y=null, got {diags:?}"
  );
}
