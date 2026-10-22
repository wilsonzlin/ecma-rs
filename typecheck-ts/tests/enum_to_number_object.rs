use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn numeric_enum_assignable_to_number_interface() {
  let src = r#"
enum E { A }
var p: Number = E.A;
var ok: number = E.A;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "numeric enum should assign to Number and number, got {diags:?}"
  );
}

#[test]
fn number_assignable_to_number_interface() {
  let src = r#"
var p: Number = 1;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "number should assign to Number, got {diags:?}"
  );
}
