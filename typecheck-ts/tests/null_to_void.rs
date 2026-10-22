use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn null_not_assignable_to_void() {
  let src = "var g: void = null;\n";
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.as_str()).collect();
  assert!(
    codes.iter().any(|c| *c == "TS2322"),
    "expected TS2322 for null→void, got {diags:?}"
  );
}

#[test]
fn undefined_assignable_to_void() {
  let src = "var g: void = undefined;\n";
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "undefined→void should be ok, got {ts2322:?}"
  );
}
