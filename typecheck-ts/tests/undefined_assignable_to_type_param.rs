use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn undefined_not_assignable_to_type_params() {
  let src = r#"
function foo<T, U, V extends Date>(x: T, y: U, z: V) {
  x = undefined;
  y = undefined;
  z = undefined;
}
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let starts: Vec<usize> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .map(|d| d.primary.range.start as usize)
    .collect();
  for site in ["x = undefined", "y = undefined", "z = undefined"] {
    let at = src.find(site).unwrap();
    assert!(
      starts.iter().any(|&s| s >= at && s < at + site.len()),
      "{site} should error, starts={starts:?}"
    );
  }
}
