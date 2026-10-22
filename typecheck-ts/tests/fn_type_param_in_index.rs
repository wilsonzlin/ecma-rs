use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  program
    .check()
    .into_iter()
    .map(|d| format!("{}:{}", d.code, d.message))
    .collect()
}

#[test]
fn bare_param_in_function_type_is_not_tc2008() {
  let a = codes("interface I { [x: string]: <T>(x: T) => T; foo: any }");
  let b = codes("interface I { [k: string]: <T>(x: T) => T; foo: any }");
  let c = codes("interface I { [x: string]: (x) => number; foo: any }");
  let d = codes("type F = <T>(x: T) => T");
  let e = codes("interface I { [x: string]: <T>(y: T) => T; foo: any }");
  for (label, diags) in [("a", &a), ("b", &b), ("c", &c), ("d", &d), ("e", &e)] {
    assert!(
      !diags.iter().any(|s| s.starts_with("TC2008")),
      "{label}: unexpected TC2008: {diags:?}"
    );
  }
}
