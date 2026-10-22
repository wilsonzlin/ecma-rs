use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn namespace_class_shadows_outer() {
  let src = r#"
class A { outer: 1 }
namespace N {
  class A { inner: 1 }
  export function f() {
    declare var x: A;
    declare var wantInner: { inner: 1 };
    declare var wantOuter: { outer: 1 };
    wantInner = x; // should be ok
    wantOuter = x; // should error
  }
}
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322" || d.code.as_str() == "TS2741")
    .map(|d| {
      let at = d.primary.range.start as usize;
      let snippet = src.get(at..at.saturating_add(20)).unwrap_or("");
      (
        d.code.as_str(),
        at,
        snippet.lines().next().unwrap_or("").to_string(),
      )
    })
    .collect();
  eprintln!("diags={codes:?}");
  let want_inner_ok = !codes.iter().any(|(_, _, s)| s.contains("wantInner"));
  let want_outer_err = codes.iter().any(|(_, _, s)| s.contains("wantOuter"));
  assert!(
    want_inner_ok,
    "wantInner = x should be ok (inner A), got {codes:?}"
  );
  assert!(
    want_outer_err,
    "wantOuter = x should error (not outer A), got {codes:?}"
  );
}
