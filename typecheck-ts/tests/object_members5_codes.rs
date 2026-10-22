use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn foo_vs_fooo_is_ts2741_both_directions() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class C { foo: string = ""; }
var c: C;
interface I { fooo: string; }
var i: I;
c = i;
i = c;
"#,
  );
  let program = Program::new(host, vec![file]);
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.to_string())
    .collect();
  let ts2741 = codes.iter().filter(|c| *c == "TS2741").count();
  let ts2322 = codes.iter().filter(|c| *c == "TS2322").count();
  assert_eq!(ts2741, 2, "expected 2x TS2741, got codes={codes:?}");
  assert_eq!(ts2322, 0, "expected no TS2322, got codes={codes:?}");
}
