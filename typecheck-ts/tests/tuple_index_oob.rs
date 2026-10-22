//! TS2493: fixed-length tuple element access out of range.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(src: &str) -> Vec<(String, String)> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let mut out: Vec<_> = Program::new(host, vec![file])
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2493")
    .map(|d| (d.code.as_str().to_string(), d.message.clone()))
    .collect();
  out.sort();
  out
}

#[test]
fn fixed_tuple_oob_reports_ts2493() {
  // Upstream: bestCommonTypeOfTuple.ts
  let src = r#"
var t1: [(x: number) => string, (x: number) => number];
var t2: [number, any];
var t4: [number, number, number];
var e1 = t1[2];
var e2 = t2[2];
var e4 = t4[3];
"#;
  let codes: Vec<_> = diags(src).into_iter().map(|(c, _)| c).collect();
  assert_eq!(codes, vec!["TS2493".to_string(); 3], "{:?}", diags(src));
}

#[test]
fn in_range_tuple_index_ok() {
  let src = r#"
var t: [number, string];
var a = t[0];
var b = t[1];
"#;
  assert!(diags(src).is_empty(), "{:?}", diags(src));
}

#[test]
fn rest_tuple_allows_higher_index() {
  let src = r#"
var t: [string, ...number[]];
var a = t[5];
"#;
  assert!(
    diags(src).is_empty(),
    "rest tuples are open-ended: {:?}",
    diags(src)
  );
}
