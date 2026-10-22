//! `typeof` on numeric enum unions must keep the enum ref (tsc
//! `TypeGuardWithEnumUnion.ts`).

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn typeof_number_narrows_numeric_enum_union_without_ts2403() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
enum Color { R, G, B }
function f1(x: Color | string) {
  if (typeof x === "number") {
    var y = x;
    var y: Color;
  } else {
    var z = x;
    var z: string;
  }
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.to_string())
    .collect();
  assert!(
    !codes.iter().any(|c| c == "TS2403"),
    "expected no TS2403 after enum typeof narrow, got {codes:?}"
  );
}
