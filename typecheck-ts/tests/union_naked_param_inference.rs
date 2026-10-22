//! Union-target inference with a naked type parameter (`T | string`).
//! Oracle: tsc 5.9.3 / `unionAndIntersectionInference2.ts`.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn check_codes(src: &str) -> Vec<String> {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut codes: Vec<String> = program
    .check()
    .into_iter()
    .map(|d| d.code.to_string())
    .collect();
  codes.sort();
  codes
}

#[test]
fn infer_strips_matching_union_constituents_into_naked_param() {
  // `f1(e1)` must not emit TS2345: T is inferred as `number | boolean`, so
  // the parameter becomes `number | boolean | string`.
  let codes = check_codes(
    r#"
declare function f1<T>(x: T | string): T;
declare const a1: string;
declare const b1: string | string[];
declare const e1: number | string | boolean;
const r1 = f1(a1);
const r2 = f1(b1);
const r3 = f1(e1);
"#,
  );
  assert!(
    !codes.iter().any(|c| c == "TS2345"),
    "expected no TS2345 on f1(e1), got {codes:?}"
  );
}

#[test]
fn infer_naked_param_return_types_match_tsc() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
declare function f1<T>(x: T | string): T;
declare const a1: string;
declare const b1: string | string[];
declare const e1: number | string | boolean;
export const r1 = f1(a1);
export const r2 = f1(b1);
export const r3 = f1(e1);
"#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();
  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);

  let ty = |name: &str| {
    exports
      .get(name)
      .and_then(|e| e.type_id)
      .unwrap_or_else(|| panic!("missing export {name}"))
  };
  assert_eq!(program.display_type(ty("r1")).to_string(), "string");
  assert_eq!(program.display_type(ty("r2")).to_string(), "string[]");
  let r3 = program.display_type(ty("r3")).to_string();
  assert!(
    r3 == "number | boolean" || r3 == "boolean | number",
    "expected number | boolean, got {r3}"
  );
}
