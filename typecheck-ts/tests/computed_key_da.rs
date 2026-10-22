//! TS2454 (definite assignment) does not apply to computed keys of *method*
//! members — tsc skips DA analysis for method/accessor name expressions
//! (`{ [s]() {} }`, `class C { [s]() {} }`, accessors) — but still checks
//! plain-property keys (`{ [s]: 1 }`). Conformance
//! `es6/computedProperties/computedPropertyNames10_ES6.ts`.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn unassigned_var_in_method_keys_is_not_ts2454() {
  // The conformance case shape.
  let src = r#"
var s: string;
var n: number;
var a: any;
var v = {
    [s]() { },
    [n]() { },
    [s + s]() { },
    [s + n]() { },
    [+s]() { },
    [""]() { },
    [0]() { },
    [a]() { },
    [<any>true]() { },
    [`hello bye`]() { },
    [`hello ${a} bye`]() { }
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn unassigned_var_in_plain_property_key_is_ts2454() {
  let src = "var s: string;\nvar p = { [s]: 1 };\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2454"),
    "plain-property computed key must still be DA-checked: {c:?}"
  );
}

#[test]
fn unassigned_var_in_accessor_and_class_member_keys_is_not_ts2454() {
  let src = r#"
var s: string;
var o = { get [s]() { return 1 } };
class C {
  [s]() {}
  [s] = 1
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}
