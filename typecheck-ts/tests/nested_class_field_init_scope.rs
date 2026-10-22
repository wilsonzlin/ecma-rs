//! The TopLevel subsequent-property pass (`check_class_subsequent_property_types`)
//! re-checks field initializers only for their *type*; diagnostics from that
//! re-check must be drained because the pass runs with the current body's
//! scope, which cannot see enclosing-function bindings of lexically nested
//! classes (`localTypes2.ts`). Genuine initializer errors are reported by the
//! field-initializer body check with the correct lexical scope.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
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
fn nested_class_field_init_captures_enclosing_params() {
  // Exact shape of the shard-29 conformance case (f2/f3 in localTypes2.ts).
  let src = r#"function f2() {
    function f(x: number) {
        class C {
            public x = x;
            constructor(public y: number) { }
        }
        return C;
    }
    let C = f(10);
    let v = new C(20);
    let x = v.x;
    let y = v.y;
}

function f3() {
    function f(x: number, y: number) {
        class C {
            public x = x;
            public y = y;
        }
        return C;
    }
    let C = f(10, 20);
    let v = new C();
    let x = v.x;
    let y = v.y;
}
"#;
  assert!(codes(src).is_empty());
}

#[test]
fn nested_class_expr_field_init_captures_enclosing_params() {
  let src = "function f2() {\n  function f(x: number) {\n    return class { x = x; };\n  }\n  let C = f(10);\n  let v = new C();\n  let x = v.x;\n}";
  assert!(codes(src).is_empty());
}

#[test]
fn genuinely_missing_name_in_field_init_still_errors() {
  // The field-initializer body check reports with the correct scope: a name
  // resolvable nowhere must still be TS2304 (exactly once).
  let src = "function f(x: number) {\n  class C { y = missing; }\n  return C;\n}";
  assert_eq!(codes(src), ["TS2304"]);
}

#[test]
fn toplevel_class_field_init_error_reported_once() {
  assert_eq!(codes("class C { x = missing; }"), ["TS2304"]);
}
