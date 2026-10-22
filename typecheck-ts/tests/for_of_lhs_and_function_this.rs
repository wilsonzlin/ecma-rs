//! For-in/of LHS assignment to an existing binding checks the element type
//! against the variable's *declared* type and narrows only the flow type —
//! the loop does not rebind `declared_ty`, so later writes still check
//! against the annotation (`controlFlowForOfStatement.ts`).
//! And `this` in a function expression/declaration without a contextual
//! `this` type is `any` (`typeOfThisInFunctionExpression.ts`).

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
fn for_of_assign_lhs_keeps_declared_write_target() {
  let src = "let obj: number[];\nlet x: string | number | boolean | RegExp;\nfunction a() {\n    x = true;\n    for (x of obj) {\n        x = x.toExponential();\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn for_of_assign_lhs_wrong_element_still_errors() {
  let src = "let obj: string[];\nlet x: number;\nfor (x of obj) {\n}\n";
  // TS2322 for the element/target mismatch; TS2454 for the unassigned `obj`.
  assert_eq!(codes(src), ["TS2322", "TS2454"]);
}

#[test]
fn this_in_function_expression_is_any() {
  let src = "var t = function () {\n    var p = this;\n    var p: any;\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn this_in_function_declaration_is_any() {
  let src = "function fn() {\n    var p = this;\n    var p: any;\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn destructuring_assignment_preserves_declared_type() {
  // `({y: x = /a/} = {y: 1})` narrows x in flow but must not replace the
  // declared union as the write target for a later `for (x of a)`
  // (`assignmentTypeNarrowing.ts`).
  let src = "let x: string | number | boolean | RegExp;\n({y: x = /a/} = {y: 1});\nlet a: string[];\nfor (x of a) {\n    x;\n}\n";
  assert_eq!(codes(src), ["TS2454"]);
}

#[test]
fn destructuring_assignment_wrong_type_still_errors() {
  let src = "let x: number;\n({y: x} = {y: 's'});\n";
  assert_eq!(codes(src), ["TS2322"]);
}

#[test]
fn rest_element_tuple_stays_positional_in_assignment() {
  // Rest of a destructuring-assignment tuple stays a tuple, so the inner
  // pattern destructures positionally (`restElementWithAssignmentPattern1.ts`).
  let src = "var a: string, b: number;\n[...[a, b = 0]] = [\"\", 1];\n";
  assert!(codes(src).is_empty());
}

#[test]
fn rest_element_declaration_form_union() {
  // Declaration form: the rest array is `Array<string | number>`, so later
  // narrowed uses error (matches tsc).
  let src = "var [...[a, b = 0]] = [\"\", 1];\nvar s: string = a;\nvar n: number = b;\n";
  assert_eq!(codes(src), ["TS2322", "TS2322"]);
}

#[test]
fn iterable_destructuring_assignment_rest() {
  // `[a, ...b] = new FooIterator` binds `a: Foo` and `b: Foo[]` via the
  // iterable protocol — assignable to `Bar` / `Bar[]` (`iterableArrayPattern4.ts`).
  let src = "class Bar { x: number }\nclass Foo extends Bar { y: number }\nclass FooIterator {\n    next() {\n        return {\n            value: new Foo,\n            done: false\n        };\n    }\n\n    [Symbol.iterator]() {\n        return this;\n    }\n}\nvar a: Bar, b: Bar[];\n[a, ...b] = new FooIterator\n";
  assert!(codes(src).is_empty());
}
