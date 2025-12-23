use parse_js;

#[test]
fn allows_classes_extending_primitive_expressions() {
  let cases = [
    "class C extends number { }",
    "class C2 extends string { }",
    "class C3 extends boolean { }",
    "class C4 extends Void  { }",
    "class C4a extends void {}",
    "class C5 extends Null { }",
    "class C5a extends null { }",
    "class C6 extends undefined { }",
    "class C7 extends Undefined { }",
    "enum E { A }\nclass C8 extends E { }",
    "const C9 = class extends number { }",
    "const C10 = class extends string { }",
    "const C11 = class extends boolean { }",
    "const C12 = class A extends number { }",
    "const C13 = class B extends string { }",
    "const C14 = class C extends boolean { }",
  ];

  for case in cases {
    let parsed = parse_js::parse(case);
    assert!(parsed.is_ok(), "failed to parse {case:?}: {parsed:?}");
  }
}
