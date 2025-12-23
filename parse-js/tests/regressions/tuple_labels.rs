use parse_js;

#[test]
fn keyword_tuple_labels_are_accepted() {
  let source = r#"
  type Foo = (...args: [type: "str", cb: (e: string) => void]) => void;
  "#;

  assert!(parse_js::parse(source).is_ok());
}
