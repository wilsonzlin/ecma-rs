use parse_js;

#[test]
fn decorator_on_overload_signature_allows_body_on_next_member() {
  let source = r#"
  class C {
    @dec
    method()
    method() {}
  }
  "#;

  assert!(parse_js::parse(source).is_ok());
}
