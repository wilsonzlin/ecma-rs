use hir_js::{lower_top_level, LowerError};
use parse_js::parse;

#[test]
fn lowering_requires_scope_annotations() {
  let parsed = parse("foo;").expect("source should parse");

  let err = lower_top_level(&parsed).expect_err("lowering should fail without scopes");

  match err {
    LowerError::MissingScope { context, .. } => {
      assert_eq!(context, "identifier expr");
    }
    other => panic!("expected MissingScope error, got {other:?}"),
  }
}
