#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::TopLevelMode;

#[test]
fn throw_statements_in_functions_are_supported() {
  let src = r#"
    const fail = () => {
      throw err();
    };
    fail();
  "#;
  let program = compile_source(src, TopLevelMode::Module, false);
  assert_eq!(
    program.functions.len(),
    1,
    "expected arrow function body to be compiled"
  );
}
