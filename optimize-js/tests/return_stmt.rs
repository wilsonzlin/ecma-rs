#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::TopLevelMode;

#[test]
fn return_statements_in_functions_are_supported() {
  // Arrow function expression bodies lower to an implicit `return` in HIR.
  let src = r#"
    const make = () => 1;
    make();
  "#;
  let program = compile_source(src, TopLevelMode::Module, false);
  assert_eq!(
    program.functions.len(),
    1,
    "expected arrow function body to be compiled"
  );
}
