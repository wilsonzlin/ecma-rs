#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::TopLevelMode;

#[test]
fn compiles_not_plus_and_void() {
  // Regression test: these unary operators should be supported by the HIR->IL lowering.
  let src = "console.log(!true, +1, void 0);";
  let _program = compile_source(src, TopLevelMode::Module, false);
}
