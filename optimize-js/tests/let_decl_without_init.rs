#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::il::inst::{Arg, Const, InstTyp};
use optimize_js::TopLevelMode;

#[test]
fn let_declarations_without_initializers_assign_undefined() {
  let program = compile_source("let x; console.log(x);", TopLevelMode::Module, true);
  let dbg = program
    .top_level
    .debug
    .as_ref()
    .expect("debug output enabled");
  let source_step = dbg
    .steps()
    .iter()
    .find(|step| step.name == "source")
    .expect("source step present");

  let mut saw_undefined_init = false;
  for block in source_step.bblocks.values() {
    for inst in block {
      if inst.t == InstTyp::VarAssign
        && inst.args.len() == 1
        && matches!(&inst.args[0], Arg::Const(Const::Undefined))
      {
        saw_undefined_init = true;
      }
    }
  }

  assert!(
    saw_undefined_init,
    "expected `let x;` to lower to an explicit undefined assignment"
  );
}
