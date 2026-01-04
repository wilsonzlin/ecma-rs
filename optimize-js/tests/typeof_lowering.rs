#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::decompile::{lower_program, LoweredInst};
use optimize_js::TopLevelMode;

#[test]
fn typeof_unknown_identifier_is_not_lowered_via_unknown_load() {
  // `typeof <unbound-ident>` must not throw. In the optimizer pipeline, that
  // means we should not emit an `UnknownLoad` for the identifier before applying
  // `typeof`.
  let program = compile_source(
    "console.log(typeof unknownVar);",
    TopLevelMode::Module,
    false,
  );
  let lowered = lower_program(&program);

  let mut saw_unknown_load = false;
  for block in lowered.top_level.bblocks {
    for inst in block.insts {
      if let LoweredInst::IdentLoad { name, .. } = inst {
        if name == "unknownVar" {
          saw_unknown_load = true;
        }
      }
    }
  }

  assert!(
    !saw_unknown_load,
    "expected `typeof unknownVar` to avoid lowering `unknownVar` via IdentLoad"
  );
}
