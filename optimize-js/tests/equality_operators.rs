#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::decompile::{lower_program, LoweredInst};
use optimize_js::il::inst::BinOp;
use optimize_js::TopLevelMode;

#[test]
fn loose_nullish_equality_and_inequality_are_lowered() {
  let src = "let x = unknownVar; console.log(x == null, x != null);";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  let mut saw_loose_eq = false;
  let mut saw_not_loose_eq = false;
  for block in lowered.top_level.bblocks {
    for inst in block.insts {
      if let LoweredInst::Bin { op, .. } = inst {
        saw_loose_eq |= op == BinOp::LooseEq;
        saw_not_loose_eq |= op == BinOp::NotLooseEq;
      }
    }
  }

  assert!(saw_loose_eq, "expected BinOp::LooseEq for `x == null`");
  assert!(
    saw_not_loose_eq,
    "expected BinOp::NotLooseEq for `x != null`"
  );
}

#[test]
fn strict_inequality_is_lowered() {
  let src = "let x = unknownVar; console.log(x !== null);";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  let mut saw_not_strict_eq = false;
  for block in lowered.top_level.bblocks {
    for inst in block.insts {
      if let LoweredInst::Bin { op, .. } = inst {
        saw_not_strict_eq |= op == BinOp::NotStrictEq;
      }
    }
  }

  assert!(
    saw_not_strict_eq,
    "expected BinOp::NotStrictEq for `x !== null`"
  );
}

#[test]
fn loose_nullish_equality_with_void_is_lowered() {
  let src = "let x = unknownVar; console.log(x == void 0, x != void 0);";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  let mut saw_loose_eq = false;
  let mut saw_not_loose_eq = false;
  for block in lowered.top_level.bblocks {
    for inst in block.insts {
      if let LoweredInst::Bin { op, .. } = inst {
        saw_loose_eq |= op == BinOp::LooseEq;
        saw_not_loose_eq |= op == BinOp::NotLooseEq;
      }
    }
  }

  assert!(saw_loose_eq, "expected BinOp::LooseEq for `x == void 0`");
  assert!(
    saw_not_loose_eq,
    "expected BinOp::NotLooseEq for `x != void 0`"
  );
}
