#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::decompile::{lower_program, LoweredArg, LoweredInst};
use optimize_js::il::inst::{BinOp, Const};
use optimize_js::TopLevelMode;

fn call_block_label_with_str_arg(
  lowered: &optimize_js::decompile::LoweredProgram,
  value: &str,
) -> Option<u32> {
  for block in lowered.top_level.bblocks.iter() {
    for inst in block.insts.iter() {
      if let LoweredInst::Call { args, .. } = inst {
        if args.iter().any(|arg| match arg {
          LoweredArg::Const(Const::Str(s)) => s == value,
          _ => false,
        }) {
          return Some(block.label);
        }
      }
    }
  }
  None
}

#[test]
fn leq_geq_mod_and_exp_are_lowered() {
  let src = "let x = unknownVar; console.log(x <= 2, x >= 2, x % 2, x ** 3);";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  let mut saw_leq = false;
  let mut saw_geq = false;
  let mut saw_mod = false;
  let mut saw_exp = false;

  for block in lowered.top_level.bblocks.iter() {
    for inst in block.insts.iter() {
      if let LoweredInst::Bin { op, .. } = inst {
        saw_leq |= *op == BinOp::Leq;
        saw_geq |= *op == BinOp::Geq;
        saw_mod |= *op == BinOp::Mod;
        saw_exp |= *op == BinOp::Exp;
      }
    }
  }

  assert!(saw_leq, "expected BinOp::Leq for `x <= 2`");
  assert!(saw_geq, "expected BinOp::Geq for `x >= 2`");
  assert!(saw_mod, "expected BinOp::Mod for `x % 2`");
  assert!(saw_exp, "expected BinOp::Exp for `x ** 3`");
}

#[test]
fn comma_operator_evaluates_both_sides() {
  let src = "console.log(\"left\"), console.log(\"right\");";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  assert!(
    call_block_label_with_str_arg(&lowered, "left").is_some(),
    "expected comma operator to evaluate left-hand side"
  );
  assert!(
    call_block_label_with_str_arg(&lowered, "right").is_some(),
    "expected comma operator to evaluate right-hand side"
  );
}

#[test]
fn nullish_coalescing_short_circuits_rhs() {
  let src = "let x = unknownVar; let y = x ?? console.log(\"rhs\");";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  let rhs_label = call_block_label_with_str_arg(&lowered, "rhs").expect("expected RHS call block");

  let mut saw_branch_to_rhs = false;
  let mut saw_nullish_check = false;

  for block in lowered.top_level.bblocks.iter() {
    for inst in block.insts.iter() {
      match inst {
        LoweredInst::CondGoto {
          t_label, f_label, ..
        } => {
          saw_branch_to_rhs |= *t_label == rhs_label || *f_label == rhs_label;
        }
        LoweredInst::Bin { op, .. } => {
          saw_nullish_check |= *op == BinOp::LooseEq;
        }
        _ => {}
      }
    }
  }

  assert!(
    saw_branch_to_rhs,
    "expected `??` to lower with a conditional branch guarding RHS evaluation"
  );
  assert!(
    saw_nullish_check,
    "expected `??` to perform a nullish check using BinOp::LooseEq"
  );
}

#[test]
fn rem_and_exponent_assignments_are_lowered() {
  let src = "let x = unknownVar; x %= 2; x **= 3; console.log(x);";

  let program = compile_source(src, TopLevelMode::Module, false);
  let lowered = lower_program(&program);

  let mut saw_mod = false;
  let mut saw_exp = false;
  for block in lowered.top_level.bblocks.iter() {
    for inst in block.insts.iter() {
      if let LoweredInst::Bin { op, .. } = inst {
        saw_mod |= *op == BinOp::Mod;
        saw_exp |= *op == BinOp::Exp;
      }
    }
  }

  assert!(saw_mod, "expected BinOp::Mod for `x %= 2`");
  assert!(saw_exp, "expected BinOp::Exp for `x **= 3`");
}
