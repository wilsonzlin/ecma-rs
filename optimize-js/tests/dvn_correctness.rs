#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::il::inst::{Arg, InstTyp};
use optimize_js::util::debug::OptimizerDebugStep;
use optimize_js::{ProgramFunction, TopLevelMode};

fn find_step<'a>(func: &'a ProgramFunction, name: &str) -> &'a OptimizerDebugStep {
  func
    .debug
    .as_ref()
    .expect("debug output should be enabled")
    .steps()
    .iter()
    .find(|step| step.name == name)
    .unwrap_or_else(|| panic!("missing debug step {name}"))
}

fn collect_phi_entries(step: &OptimizerDebugStep) -> Vec<(Vec<u32>, Vec<Arg>)> {
  step
    .bblocks
    .values()
    .flat_map(|block| {
      block
        .iter()
        .filter(|inst| inst.t == InstTyp::Phi)
        .map(|inst| (inst.labels.clone(), inst.args.clone()))
    })
    .collect()
}

#[test]
fn dvn_canonicalizes_phi_inputs_per_predecessor() {
  let program = compile_source(
    r#"
      let result;
      if (Math.random()) {
        const base = 40 + 2;
        result = base;
      } else {
        result = 21 * 2;
      }
      result;
    "#,
    TopLevelMode::Module,
    true,
  );

  let step = find_step(&program.top_level, "opt1_dvn");
  let phi_entries = collect_phi_entries(step);
  assert!(
    !phi_entries.is_empty(),
    "expected at least one phi in the debug output"
  );
  assert!(
    phi_entries
      .iter()
      .any(|(_, args)| args.iter().all(|arg| matches!(arg, Arg::Const(_)))),
    "phi arguments should be canonicalized to constants when predecessors compute constants: {phi_entries:?}"
  );
}

#[test]
fn dvn_sorts_phi_entries_by_predecessor() {
  let program = compile_source(
    r#"
      let value;
      if (cond()) {
        value = 1;
      } else if (other()) {
        value = 2;
      } else {
        value = 3;
      }
      value;
    "#,
    TopLevelMode::Module,
    true,
  );

  let step = find_step(&program.top_level, "opt1_dvn");
  let phi_entries = collect_phi_entries(step);
  assert!(
    !phi_entries.is_empty(),
    "expected at least one phi in the debug output"
  );
  for (labels, _) in phi_entries {
    assert!(
      labels.windows(2).all(|w| w[0] < w[1]),
      "phi predecessor labels should stay sorted for determinism: {labels:?}"
    );
  }
}

#[test]
fn consteval_call_without_target_is_preserved() {
  let program = compile_source(
    r#"
      let x = 0;
      external(x);
      x;
    "#,
    TopLevelMode::Module,
    true,
  );

  let mut saw_call = false;
  for (_label, block) in program.top_level.body.bblocks.all() {
    for inst in block {
      if inst.t == InstTyp::Call && inst.tgts.is_empty() {
        saw_call = true;
      }
    }
  }
  assert!(
    saw_call,
    "const-evaluable call without a target should not be deleted"
  );
}
