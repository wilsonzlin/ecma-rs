use optimize_js::il::inst::Inst;
use optimize_js::ProgramFunction;
use optimize_js::TopLevelMode;
use optimize_js::{compile_source, OptimizationStats};

fn flatten_insts(func: &ProgramFunction) -> Vec<Inst> {
  let mut blocks: Vec<_> = func.body.bblocks.all().collect();
  blocks.sort_by_key(|(label, _)| *label);
  let mut insts = Vec::new();
  for (_, block) in blocks.into_iter() {
    insts.extend(block.iter().cloned());
  }
  insts
}

fn stats_summary(func: &ProgramFunction) -> (OptimizationStats, Vec<Inst>) {
  (func.stats, flatten_insts(func))
}

#[test]
fn dom_cached_when_cfg_is_stable() {
  let source = r#"
    let x = 1 + 2;
    let y = x + 0;
    x + y;
  "#;

  let program = compile_source(source, TopLevelMode::Module, false).expect("compile");
  let (stats, insts) = stats_summary(&program.top_level);

  assert!(
    stats.fixpoint_iterations >= 2,
    "expected at least two iterations to exercise the cache"
  );
  assert_eq!(
    stats.dom_calculations, 1,
    "dominators should not be recomputed when the CFG is unchanged"
  );

  let second_program = compile_source(source, TopLevelMode::Module, false).expect("compile");
  let (second_stats, second_insts) = stats_summary(&second_program.top_level);
  assert_eq!(
    insts, second_insts,
    "optimizations should stay deterministic"
  );
  assert_eq!(
    stats.dom_calculations, second_stats.dom_calculations,
    "dominator counts should be deterministic"
  );
}

#[test]
fn dom_recomputed_when_cfg_changes() {
  let source = r#"
    if (false) {
      let unreachable = 1;
    } else {
      let taken = 2;
      taken;
    }
  "#;

  let program = compile_source(source, TopLevelMode::Module, false).expect("compile");
  let stats = program.top_level.stats;
  assert!(
    stats.dom_calculations >= 2,
    "CFG mutations should force dominator recomputation"
  );
  assert!(
    stats.fixpoint_iterations >= 2,
    "cfg-shape changes should still converge through the fixpoint loop"
  );
}
