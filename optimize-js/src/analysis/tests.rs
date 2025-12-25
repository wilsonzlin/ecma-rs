use super::dfa::{AnalysisBoundary, AnalysisResult, DataFlowAnalysis, ResolvedAnalysisBoundary};
use crate::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use crate::il::inst::Inst;
use ahash::HashMap;
use std::collections::BTreeSet;

#[derive(Default)]
struct CollectLabels;

impl<const FORWARDS: bool> DataFlowAnalysis<BTreeSet<u32>, FORWARDS> for CollectLabels {
  fn transfer(&mut self, label: u32, _block: &[Inst], in_: &BTreeSet<u32>) -> BTreeSet<u32> {
    let mut next = in_.clone();
    next.insert(label);
    next
  }

  fn join(&mut self, pred_outs: &[(u32, &BTreeSet<u32>)]) -> BTreeSet<u32> {
    let mut next = BTreeSet::new();
    for (_, set) in pred_outs {
      next.extend(set.iter().copied());
    }
    next
  }
}

fn cfg(labels: &[u32], edges: &[(u32, u32)]) -> Cfg {
  let mut graph = CfgGraph::default();
  for &(from, to) in edges {
    graph.connect(from, to);
  }
  let mut bblocks = CfgBBlocks::default();
  for &label in labels {
    bblocks.add(label, Vec::new());
  }
  Cfg { graph, bblocks }
}

fn run<const FORWARDS: bool>(
  cfg: &Cfg,
  boundary: AnalysisBoundary,
) -> AnalysisResult<BTreeSet<u32>> {
  let mut analysis = CollectLabels::default();
  <CollectLabels as DataFlowAnalysis<BTreeSet<u32>, FORWARDS>>::analyze(
    &mut analysis,
    cfg,
    boundary,
  )
}

fn assert_state(states: &HashMap<u32, BTreeSet<u32>>, label: u32, expected: &[u32]) {
  let expected_set = expected.iter().copied().collect::<BTreeSet<_>>();
  assert_eq!(
    states.get(&label),
    Some(&expected_set),
    "unexpected state for block {}",
    label
  );
}

#[test]
fn diamond_two_exits() {
  let cfg = cfg(&[0, 1, 2, 3, 4], &[(0, 1), (0, 2), (1, 3), (2, 4)]);

  let forward_result = run::<true>(&cfg, AnalysisBoundary::Entry(0));
  assert_state(&forward_result.states, 0, &[0]);
  assert_state(&forward_result.states, 1, &[0, 1]);
  assert_state(&forward_result.states, 2, &[0, 2]);
  assert_state(&forward_result.states, 3, &[0, 1, 3]);
  assert_state(&forward_result.states, 4, &[0, 2, 4]);

  let backward_result = run::<false>(&cfg, AnalysisBoundary::VirtualExit);
  let exit_label = match &backward_result.boundary {
    ResolvedAnalysisBoundary::VirtualExit {
      label,
      predecessors,
    } => {
      assert_eq!(predecessors, &vec![3, 4]);
      *label
    }
    ResolvedAnalysisBoundary::Entry(label) => panic!("expected virtual exit, got entry {label}"),
  };
  assert_state(&backward_result.states, exit_label, &[exit_label]);
  assert_state(&backward_result.states, 3, &[exit_label, 3]);
  assert_state(&backward_result.states, 4, &[exit_label, 4]);
  assert_state(&backward_result.states, 1, &[exit_label, 1, 3]);
  assert_state(&backward_result.states, 2, &[exit_label, 2, 4]);
  assert_state(&backward_result.states, 0, &[exit_label, 0, 1, 2, 3, 4]);
}

#[test]
fn diamond_single_exit() {
  let cfg = cfg(&[0, 1, 2, 3], &[(0, 1), (0, 2), (1, 3), (2, 3)]);

  let forward_result = run::<true>(&cfg, AnalysisBoundary::Entry(0));
  assert_state(&forward_result.states, 0, &[0]);
  assert_state(&forward_result.states, 1, &[0, 1]);
  assert_state(&forward_result.states, 2, &[0, 2]);
  assert_state(&forward_result.states, 3, &[0, 1, 2, 3]);

  let backward_result = run::<false>(&cfg, AnalysisBoundary::VirtualExit);
  let exit_label = match &backward_result.boundary {
    ResolvedAnalysisBoundary::VirtualExit {
      label,
      predecessors,
    } => {
      assert_eq!(predecessors, &vec![3]);
      *label
    }
    ResolvedAnalysisBoundary::Entry(label) => panic!("expected virtual exit, got entry {label}"),
  };
  assert_state(&backward_result.states, exit_label, &[exit_label]);
  assert_state(&backward_result.states, 3, &[exit_label, 3]);
  assert_state(&backward_result.states, 1, &[exit_label, 1, 3]);
  assert_state(&backward_result.states, 2, &[exit_label, 2, 3]);
  assert_state(&backward_result.states, 0, &[exit_label, 0, 1, 2, 3]);
}

#[test]
fn infinite_loop_virtual_exit_from_sink_scc() {
  let cfg = cfg(&[0, 1, 2], &[(0, 1), (1, 2), (2, 1)]);

  let forward_result = run::<true>(&cfg, AnalysisBoundary::Entry(0));
  assert_state(&forward_result.states, 0, &[0]);
  assert_state(&forward_result.states, 1, &[0, 1, 2]);
  assert_state(&forward_result.states, 2, &[0, 1, 2]);

  let backward_result = run::<false>(&cfg, AnalysisBoundary::VirtualExit);
  let exit_label = match &backward_result.boundary {
    ResolvedAnalysisBoundary::VirtualExit {
      label,
      predecessors,
    } => {
      assert_eq!(predecessors, &vec![1, 2]);
      *label
    }
    ResolvedAnalysisBoundary::Entry(label) => panic!("expected virtual exit, got entry {label}"),
  };
  assert_state(&backward_result.states, exit_label, &[exit_label]);
  assert_state(&backward_result.states, 1, &[exit_label, 1, 2]);
  assert_state(&backward_result.states, 2, &[exit_label, 1, 2]);
  assert_state(&backward_result.states, 0, &[exit_label, 0, 1, 2]);
}
