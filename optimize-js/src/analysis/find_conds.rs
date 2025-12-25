use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::dom::PostDom;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use itertools::Itertools;

/// Finds conditional expressions/statements in the CFG.
/// Returns a map from the condition node to the set of nodes that it controls.
pub fn find_conds(cfg: &Cfg, dom: &Dom, postdom: &PostDom) -> HashMap<u32, HashSet<u32>> {
  let _ = dom;

  let mut conds = HashMap::<u32, HashSet<u32>>::new();
  let mut labels = cfg.graph.labels().collect_vec();
  labels.sort_unstable();
  for c in labels {
    let mut succs = cfg.graph.children(c).collect_vec();
    succs.sort_unstable();
    if succs.len() < 2 {
      continue;
    };
    let Some(join) = postdom.idom_of(c) else {
      continue;
    };
    for s in succs {
      let mut runner = s;
      while runner != join {
        conds.entry(c).or_default().insert(runner);
        let Some(next) = postdom.idom_of(runner) else {
          break;
        };
        // If the postdominator tree is malformed and the next node is the same as the current,
        // avoid an infinite loop.
        if next == runner {
          break;
        };
        runner = next;
      }
    }
  }
  conds
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::cfg::cfg::CfgGraph;
  use ahash::HashSet;
  use std::iter::FromIterator;

  fn cfg_from_edges(edges: &[(u32, u32)]) -> Cfg {
    let mut graph = CfgGraph::default();
    for &(from, to) in edges {
      graph.connect(from, to);
    }
    Cfg {
      graph,
      bblocks: Default::default(),
    }
  }

  #[test]
  fn diamond_if_else_controls_branch_bodies() {
    let cfg = cfg_from_edges(&[
      (0, 1),          // entry to condition
      (1, 2),          // true branch
      (1, 3),          // false branch
      (2, 4),          // join
      (3, 4),          // join
      (4, u32::MAX),   // exit
    ]);
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    let controlled = conds.get(&1).cloned().unwrap_or_default();
    assert_eq!(controlled, HashSet::from_iter([2_u32, 3_u32]));
    assert!(!controlled.contains(&4));
  }

  #[test]
  fn nested_ifs_assign_control_to_inner_and_outer_conditions() {
    let cfg = cfg_from_edges(&[
      (0, 1),          // entry to outer condition
      (1, 2),          // outer then: leads to inner condition
      (1, 5),          // outer else
      (2, 3),          // inner then
      (2, 4),          // inner else
      (3, 6),          // join after inner then
      (4, 6),          // join after inner else
      (5, 6),          // join outer else
      (6, u32::MAX),   // exit
    ]);
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_eq!(
      conds.get(&1).cloned().unwrap_or_default(),
      HashSet::from_iter([2_u32, 5_u32])
    );
    assert_eq!(
      conds.get(&2).cloned().unwrap_or_default(),
      HashSet::from_iter([3_u32, 4_u32])
    );
  }

  #[test]
  fn condition_with_exit_join_uses_synthetic_exit() {
    let cfg = cfg_from_edges(&[
      (0, 1),          // entry to condition
      (1, 2),          // fallthrough branch
      (1, u32::MAX),   // exit branch
      (2, u32::MAX),   // exit
    ]);
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_eq!(
      conds.get(&1).cloned().unwrap_or_default(),
      HashSet::from_iter([2_u32])
    );
  }

  #[test]
  fn loop_header_controls_loop_body_region() {
    let cfg = cfg_from_edges(&[
      (0, 1),          // entry to loop header
      (1, 2),          // loop body
      (1, 3),          // exit from loop
      (2, 1),          // back edge
      (3, u32::MAX),   // exit
    ]);
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_eq!(
      conds.get(&1).cloned().unwrap_or_default(),
      HashSet::from_iter([1_u32, 2_u32])
    );
  }
}
