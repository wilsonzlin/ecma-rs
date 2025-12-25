use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::dom::PostDom;
use crate::il::inst::InstTyp;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use ahash::HashSetExt;
use std::collections::HashSet as StdHashSet;
use std::collections::VecDeque;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CondRegion {
  pub then_entry: u32,
  pub else_entry: u32,
  pub join: u32,
  pub then_nodes: HashSet<u32>,
  pub else_nodes: HashSet<u32>,
}

fn nearest_common_postdom(postdom: &PostDom, a: u32, b: u32) -> u32 {
  if a == b {
    return a;
  }
  let mut ancestors = StdHashSet::new();
  let mut current = Some(a);
  while let Some(node) = current {
    ancestors.insert(node);
    let parent = postdom.immediate_dominator(node);
    if parent == Some(node) {
      break;
    }
    current = parent;
  }
  ancestors.insert(postdom.entry());

  let mut current = Some(b);
  while let Some(node) = current {
    if ancestors.contains(&node) {
      return node;
    }
    let parent = postdom.immediate_dominator(node);
    if parent == Some(node) {
      break;
    }
    current = parent;
  }
  postdom.entry()
}

fn collect_branch_region(
  cfg: &Cfg,
  dominates: &crate::dom::DominatesGraph,
  cond: u32,
  join: u32,
  start: u32,
) -> HashSet<u32> {
  let mut region = HashSet::new();
  if start == join {
    return region;
  }
  if !dominates.dominates(cond, start) {
    return region;
  }
  let mut queue = VecDeque::from([start]);
  region.insert(start);
  while let Some(node) = queue.pop_front() {
    let mut children = cfg.graph.children(node).collect::<Vec<_>>();
    children.sort_unstable();
    for child in children {
      if child == join || child == cond {
        continue;
      }
      if !dominates.dominates(cond, child) {
        continue;
      }
      if region.insert(child) {
        queue.push_back(child);
      }
    }
  }
  region
}

/// Finds conditional expressions/statements in the CFG.
/// Returns a map from the condition node to the region it controls.
pub fn find_conds(cfg: &Cfg, dom: &Dom, postdom: &PostDom) -> HashMap<u32, CondRegion> {
  let dominates = dom.dominates_graph();
  let post_dominates = postdom.dominates_graph();
  let mut conds = HashMap::new();
  let mut labels = cfg.graph.labels().collect::<Vec<_>>();
  labels.sort_unstable();
  for label in labels {
    let mut children = cfg.graph.children(label).collect::<Vec<_>>();
    let mut succ = None;
    if let Some(block) = cfg.bblocks.maybe_get(label) {
      if let Some(inst) = block.last() {
        if inst.t == InstTyp::CondGoto {
          succ = Some((inst.labels[0], inst.labels[1]));
        }
      }
    }
    if succ.is_none() && children.len() == 2 {
      children.sort_unstable();
      succ = Some((children[0], children[1]));
    }
    let Some((then_entry, else_entry)) = succ else {
      continue;
    };
    if !dominates.dominates(label, then_entry) && !dominates.dominates(label, else_entry) {
      continue;
    }
    let join = nearest_common_postdom(postdom, then_entry, else_entry);
    if !post_dominates.dominates(join, label) {
      continue;
    }
    let then_nodes = collect_branch_region(cfg, &dominates, label, join, then_entry);
    let else_nodes = collect_branch_region(cfg, &dominates, label, join, else_entry);
    conds.insert(
      label,
      CondRegion {
        then_entry,
        else_entry,
        join,
        then_nodes,
        else_nodes,
      },
    );
  }
  conds
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::cfg::cfg::Cfg;
  use crate::cfg::cfg::CfgBBlocks;
  use crate::cfg::cfg::CfgGraph;
  use crate::dom::Dom;
  use crate::il::inst::Arg;
  use crate::il::inst::Const;
  use crate::il::inst::Inst;

  fn cond_inst(t: u32, f: u32) -> Inst {
    Inst::cond_goto(Arg::Const(Const::Bool(true)), t, f)
  }

  fn assert_region(
    conds: &HashMap<u32, CondRegion>,
    label: u32,
    then_entry: u32,
    else_entry: u32,
    join: u32,
    then_nodes: &[u32],
    else_nodes: &[u32],
  ) {
    let region = conds.get(&label).unwrap();
    assert_eq!(region.then_entry, then_entry);
    assert_eq!(region.else_entry, else_entry);
    assert_eq!(region.join, join);
    let expected_then: HashSet<u32> = then_nodes.iter().copied().collect();
    let expected_else: HashSet<u32> = else_nodes.iter().copied().collect();
    assert_eq!(region.then_nodes, expected_then);
    assert_eq!(region.else_nodes, expected_else);
  }

  fn build_cfg(edges: &[(u32, u32)], blocks: &[(u32, Vec<Inst>)]) -> Cfg {
    let mut graph = CfgGraph::default();
    for (p, c) in edges {
      graph.connect(*p, *c);
    }
    let mut bblocks = CfgBBlocks::default();
    for (label, insts) in blocks {
      bblocks.add(*label, insts.clone());
    }
    Cfg {
      graph,
      bblocks,
    }
  }

  #[test]
  fn detects_if_without_else() {
    let cfg = build_cfg(
      &[(0, 1), (0, 2), (1, 2), (2, u32::MAX)],
      &[(0, vec![cond_inst(1, 2)]), (1, vec![]), (2, vec![])],
    );
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_region(&conds, 0, 1, 2, 2, &[1], &[]);
  }

  #[test]
  fn detects_if_else_diamond() {
    let cfg = build_cfg(
      &[(0, 1), (0, 2), (1, 3), (2, 3), (3, u32::MAX)],
      &[
        (0, vec![cond_inst(1, 2)]),
        (1, vec![]),
        (2, vec![]),
        (3, vec![]),
      ],
    );
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_region(&conds, 0, 1, 2, 3, &[1], &[2]);
  }

  #[test]
  fn detects_short_circuit() {
    let cfg = build_cfg(
      &[(0, 2), (0, 1), (1, 2), (2, u32::MAX)],
      &[(0, vec![cond_inst(2, 1)]), (1, vec![]), (2, vec![])],
    );
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_region(&conds, 0, 2, 1, 2, &[], &[1]);
  }

  #[test]
  fn detects_nested_conditionals() {
    let cfg = build_cfg(
      &[
        (0, 1),
        (0, 4),
        (1, 2),
        (1, 3),
        (2, 5),
        (3, 5),
        (4, 5),
        (5, u32::MAX),
      ],
      &[
        (0, vec![cond_inst(1, 4)]),
        (1, vec![cond_inst(2, 3)]),
        (2, vec![]),
        (3, vec![]),
        (4, vec![]),
        (5, vec![]),
      ],
    );
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_region(&conds, 0, 1, 4, 5, &[1, 2, 3], &[4]);
    assert_region(&conds, 1, 2, 3, 5, &[2], &[3]);
  }

  #[test]
  fn detects_conditional_in_loop_body() {
    let cfg = build_cfg(
      &[(0, 2), (2, 3), (2, 4), (3, 2), (4, 5), (5, u32::MAX)],
      &[
        (0, vec![]),
        (2, vec![cond_inst(3, 4)]),
        (3, vec![]),
        (4, vec![]),
        (5, vec![]),
      ],
    );
    let dom = Dom::calculate(&cfg);
    let postdom = PostDom::calculate(&cfg);
    let conds = find_conds(&cfg, &dom, &postdom);
    assert_region(&conds, 2, 3, 4, 4, &[3], &[]);
  }
