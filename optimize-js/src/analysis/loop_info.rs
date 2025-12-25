use crate::analysis::find_loops::find_loops;
use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;

#[derive(Debug)]
pub struct LoopInfo {
  pub loops: Vec<Loop>,
  pub header_to_loop: HashMap<u32, LoopId>,
  /// Pairs of loops whose node sets overlap without a strict nesting relationship.
  /// These are irreducible for the purposes of structured reconstruction.
  pub overlapping: Vec<(LoopId, LoopId)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoopId(pub u32);

#[derive(Debug)]
pub struct Loop {
  pub id: LoopId,
  pub header: u32,
  pub parent: Option<LoopId>,
  pub children: Vec<LoopId>,
  pub nodes: HashSet<u32>,
  pub latches: Vec<u32>,
  pub exits: Vec<(u32, u32)>,
}

impl LoopInfo {
  pub fn compute(cfg: &Cfg, dom: &Dom) -> Self {
    Self::from_loops_map(cfg, dom, find_loops(cfg, dom))
  }

  pub(crate) fn from_loops_map(
    cfg: &Cfg,
    dom: &Dom,
    loops_map: HashMap<u32, HashSet<u32>>,
  ) -> Self {
    let dominates = dom.dominates_graph();

    let mut loop_entries = loops_map.into_iter().collect::<Vec<_>>();
    loop_entries.sort_by(|(h1, n1), (h2, n2)| {
      h1.cmp(h2).then_with(|| n2.len().cmp(&n1.len()))
    });

    let mut loops = Vec::<Loop>::new();
    let mut header_to_loop = HashMap::new();
    for (idx, (header, nodes)) in loop_entries.into_iter().enumerate() {
      let mut latches = cfg
        .graph
        .parents(header)
        .filter(|&tail| dominates.dominates(header, tail))
        .collect::<Vec<_>>();
      latches.sort_unstable();
      latches.dedup();

      let mut exits = Vec::<(u32, u32)>::new();
      for &node in nodes.iter() {
        for succ in cfg.graph.children(node) {
          if !nodes.contains(&succ) {
            exits.push((node, succ));
          }
        }
      }
      exits.sort_unstable();
      exits.dedup();

      let id = LoopId(idx as u32);
      header_to_loop.insert(header, id);
      loops.push(Loop {
        id,
        header,
        parent: None,
        children: Vec::new(),
        nodes,
        latches,
        exits,
      });
    }

    let mut parents: Vec<Option<usize>> = vec![None; loops.len()];
    for i in 0..loops.len() {
      for j in 0..loops.len() {
        if i == j {
          continue;
        }
        let child_nodes = &loops[i].nodes;
        let parent_nodes = &loops[j].nodes;
        if child_nodes.len() < parent_nodes.len() && child_nodes.is_subset(parent_nodes) {
          let replace = parents[i].map_or(true, |cur| {
            let cur_nodes = &loops[cur].nodes;
            parent_nodes.len() < cur_nodes.len()
              || (parent_nodes.len() == cur_nodes.len()
                && loops[j].header < loops[cur].header)
          });
          if replace {
            parents[i] = Some(j);
          }
        }
      }
    }

    let mut overlapping = Vec::<(LoopId, LoopId)>::new();
    for i in 0..loops.len() {
      for j in (i + 1)..loops.len() {
        let left = &loops[i].nodes;
        let right = &loops[j].nodes;
        let left_in_right = left.len() < right.len() && left.is_subset(right);
        let right_in_left = right.len() < left.len() && right.is_subset(left);
        if !left_in_right && !right_in_left && !left.is_disjoint(right) {
          overlapping.push((LoopId(i as u32), LoopId(j as u32)));
        }
      }
    }
    overlapping.sort_by(|(a1, b1), (a2, b2)| a1.0.cmp(&a2.0).then(b1.0.cmp(&b2.0)));
    overlapping.dedup();

    for (idx, parent) in parents.into_iter().enumerate() {
      if let Some(parent) = parent {
        loops[idx].parent = Some(LoopId(parent as u32));
        loops[parent].children.push(LoopId(idx as u32));
      }
    }

    let header_by_id = loops.iter().map(|l| l.header).collect::<Vec<_>>();
    for l in loops.iter_mut() {
      l
        .children
        .sort_by_key(|child| header_by_id[child.0 as usize]);
    }

    LoopInfo {
      loops,
      header_to_loop,
      overlapping,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::cfg::cfg::Cfg;
  use crate::cfg::cfg::CfgGraph;
  use crate::dom::Dom;
  use ahash::HashMap;
  use std::iter::FromIterator;

  fn nested_cfg() -> Cfg {
    let mut graph = CfgGraph::default();
    graph.connect(0, 1);
    graph.connect(1, 2);
    graph.connect(2, 3);
    graph.connect(3, 2);
    graph.connect(2, 4);
    graph.connect(4, 1);
    graph.connect(1, 5);
    Cfg {
      graph,
      bblocks: Default::default(),
    }
  }

  #[test]
  fn builds_nested_loop_hierarchy() {
    let cfg = nested_cfg();
    let dom = Dom::calculate(&cfg);
    let info = LoopInfo::compute(&cfg, &dom);

    assert!(info.overlapping.is_empty());
    assert_eq!(info.loops.len(), 2);

    let outer = info.header_to_loop[&1];
    let inner = info.header_to_loop[&2];

    let outer_loop = &info.loops[outer.0 as usize];
    let inner_loop = &info.loops[inner.0 as usize];

    assert_eq!(inner_loop.parent, Some(outer));
    assert_eq!(outer_loop.children, vec![inner]);
    assert_eq!(outer_loop.latches, vec![4]);
    assert_eq!(inner_loop.latches, vec![3]);
    assert_eq!(outer_loop.exits, vec![(1, 5)]);
    assert_eq!(inner_loop.exits, vec![(2, 4)]);
  }

  #[test]
  fn collects_multiple_latches_for_one_header() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 1);
    graph.connect(1, 2);
    graph.connect(2, 1);
    graph.connect(1, 3);
    graph.connect(3, 1);
    graph.connect(1, 4);
    let cfg = Cfg {
      graph,
      bblocks: Default::default(),
    };
    let dom = Dom::calculate(&cfg);
    let info = LoopInfo::compute(&cfg, &dom);

    assert!(info.overlapping.is_empty());
    assert_eq!(info.loops.len(), 1);
    let loop0 = &info.loops[0];
    assert_eq!(loop0.header, 1);
    assert_eq!(loop0.latches, vec![2, 3]);
    assert_eq!(loop0.exits, vec![(1, 4)]);
  }

  #[test]
  fn flags_overlapping_loops() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 1);
    graph.connect(1, 2);
    graph.connect(2, 3);
    graph.connect(3, 1);
    graph.connect(2, 4);
    graph.connect(4, 2);
    graph.connect(2, 5);
    let cfg = Cfg {
      graph,
      bblocks: Default::default(),
    };
    let dom = Dom::calculate(&cfg);
    let info = LoopInfo::from_loops_map(
      &cfg,
      &dom,
      HashMap::from_iter([
        (1, HashSet::from_iter([1, 2, 3])),
        (2, HashSet::from_iter([2, 4])),
      ]),
    );

    assert_eq!(
      info.overlapping,
      vec![(info.header_to_loop[&1], info.header_to_loop[&2])]
    );

    let loop1 = &info.loops[info.header_to_loop[&1].0 as usize];
    let loop2 = &info.loops[info.header_to_loop[&2].0 as usize];

    assert_eq!(loop1.parent, None);
    assert_eq!(loop2.parent, None);
    assert_eq!(loop1.latches, vec![3]);
    assert_eq!(loop2.latches, vec![4]);
    assert_eq!(loop1.exits, vec![(2, 4), (2, 5)]);
    assert_eq!(loop2.exits, vec![(2, 3), (2, 5)]);
  }
}
