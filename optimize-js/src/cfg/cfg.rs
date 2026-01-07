use crate::graph::Graph;
use crate::graph::GraphRelatedNodesIter;
use crate::il::inst::Arg;
use crate::il::inst::Inst;
use crate::il::inst::InstTyp;
use crate::il::s2i::DUMMY_LABEL;
use ahash::HashMap;
use ahash::HashSet;
use itertools::Itertools;
use std::collections::VecDeque;
use std::iter;

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Terminator {
  /// No outgoing edges from this block.
  Stop,
  /// Exactly one outgoing edge.
  Goto(u32),
  /// Conditional branch represented explicitly by `InstTyp::CondGoto`.
  CondGoto { cond: Arg, t: u32, f: u32 },
  /// Multi-way branch not representable as a simple conditional.
  Multi { targets: Vec<u32> },
}

/// Wrapper over a Graph<u32> that provides owned types and better method names,
/// as well as domain-specific methods.
#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct CfgGraph(Graph<u32>);

impl CfgGraph {
  pub fn labels(&self) -> impl Iterator<Item = u32> + '_ {
    self.0.nodes().cloned()
  }

  pub fn contains(&self, label: u32) -> bool {
    self.0.contains(&label)
  }

  pub fn labels_sorted(&self) -> Vec<u32> {
    let mut labels = self.labels().collect_vec();
    labels.sort_unstable();
    labels
  }

  pub fn sorted_labels(&self) -> Vec<u32> {
    self.labels_sorted()
  }

  pub fn clone_graph(&self) -> Graph<u32> {
    self.0.clone()
  }

  pub fn from_graph(graph: Graph<u32>) -> Self {
    Self(graph)
  }

  pub fn parents(&self, bblock: u32) -> iter::Cloned<GraphRelatedNodesIter<'_, u32>> {
    self.0.parents(&bblock).cloned()
  }

  pub fn parents_sorted(&self, bblock: u32) -> Vec<u32> {
    let mut parents = self.parents(bblock).collect_vec();
    parents.sort_unstable();
    parents
  }

  pub fn sorted_parents(&self, bblock: u32) -> Vec<u32> {
    self.parents_sorted(bblock)
  }

  pub fn children(&self, bblock: u32) -> iter::Cloned<GraphRelatedNodesIter<'_, u32>> {
    self.0.children(&bblock).cloned()
  }

  pub fn children_sorted(&self, bblock: u32) -> Vec<u32> {
    let mut children = self.children(bblock).collect_vec();
    children.sort_unstable();
    children
  }

  pub fn sorted_children(&self, bblock: u32) -> Vec<u32> {
    self.children_sorted(bblock)
  }

  pub fn connect(&mut self, parent: u32, child: u32) {
    self.0.connect(&parent, &child);
  }

  pub fn disconnect(&mut self, parent: u32, child: u32) {
    self.0.disconnect(&parent, &child);
  }

  pub fn delete_many(&mut self, bblocks: impl IntoIterator<Item = u32>) {
    for bblock in bblocks {
      self.0.contract(&bblock);
    }
  }

  /// Remove a disconnected bblock from the graph.
  /// Panics if still connected or doesn't exist.
  pub fn pop(&mut self, bblock: u32) {
    self.0.pop(&bblock);
  }

  /**
   * WARNING: It is dangerous to remove empty bblocks, as they can have significance despite being empty:
   * - Phi insts still need to distinguish between different branches for different values. This can happen quite often with const propagation, where an empty block merely determines which const value in a Phi is picked.
   * When is it safe to remove a bblock (and move insts and fix up parent-child relationships and Phi insts)?
   * - When a bblock has exactly one parent and that parent has exactly one child.
   * - When an empty bblock has no children.
   * - When an empty bblock has no children with Phi insts.
   */
  pub fn find_unreachable(&self, entry: u32) -> impl Iterator<Item = u32> + '_ {
    let mut seen = HashSet::from_iter([entry]);
    let mut to_visit = VecDeque::from([entry]);
    while let Some(n) = to_visit.pop_front() {
      for c in self.children_sorted(n) {
        if !seen.contains(&c) {
          seen.insert(c);
          to_visit.push_back(c);
        };
      }
    }
    // Find unreachable bblocks deterministically.
    let mut unreachable = self.labels_sorted();
    unreachable.retain(|n| !seen.contains(n));
    unreachable.into_iter()
  }

  pub fn calculate_postorder(&self, entry: u32) -> (Vec<u32>, HashMap<u32, usize>) {
    let (postorder, label_to_postorder) = self.0.calculate_postorder(&entry);
    (
      postorder.into_iter().map(|&n| n).collect_vec(),
      label_to_postorder
        .into_iter()
        .map(|(&k, v)| (k, v))
        .collect::<HashMap<_, _>>(),
    )
  }

  /// WARNING: This is not the same as reverse postorder. This is the postorder of the reversed graph.
  pub fn calculate_reversed_graph_postorder(&self, entry: u32) -> (Vec<u32>, HashMap<u32, usize>) {
    let (postorder, label_to_postorder) = self.0.calculate_reversed_graph_postorder(&entry);
    (
      postorder.into_iter().map(|&n| n).collect_vec(),
      label_to_postorder
        .into_iter()
        .map(|(&k, v)| (k, v))
        .collect::<HashMap<_, _>>(),
    )
  }
}

/// Wrapper over a HashMap that provides owned types and better method names,
/// as well as domain-specific methods.
#[derive(Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct CfgBBlocks(HashMap<u32, Vec<Inst>>);

impl CfgBBlocks {
  pub fn get(&self, label: u32) -> &Vec<Inst> {
    self.0.get(&label).unwrap()
  }

  pub fn maybe_get(&self, label: u32) -> Option<&Vec<Inst>> {
    self.0.get(&label)
  }

  pub fn get_mut(&mut self, label: u32) -> &mut Vec<Inst> {
    self.0.get_mut(&label).unwrap()
  }

  pub fn add(&mut self, label: u32, bblock: Vec<Inst>) {
    assert!(self.0.insert(label, bblock).is_none());
  }

  pub fn remove(&mut self, label: u32) -> Vec<Inst> {
    self.0.remove(&label).unwrap()
  }

  pub fn remove_many(&mut self, labels: impl IntoIterator<Item = u32>) -> Vec<Vec<Inst>> {
    labels.into_iter().map(|label| self.remove(label)).collect()
  }

  pub fn all(&self) -> impl Iterator<Item = (u32, &Vec<Inst>)> {
    self.0.iter().map(|(k, v)| (*k, v))
  }

  pub fn all_mut(&mut self) -> impl Iterator<Item = (u32, &mut Vec<Inst>)> {
    self.0.iter_mut().map(|(k, v)| (*k, v))
  }
}

/// Control flow graph. Contains the bblock graph and the bblocks themselves.
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Cfg {
  // We store these as different fields because we often want to mutate one while holding a reference to the other. If we only provide &mut self methods, we'd have to borrow both mutably at the same time.
  pub graph: CfgGraph,
  pub bblocks: CfgBBlocks,
  pub entry: u32,
}

/// Helper methods for operating on both Cfg graph and bblocks at once and therefore keep them in sync.
impl Cfg {
  /// Removes a disconnected bblock from the graph and the bblocks.
  /// Panics if still connected.
  pub fn pop(&mut self, label: u32) -> Vec<Inst> {
    if self.graph.contains(label) {
      self.graph.pop(label);
    }
    self.bblocks.remove(label)
  }

  /// Disconnects unreachable bblocks from the graph and removes them from the bblocks.
  /// Returns the labels of the removed bblocks.
  pub fn find_and_pop_unreachable(&mut self) -> Vec<u32> {
    let to_delete = self.graph.find_unreachable(self.entry).collect_vec();
    self.graph.delete_many(to_delete.iter().cloned());
    self.bblocks.remove_many(to_delete.iter().cloned());
    to_delete
  }
}

impl Cfg {
  pub fn from_bblocks(
    mut bblocks: HashMap<u32, Vec<Inst>>,
    // We consume this because all subsequent analysis operations should use a well-defined order (e.g. reverse postorder) for safety/correctness, and not this rather arbitrary ordering.
    bblock_order: Vec<u32>,
  ) -> Self {
    let mut graph = Graph::new();
    for i in 0..bblocks.len() {
      let parent = bblock_order[i];
      if let Some(Inst {
        t: InstTyp::_Goto,
        labels,
        ..
      }) = bblocks[&parent].last()
      {
        let label = labels[0];
        graph.connect(&parent, &label);
        // We don't want Goto insts after this point.
        bblocks.get_mut(&parent).unwrap().pop().unwrap();
      } else if let Some(Inst {
        t: InstTyp::CondGoto,
        labels,
        ..
      }) = bblocks.get_mut(&parent).unwrap().last_mut()
      {
        for label in labels.iter_mut() {
          // We use DUMMY_LABEL during source_to_inst for one branch of a CondGoto to indicate fallthrough.
          // We must update the Inst label too.
          if *label == DUMMY_LABEL {
            *label = bblock_order[i + 1];
          };
          graph.connect(&parent, label);
        }
      } else if i == bblocks.len() - 1 {
        // Last bblock, don't connect to anything.
      } else {
        // Implicit fallthrough.
        graph.connect(&parent, &bblock_order[i + 1]);
      };
    }
    Self {
      graph: CfgGraph(graph),
      bblocks: CfgBBlocks(bblocks),
      entry: 0,
    }
  }

  pub fn reverse_postorder(&self) -> Vec<u32> {
    let (postorder, _) = self.graph.calculate_postorder(self.entry);
    postorder.into_iter().rev().collect()
  }

  pub fn terminator(&self, label: u32) -> Terminator {
    if let Some(inst) = self.bblocks.get(label).last() {
      if inst.t == InstTyp::CondGoto {
        let (cond, t, f) = inst.as_cond_goto();
        return Terminator::CondGoto {
          cond: cond.clone(),
          t,
          f,
        };
      }
    }

    let children = self.graph.sorted_children(label);
    match children.len() {
      0 => Terminator::Stop,
      1 => Terminator::Goto(children[0]),
      _ => Terminator::Multi { targets: children },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::il::inst::Arg;

  fn make_cfg(graph: CfgGraph, bblocks: CfgBBlocks) -> Cfg {
    Cfg {
      graph,
      bblocks,
      entry: 0,
    }
  }

  #[test]
  fn terminator_implicit_fallthrough() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 1);

    let mut bblocks = CfgBBlocks::default();
    bblocks.add(0, vec![Inst::var_assign(0, Arg::Var(1))]);
    bblocks.add(1, vec![]);

    let cfg = make_cfg(graph, bblocks);
    assert_eq!(cfg.terminator(0), Terminator::Goto(1));
  }

  #[test]
  fn terminator_conditional_branch() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 2);
    graph.connect(0, 1);

    let mut bblocks = CfgBBlocks::default();
    bblocks.add(0, vec![Inst::cond_goto(Arg::Var(0), 1, 2)]);
    bblocks.add(1, vec![]);
    bblocks.add(2, vec![]);

    let cfg = make_cfg(graph, bblocks);
    assert_eq!(
      cfg.terminator(0),
      Terminator::CondGoto {
        cond: Arg::Var(0),
        t: 1,
        f: 2
      }
    );
  }

  #[test]
  fn terminator_leaf_block() {
    let graph = CfgGraph::default();
    let mut bblocks = CfgBBlocks::default();
    bblocks.add(0, vec![]);

    let cfg = make_cfg(graph, bblocks);
    assert_eq!(cfg.terminator(0), Terminator::Stop);
  }

  #[test]
  fn terminator_self_loop_block() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 0);

    let mut bblocks = CfgBBlocks::default();
    bblocks.add(0, vec![Inst::var_assign(0, Arg::Var(1))]);

    let cfg = make_cfg(graph, bblocks);
    assert_eq!(cfg.terminator(0), Terminator::Goto(0));
  }

  #[test]
  fn terminator_multi_branch_is_sorted() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 3);
    graph.connect(0, 1);
    graph.connect(0, 2);

    let mut bblocks = CfgBBlocks::default();
    bblocks.add(0, vec![Inst::var_assign(0, Arg::Var(1))]);
    bblocks.add(1, vec![]);
    bblocks.add(2, vec![]);
    bblocks.add(3, vec![]);

    let cfg = make_cfg(graph, bblocks);
    assert_eq!(
      cfg.terminator(0),
      Terminator::Multi {
        targets: vec![1, 2, 3]
      }
    );
  }

  #[test]
  fn reverse_postorder_uses_sorted_traversal() {
    let mut graph = CfgGraph::default();
    graph.connect(0, 2);
    graph.connect(0, 1);

    let mut bblocks = CfgBBlocks::default();
    bblocks.add(0, vec![]);
    bblocks.add(1, vec![]);
    bblocks.add(2, vec![]);

    let cfg = make_cfg(graph, bblocks);
    assert_eq!(cfg.reverse_postorder(), vec![0, 2, 1]);
  }
}
