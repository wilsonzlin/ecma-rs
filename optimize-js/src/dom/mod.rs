use crate::cfg::cfg::Cfg;
use crate::cfg::cfg::CfgGraph;
use ahash::HashMap;
use ahash::HashSet;
use ahash::HashSetExt;
use itertools::Itertools;
use std::collections::VecDeque;

fn reachable_from_entry(cfg: &Cfg) -> HashSet<u32> {
  let mut reachable = HashSet::new();
  let mut queue = VecDeque::from([0]);
  while let Some(label) = queue.pop_front() {
    if !reachable.insert(label) {
      continue;
    };
    let mut children = cfg.graph.children(label).collect_vec();
    children.sort_unstable();
    queue.extend(children);
  }
  reachable
}

fn terminal_nodes(cfg: &Cfg, reachable: &HashSet<u32>) -> Vec<u32> {
  let mut terminals = reachable
    .iter()
    .copied()
    .filter(|label| cfg.graph.children(*label).next().is_none())
    .collect_vec();
  terminals.sort_unstable();
  terminals
}

fn blocks_that_can_reach_terminals(
  cfg: &Cfg,
  reachable: &HashSet<u32>,
  terminals: &[u32],
) -> HashSet<u32> {
  let mut can_reach_terminal = HashSet::new();
  let mut queue = VecDeque::new();
  for &label in terminals.iter() {
    if can_reach_terminal.insert(label) {
      queue.push_back(label);
    }
  }
  while let Some(label) = queue.pop_front() {
    let mut parents = cfg.graph.parents(label).collect_vec();
    parents.sort_unstable();
    for parent in parents {
      if reachable.contains(&parent) && can_reach_terminal.insert(parent) {
        queue.push_back(parent);
      }
    }
  }
  can_reach_terminal
}

/// Returns reachable blocks from entry and the set of blocks that should be treated as exits for
/// postdominance calculations (terminal + divergent).
pub(crate) fn virtual_exit_roots(cfg: &Cfg) -> (HashSet<u32>, Vec<u32>) {
  let reachable = reachable_from_entry(cfg);
  let terminals = terminal_nodes(cfg, &reachable);
  let can_reach_terminal = blocks_that_can_reach_terminals(cfg, &reachable, &terminals);
  let mut exits = terminals;
  exits.extend(
    reachable
      .iter()
      .filter(|label| !can_reach_terminal.contains(label))
      .copied(),
  );
  exits.sort_unstable();
  exits.dedup();
  (reachable, exits)
}

pub struct DominatesGraph(HashMap<u32, HashSet<u32>>);

impl DominatesGraph {
  pub fn dominates(&self, a: u32, b: u32) -> bool {
    self.0.get(&a).is_some_and(|s| s.contains(&b))
  }
}

pub struct DominatedByGraph(HashMap<u32, HashSet<u32>>);

impl DominatedByGraph {
  pub fn dominated_by(&self, a: u32, b: u32) -> bool {
    self.0.get(&a).is_some_and(|s| s.contains(&b))
  }
}

pub type PostDom = Dom<true>;

fn find_virtual_exit_label(labels: &[u32]) -> u32 {
  let label_set: HashSet<u32> = HashSet::from_iter(labels.iter().copied());
  let mut exit = u32::MAX;
  while label_set.contains(&exit) {
    exit = exit.checked_sub(1).expect("unable to find unused virtual exit label");
  }
  exit
}

fn calculate_sink_sccs(graph: &CfgGraph) -> Vec<Vec<u32>> {
  fn strongconnect(
    v: u32,
    graph: &CfgGraph,
    index: &mut u32,
    stack: &mut Vec<u32>,
    on_stack: &mut HashSet<u32>,
    indices: &mut HashMap<u32, u32>,
    lowlink: &mut HashMap<u32, u32>,
    components: &mut Vec<Vec<u32>>,
  ) {
    indices.insert(v, *index);
    lowlink.insert(v, *index);
    *index += 1;
    stack.push(v);
    on_stack.insert(v);

    let mut neighbors = graph.children(v).collect_vec();
    neighbors.sort_unstable();
    for w in neighbors {
      if !indices.contains_key(&w) {
        strongconnect(
          w, graph, index, stack, on_stack, indices, lowlink, components,
        );
        let low_v = lowlink[&v];
        let low_w = lowlink[&w];
        lowlink.insert(v, low_v.min(low_w));
      } else if on_stack.contains(&w) {
        let low_v = lowlink[&v];
        let idx_w = indices[&w];
        lowlink.insert(v, low_v.min(idx_w));
      }
    }

    if indices[&v] == lowlink[&v] {
      let mut component = Vec::new();
      loop {
        let w = stack.pop().unwrap();
        on_stack.remove(&w);
        component.push(w);
        if w == v {
          break;
        }
      }
      component.sort_unstable();
      components.push(component);
    }
  }

  let mut index = 0u32;
  let mut stack = Vec::new();
  let mut on_stack = HashSet::default();
  let mut indices = HashMap::default();
  let mut lowlink = HashMap::default();
  let mut components = Vec::new();

  let mut nodes: Vec<u32> = graph.labels().collect();
  nodes.sort_unstable();
  for n in nodes {
    if !indices.contains_key(&n) {
      strongconnect(
        n,
        graph,
        &mut index,
        &mut stack,
        &mut on_stack,
        &mut indices,
        &mut lowlink,
        &mut components,
      );
    }
  }

  let mut node_to_component = HashMap::<u32, usize>::default();
  for (idx, comp) in components.iter().enumerate() {
    for &n in comp {
      node_to_component.insert(n, idx);
    }
  }

  let mut is_sink = vec![true; components.len()];
  for (idx, comp) in components.iter().enumerate() {
    for &n in comp {
      let mut children: Vec<u32> = graph.children(n).collect();
      children.sort_unstable();
      for child in children {
        if let Some(&child_comp) = node_to_component.get(&child) {
          if child_comp != idx {
            is_sink[idx] = false;
            break;
          }
        }
      }
      if !is_sink[idx] {
        break;
      }
    }
  }

  let mut sink_components: Vec<Vec<u32>> = components
    .into_iter()
    .enumerate()
    .filter_map(|(idx, mut comp)| {
      if is_sink[idx] {
        comp.sort_unstable();
        Some(comp)
      } else {
        None
      }
    })
    .collect();
  sink_components.sort_by_key(|comp| comp[0]);
  sink_components
}

fn augment_cfg_for_postdom(cfg: &Cfg) -> (CfgGraph, u32) {
  let mut graph = CfgGraph::from_graph(cfg.graph.clone_graph());

  let mut labels: Vec<u32> = graph.labels().collect();
  labels.sort_unstable();
  let exit = find_virtual_exit_label(&labels);

  let sink_sccs = calculate_sink_sccs(&graph);

  let mut to_exit = HashSet::from_iter(labels.iter().copied().filter(|label| graph.children(*label).next().is_none()));
  for component in sink_sccs {
    to_exit.extend(component);
  }
  let mut to_exit: Vec<u32> = to_exit.into_iter().collect();
  to_exit.sort_unstable();
  for node in to_exit {
    graph.connect(node, exit);
  }

  #[cfg(debug_assertions)]
  {
    let mut seen = HashSet::from_iter([exit]);
    let mut stack = vec![exit];
    while let Some(node) = stack.pop() {
      let mut parents: Vec<u32> = graph.parents(node).collect();
      parents.sort_unstable();
      for parent in parents {
        if seen.insert(parent) {
          stack.push(parent);
        }
      }
    }
    debug_assert!(labels.iter().all(|l| seen.contains(l)));
  }

  (graph, exit)
}

/// If `POST`, calculates postdominance instead of dominance.
pub struct Dom<const POST: bool = false> {
  postorder: Vec<u32>,
  // Inverse of `domtree`, child => parent.
  idom_by: HashMap<u32, u32>,
  // Parent => children, where parent is the immediate dominator of each child.
  // Yes, the name is dominator tree, even though it's only nodes it immediate dominates and not all nodes it dominates. See https://en.wikipedia.org/wiki/Dominator_(graph_theory).
  domtree: HashMap<u32, HashSet<u32>>,
  entry: u32,
}

impl<const POST: bool> Dom<POST> {
  // A dominates B if A will **always** execute some time at or before B. (All paths to B go through A.)
  // B is dominated by A if A also dominates **all** of B's parents. (Think about it.)
  // Dominance tree: edges represent only "immediate" dominations. A immediately dominates B iff A dominates B and doesn't strictly dominate any other node that strictly dominates B. (Strictly dominates means A dominates B and A != B.)
  // NOTE: Every node, except the entry node, has exactly one immediate dominator: https://en.wikipedia.org/wiki/Dominator_(graph_theory).
  //
  // https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
  // - This paper also contains an explanation on how to calculate what a node dominates given `idom_by`, which is much faster than other dominance calculation algorithms.
  // Other implementations:
  // - https://github.com/sampsyo/bril/blob/34133101a68bb50ae0fc8083857a3e3bd6bae260/bril-llvm/dom.py#L47
  // To calculate the post dominators, reverse the edges and run any dominator algorithm. This is what we do when `POST` is true.
  pub fn calculate(cfg: &Cfg) -> Self {
    let (post_graph, entry, postorder, label_to_postorder) = if POST {
      let (graph, entry) = augment_cfg_for_postdom(cfg);
      let (postorder, label_to_postorder) = graph.calculate_reversed_graph_postorder(entry);
      (Some(graph), entry, postorder, label_to_postorder)
    } else {
      let entry = 0;
      let (postorder, label_to_postorder) = cfg.graph.calculate_postorder(entry);
      (None, entry, postorder, label_to_postorder)
    };

    let graph = post_graph.as_ref().unwrap_or(&cfg.graph);

    let mut idom_by = HashMap::<u32, u32>::default();
    let mut domtree = HashMap::<u32, HashSet<u32>>::default();
    {
      macro_rules! intersect {
        ($b1:expr, $b2:expr) => {{
          // WARNING: We're getting the position in postorder, NOT reverse postorder.
          let mut finger1 = label_to_postorder[&$b1];
          let mut finger2 = label_to_postorder[&$b2];
          while finger1 != finger2 {
            while finger1 < finger2 {
              finger1 = label_to_postorder[&idom_by[&postorder[finger1]]];
            }
            while finger2 < finger1 {
              finger2 = label_to_postorder[&idom_by[&postorder[finger2]]];
            }
          }
          postorder[finger1]
        }};
      }
      idom_by.insert(entry, entry);
      loop {
        let mut changed = false;
        for &b in postorder.iter().rev().filter(|b| **b != entry) {
          let mut parents = if POST { graph.children(b) } else { graph.parents(b) }.collect_vec();
          parents.sort_unstable();
          let Some(mut new_idom) = parents.iter().find(|n| idom_by.contains_key(n)).cloned() else {
            continue;
          };
          let to_skip = new_idom;
          for p in parents.iter().filter(|&&p| p != to_skip) {
            if idom_by.contains_key(&p) {
              new_idom = intersect!(p, new_idom);
            };
          }
          if idom_by.get(&b) != Some(&new_idom) {
            idom_by.insert(b, new_idom);
            changed = true;
          }
        }
        if !changed {
          break;
        };
      }
      idom_by.remove(&entry);
      for (&c, &p) in idom_by.iter() {
        domtree.entry(p).or_default().insert(c);
      }
    };
    Self {
      postorder,
      idom_by,
      domtree,
      entry,
    }
  }

  pub fn idom_of(&self, node: u32) -> Option<u32> {
    self.idom_by.get(&node).copied()
  }

  pub fn entry_label(&self) -> u32 {
    self.entry
  }

  // Node => nodes that dominate it (are its dominator). Also called the dominator graph.
  // https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
  pub fn dominated_by_graph(&self) -> DominatedByGraph {
    let mut dom = HashMap::<u32, HashSet<u32>>::default();
    dom.entry(self.entry).or_default().insert(self.entry);
    for label in self.idom_by.keys().cloned() {
      let e = dom.entry(label).or_default();
      let mut n = label;
      loop {
        e.insert(n);
        if n == self.entry {
          break;
        };
        n = self.idom_by[&n];
      }
    }
    DominatedByGraph(dom)
  }

  /// Node => nodes that it dominates.
  /// The inverse of `dominated_bys`.
  pub fn dominates_graph(&self) -> DominatesGraph {
    let dom_bys = self.dominated_by_graph();
    let mut doms = HashMap::<u32, HashSet<u32>>::default();
    for (child, dominated_by) in dom_bys.0 {
      for parent in dominated_by {
        doms.entry(parent).or_default().insert(child);
      }
    }
    DominatesGraph(doms)
  }

  // A's dominance frontier contains B if A doesn't dominate B, but does dominate a parent of B.
  // One way of thinking about it: it's the nodes immediately adjacent to the subgraph of A's domination.
  // Another way to think about it: B is dominated by A if all of B's parents are dominated by A (see comments further up). On the other hand, if it's in the fringe, at least one parent is dominated by A, but not all of them.
  // https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
  // Other implementations: https://github.com/sampsyo/bril/blob/34133101a68bb50ae0fc8083857a3e3bd6bae260/bril-llvm/dom.py#L69
  // It'd be nice to store `cfg` on `Dom`, but that'd keep it borrowed, and usually we want to mutate the CFG using dominance information (and not recalculate every time).
  pub fn dominance_frontiers(&self, cfg: &Cfg) -> HashMap<u32, HashSet<u32>> {
    let mut domfront = HashMap::<u32, HashSet<u32>>::default();
    for &b in self.postorder.iter().rev() {
      if !self.idom_by.contains_key(&b) {
        continue;
      }
      let mut parents = cfg.graph.parents(b).collect_vec();
      parents.sort_unstable();
      if parents.len() < 2 {
        continue;
      };
      for &p in parents.iter() {
        let mut runner = p;
        while runner != self.idom_by[&b] {
          domfront.entry(runner).or_default().insert(b);
          runner = self.idom_by[&runner];
        }
      }
    }
    domfront
  }

  /// Yields the child nodes that are immediately dominated by the parent node.
  pub fn immediately_dominated_by(&self, parent: u32) -> impl Iterator<Item = u32> + '_ {
    self
      .domtree
      .get(&parent)
      .map(|s| {
        let mut children = s.iter().copied().collect_vec();
        children.sort_unstable();
        children
      })
      .into_iter()
      .flatten()
  }

  pub fn idom(&self, node: u32) -> Option<u32> {
    self.idom_by.get(&node).copied()
  }

  pub fn immediate_dominator(&self, node: u32) -> Option<u32> {
    self.idom(node)
  }

  pub fn lca(&self, a: u32, b: u32) -> Option<u32> {
    if a == b {
      return Some(a);
    }

    let mut ancestors = HashSet::default();
    let mut current = a;
    loop {
      ancestors.insert(current);
      if current == self.entry {
        break;
      }
      current = *self.idom_by.get(&current)?;
    }

    let mut current = b;
    loop {
      if ancestors.contains(&current) {
        return Some(current);
      }
      if current == self.entry {
        break;
      }
      current = *self.idom_by.get(&current)?;
    }
    None
  }

  pub fn lca_all(&self, nodes: impl IntoIterator<Item = u32>) -> Option<u32> {
    let mut iter = nodes.into_iter();
    let mut acc = iter.next()?;
    for n in iter {
      acc = self.lca(acc, n)?;
    }
    Some(acc)
  }

  pub fn entry(&self) -> u32 {
    self.entry
  }

  pub fn postorder(&self) -> &[u32] {
    &self.postorder
  }
}

#[cfg(test)]
mod tests {
  use crate::cfg::cfg::Cfg;
  use crate::cfg::cfg::CfgGraph;
  use crate::dom::Dom;
  use crate::dom::PostDom;

  fn cfg_from_edges(edges: &[(u32, u32)]) -> Cfg {
    let mut graph = CfgGraph::default();
    for &(parent, child) in edges {
      graph.connect(parent, child);
    }
    Cfg {
      bblocks: Default::default(),
      graph,
    }
  }

  #[test]
  fn dominance_basic() {
    let cfg = cfg_from_edges(&[(0, 1), (0, 2), (1, 3), (2, 3)]);
    let dom = Dom::<false>::calculate(&cfg);
    assert!(dom.dominates_graph().dominates(0, 3));
    assert!(dom.dominated_by_graph().dominated_by(3, 0));
  }

  #[test]
  fn postdom_diamond() {
    let cfg = cfg_from_edges(&[(0, 1), (0, 2), (1, 3), (2, 3)]);
    let postdom = PostDom::calculate(&cfg);
    let exit = postdom.entry();
    assert_eq!(postdom.idom(1), Some(3));
    assert_eq!(postdom.idom(2), Some(3));
    assert_eq!(postdom.idom(0), Some(3));
    assert_eq!(postdom.idom(3), Some(exit));
  }

  #[test]
  fn postdom_loop_follow_block() {
    let cfg = cfg_from_edges(&[(0, 1), (1, 1), (1, 2)]);
    let postdom = PostDom::calculate(&cfg);
    let exit = postdom.entry();
    assert_eq!(postdom.idom(0), Some(1));
    assert_eq!(postdom.idom(1), Some(2));
    assert_eq!(postdom.idom(2), Some(exit));
  }

  #[test]
  fn postdom_infinite_loop_sink_scc() {
    let cfg = cfg_from_edges(&[(0, 0)]);
    let postdom = PostDom::calculate(&cfg);
    let exit = postdom.entry();
    assert_eq!(postdom.idom(0), Some(exit));
    assert!(postdom.postorder().contains(&0));
    assert!(postdom.postorder().contains(&exit));
  }

  #[test]
  fn postdom_multiple_exits() {
    let cfg = cfg_from_edges(&[(0, 1), (0, 2)]);
    let postdom = PostDom::calculate(&cfg);
    let exit = postdom.entry();
    assert_eq!(postdom.idom(1), Some(exit));
    assert_eq!(postdom.idom(2), Some(exit));
    assert_eq!(postdom.idom(0), Some(exit));
  }

  #[test]
  fn postdom_virtual_exit_collision() {
    let cfg = cfg_from_edges(&[(0, u32::MAX)]);
    let postdom = PostDom::calculate(&cfg);
    assert_ne!(postdom.entry(), u32::MAX);
    assert_eq!(postdom.idom(u32::MAX), Some(postdom.entry()));
  }
}
