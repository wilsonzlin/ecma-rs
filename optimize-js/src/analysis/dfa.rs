use crate::cfg::cfg::Cfg;
use crate::il::inst::Inst;
use ahash::HashMap;
use ahash::HashSet;
use itertools::chain;
use itertools::Itertools;
use std::collections::VecDeque;
use std::hash::Hash;

#[derive(Clone, PartialEq, Eq)]
pub enum Set<T: Clone + Eq + Hash> {
  Finite(HashSet<T>),
  Infinite,
}

impl<T: Clone + Eq + Hash> Set<T> {
  pub fn empty() -> Self {
    Set::Finite(HashSet::default())
  }

  pub fn of_one(t: T) -> Self {
    Set::Finite([t].into_iter().collect())
  }

  pub fn union(&self, other: &Self) -> Self {
    match (self, other) {
      (Set::Finite(a), Set::Finite(b)) => Set::Finite(chain!(a, b).cloned().collect()),
      _ => Set::Infinite,
    }
  }

  pub fn intersection(&self, other: &Self) -> Self {
    match (self, other) {
      (Set::Finite(a), Set::Finite(b)) => Set::Finite(a.intersection(b).cloned().collect()),
      (Set::Finite(a), Set::Infinite) => Set::Finite(a.clone()),
      (Set::Infinite, Set::Finite(b)) => Set::Finite(b.clone()),
      (Set::Infinite, Set::Infinite) => Set::Infinite,
    }
  }

  pub fn difference(&self, other: &Self) -> Self {
    match (self, other) {
      (Set::Finite(a), Set::Finite(b)) => Set::Finite(a.difference(b).cloned().collect()),
      (Set::Finite(_), Set::Infinite) => Set::Finite(HashSet::default()),
      (Set::Infinite, Set::Finite(_)) => Set::Finite(HashSet::default()),
      (Set::Infinite, Set::Infinite) => Set::Finite(HashSet::default()),
    }
  }

  pub fn len(&self) -> usize {
    match self {
      Set::Finite(s) => s.len(),
      Set::Infinite => usize::MAX,
    }
  }
}

impl<T: Clone + Eq + Hash> Default for Set<T> {
  fn default() -> Self {
    Set::Finite(HashSet::default())
  }
}

/// Describes where to seed a dataflow analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnalysisBoundary {
  /// Start from an existing CFG entry block.
  Entry(u32),
  /// Start from a synthetic exit that connects all terminal blocks (or sink SCCs
  /// when no terminals exist) to a single node.
  VirtualExit,
}

/// Boundary used for a particular analysis run, including synthetic nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedAnalysisBoundary {
  Entry(u32),
  VirtualExit { label: u32, predecessors: Vec<u32> },
}

impl ResolvedAnalysisBoundary {
  pub fn label(&self) -> u32 {
    match self {
      ResolvedAnalysisBoundary::Entry(label) => *label,
      ResolvedAnalysisBoundary::VirtualExit { label, .. } => *label,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalysisResult<T> {
  pub boundary: ResolvedAnalysisBoundary,
  pub states: HashMap<u32, T>,
}

pub trait DataFlowAnalysis<T: Eq, const FORWARDS: bool> {
  // Must be monotonic.
  fn transfer(&mut self, label: u32, block: &[Inst], in_: &T) -> T;
  fn join(&mut self, pred_outs: &[(u32, &T)]) -> T;
  fn analyze(&mut self, cfg: &Cfg, boundary: AnalysisBoundary) -> AnalysisResult<T> {
    let virtual_exit = match boundary {
      AnalysisBoundary::Entry(_) => None,
      AnalysisBoundary::VirtualExit => Some(calculate_virtual_exit(cfg)),
    };
    let resolved_boundary = match (&boundary, &virtual_exit) {
      (AnalysisBoundary::Entry(label), _) => ResolvedAnalysisBoundary::Entry(*label),
      (
        AnalysisBoundary::VirtualExit,
        Some(VirtualExit {
          label,
          predecessors,
        }),
      ) => ResolvedAnalysisBoundary::VirtualExit {
        label: *label,
        predecessors: predecessors.clone(),
      },
      _ => unreachable!("virtual exit must be calculated when requested"),
    };
    let virtual_exit_label = virtual_exit.as_ref().map(|v| v.label);
    let virtual_exit_predecessors = virtual_exit.as_ref().map(|v| v.predecessors.clone());
    let parents = |label: u32| -> Vec<u32> {
      if Some(label) == virtual_exit_label {
        virtual_exit_predecessors.clone().unwrap_or_default()
      } else {
        cfg.graph.parents_sorted(label)
      }
    };
    let children = |label: u32| -> Vec<u32> {
      if Some(label) == virtual_exit_label {
        Vec::new()
      } else {
        let mut nodes = cfg.graph.children_sorted(label);
        if let Some(preds) = &virtual_exit_predecessors {
          if preds.binary_search(&label).is_ok() {
            if let Some(exit) = virtual_exit_label {
              nodes.push(exit);
            }
          }
        }
        nodes.sort_unstable();
        nodes.dedup();
        nodes
      }
    };
    let related = |successors: bool, label: u32| -> Vec<u32> {
      match (FORWARDS, successors) {
        (true, true) => children(label),
        (true, false) => parents(label),
        (false, true) => parents(label),
        (false, false) => children(label),
      }
    };
    let mut outs = HashMap::<u32, T>::default();
    let mut worklist = VecDeque::from([resolved_boundary.label()]);
    while let Some(label) = worklist.pop_front() {
      let in_ = self.join(
        &related(false, label)
          .into_iter()
          .filter_map(|p| outs.get(&p).map(|out| (p, out)))
          .collect_vec(),
      );
      let out = self.transfer(
        label,
        if Some(label) == virtual_exit_label {
          &[]
        } else {
          cfg.bblocks.get(label)
        },
        &in_,
      );
      let did_change = outs.get(&label).is_none_or(|ex| ex != &out);
      outs.insert(label, out);
      if did_change {
        worklist.extend(related(true, label));
      };
    }
    AnalysisResult {
      boundary: resolved_boundary,
      states: outs,
    }
  }
}

#[derive(Clone, Debug)]
struct VirtualExit {
  label: u32,
  predecessors: Vec<u32>,
}

fn calculate_virtual_exit(cfg: &Cfg) -> VirtualExit {
  // Connect the virtual exit to every natural exit, or to every node in a sink
  // SCC if the graph has no terminal nodes (e.g. infinite loops).
  let predecessors = {
    let mut terminals = cfg
      .graph
      .labels()
      .filter(|&l| cfg.graph.children(l).next().is_none())
      .collect_vec();
    terminals.sort_unstable();
    if !terminals.is_empty() {
      terminals
    } else {
      sink_scc_nodes(cfg)
    }
  };
  VirtualExit {
    label: next_unused_label(cfg),
    predecessors,
  }
}

fn next_unused_label(cfg: &Cfg) -> u32 {
  let used: HashSet<u32> = cfg.graph.labels().collect();
  let candidate = used.iter().copied().max().unwrap_or(0).saturating_add(1);
  if !used.contains(&candidate) {
    return candidate;
  }
  let mut candidate = 0u32;
  loop {
    if !used.contains(&candidate) {
      return candidate;
    }
    candidate = candidate.wrapping_add(1);
    if candidate == 0 {
      break;
    }
  }
  panic!("exhausted all possible CFG labels while searching for a virtual exit");
}

fn sink_scc_nodes(cfg: &Cfg) -> Vec<u32> {
  let mut index: u32 = 0;
  let mut indices = HashMap::<u32, u32>::default();
  let mut lowlinks = HashMap::<u32, u32>::default();
  let mut stack = Vec::<u32>::new();
  let mut on_stack = HashSet::<u32>::default();
  let mut components = Vec::<Vec<u32>>::new();

  fn strongconnect(
    cfg: &Cfg,
    v: u32,
    index: &mut u32,
    indices: &mut HashMap<u32, u32>,
    lowlinks: &mut HashMap<u32, u32>,
    stack: &mut Vec<u32>,
    on_stack: &mut HashSet<u32>,
    components: &mut Vec<Vec<u32>>,
  ) {
    indices.insert(v, *index);
    lowlinks.insert(v, *index);
    *index += 1;
    stack.push(v);
    on_stack.insert(v);

    let mut neighbors = cfg.graph.children(v).collect_vec();
    neighbors.sort_unstable();
    for w in neighbors {
      if !indices.contains_key(&w) {
        strongconnect(
          cfg, w, index, indices, lowlinks, stack, on_stack, components,
        );
        let lowlink = *lowlinks.get(&v).unwrap();
        let neighbor_lowlink = *lowlinks.get(&w).unwrap();
        if lowlink > neighbor_lowlink {
          lowlinks.insert(v, neighbor_lowlink);
        }
      } else if on_stack.contains(&w) {
        let lowlink = *lowlinks.get(&v).unwrap();
        let neighbor_index = *indices.get(&w).unwrap();
        if lowlink > neighbor_index {
          lowlinks.insert(v, neighbor_index);
        }
      }
    }

    if lowlinks.get(&v) == indices.get(&v) {
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

  let mut nodes = cfg.graph.labels().collect_vec();
  nodes.sort_unstable();
  for node in nodes {
    if !indices.contains_key(&node) {
      strongconnect(
        cfg,
        node,
        &mut index,
        &mut indices,
        &mut lowlinks,
        &mut stack,
        &mut on_stack,
        &mut components,
      );
    }
  }

  let node_to_component = components
    .iter()
    .enumerate()
    .flat_map(|(i, comp)| comp.iter().map(move |&node| (node, i)))
    .collect::<HashMap<_, _>>();
  let mut is_sink_component = vec![true; components.len()];
  for (&node, &component) in node_to_component.iter() {
    for succ in cfg.graph.children(node) {
      if node_to_component[&succ] != component {
        is_sink_component[component] = false;
        break;
      }
    }
  }

  let mut sink_nodes = components
    .into_iter()
    .enumerate()
    .filter(|(i, _)| is_sink_component[*i])
    .flat_map(|(_, comp)| comp.into_iter())
    .collect_vec();
  sink_nodes.sort_unstable();
  sink_nodes
}
