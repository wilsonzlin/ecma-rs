use crate::cfg::cfg::Cfg;
use crate::il::inst::Inst;
use ahash::{HashMap, HashSet};
use itertools::Itertools;
use std::collections::VecDeque;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
  Forward,
  Backward,
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
pub struct BlockState<T> {
  pub entry: T,
  pub exit: T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataFlowResult<T> {
  pub boundary: ResolvedAnalysisBoundary,
  pub blocks: HashMap<u32, BlockState<T>>,
}

pub trait DataFlowAnalysis {
  type State: Clone + Eq;

  const DIRECTION: Direction;

  /// The bottom element for the lattice of [`Self::State`].
  fn bottom(&self, cfg: &Cfg) -> Self::State;

  /// Provide the initial state for the boundary node. Defaults to bottom.
  fn boundary_state(&self, boundary: &ResolvedAnalysisBoundary, cfg: &Cfg) -> Self::State {
    let _ = (boundary, cfg);
    self.bottom(cfg)
  }

  /// Combine states flowing into a block.
  fn meet(&mut self, states: &[(u32, &Self::State)]) -> Self::State;

  /// Instruction-level transfer function. Implementations should mutate
  /// `state` in-place to reflect the state that flows past `inst` in the
  /// analysis direction.
  fn apply_to_instruction(
    &mut self,
    label: u32,
    inst_idx: usize,
    inst: &Inst,
    state: &mut Self::State,
  );

  /// Block-level transfer function derived from instruction-level transfers.
  fn apply_to_block(&mut self, label: u32, block: &[Inst], state: &Self::State) -> Self::State {
    let mut next = state.clone();
    match Self::DIRECTION {
      Direction::Forward => {
        for (idx, inst) in block.iter().enumerate() {
          self.apply_to_instruction(label, idx, inst, &mut next);
        }
      }
      Direction::Backward => {
        for (idx, inst) in block.iter().enumerate().rev() {
          self.apply_to_instruction(label, idx, inst, &mut next);
        }
      }
    }
    next
  }

  fn analyze(&mut self, cfg: &Cfg, boundary: AnalysisBoundary) -> DataFlowResult<Self::State>
  where
    Self: Sized,
  {
    run_dataflow(self, cfg, boundary)
  }
}

fn run_dataflow<A: DataFlowAnalysis>(
  analysis: &mut A,
  cfg: &Cfg,
  boundary: AnalysisBoundary,
) -> DataFlowResult<A::State> {
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
  let flow_graph = FlowGraph::new(cfg, A::DIRECTION, virtual_exit);

  let bottom = analysis.bottom(cfg);
  let mut blocks = HashMap::<u32, BlockState<A::State>>::default();
  for label in flow_graph.labels() {
    blocks.insert(
      label,
      BlockState {
        entry: bottom.clone(),
        exit: bottom.clone(),
      },
    );
  }

  let boundary_label = resolved_boundary.label();
  let boundary_state = analysis.boundary_state(&resolved_boundary, cfg);
  let mut worklist = VecDeque::from([boundary_label]);
  let mut queued = HashSet::from_iter([boundary_label]);
  while let Some(label) = worklist.pop_front() {
    queued.remove(&label);
    let incoming = if label == boundary_label {
      boundary_state.clone()
    } else {
      let merged_inputs = flow_graph
        .predecessors(label)
        .into_iter()
        .map(|pred| match A::DIRECTION {
          Direction::Forward => (pred, &blocks[&pred].exit),
          Direction::Backward => (pred, &blocks[&pred].entry),
        })
        .collect_vec();
      analysis.meet(&merged_inputs)
    };

    let block = flow_graph.block(label);
    let (entry, exit) = match A::DIRECTION {
      Direction::Forward => {
        let exit = analysis.apply_to_block(label, block, &incoming);
        (incoming, exit)
      }
      Direction::Backward => {
        let entry = analysis.apply_to_block(label, block, &incoming);
        (entry, incoming)
      }
    };

    let block_state = blocks.get_mut(&label).unwrap();
    if block_state.entry != entry || block_state.exit != exit {
      *block_state = BlockState { entry, exit };
      for succ in flow_graph.successors(label) {
        if queued.insert(succ) {
          worklist.push_back(succ);
        }
      }
    }
  }

  DataFlowResult {
    boundary: resolved_boundary,
    blocks,
  }
}

#[derive(Clone, Debug)]
struct VirtualExit {
  label: u32,
  predecessors: Vec<u32>,
}

struct FlowGraph<'cfg> {
  cfg: &'cfg Cfg,
  direction: Direction,
  virtual_exit: Option<VirtualExit>,
}

impl<'cfg> FlowGraph<'cfg> {
  fn new(cfg: &'cfg Cfg, direction: Direction, virtual_exit: Option<VirtualExit>) -> Self {
    Self {
      cfg,
      direction,
      virtual_exit,
    }
  }

  fn labels(&self) -> Vec<u32> {
    let mut labels = self.cfg.graph.labels_sorted();
    labels.extend(self.cfg.bblocks.all().map(|(label, _)| label));
    if let Some(VirtualExit { label, .. }) = self.virtual_exit {
      labels.push(label);
    }
    labels.sort_unstable();
    labels.dedup();
    labels
  }

  fn block(&self, label: u32) -> &[Inst] {
    if Some(label) == self.virtual_exit_label() {
      &[]
    } else {
      self.cfg.bblocks.get(label)
    }
  }

  fn virtual_exit_label(&self) -> Option<u32> {
    self.virtual_exit.as_ref().map(|v| v.label)
  }

  fn predecessors(&self, label: u32) -> Vec<u32> {
    if Some(label) == self.virtual_exit_label() {
      return Vec::new();
    }
    let mut nodes = match self.direction {
      Direction::Forward => self.cfg.graph.parents_sorted(label),
      Direction::Backward => self.cfg.graph.children_sorted(label),
    };
    if self.direction == Direction::Backward {
      if let Some(exit) = &self.virtual_exit {
        if exit.predecessors.binary_search(&label).is_ok() {
          nodes.push(exit.label);
        }
      }
    }
    nodes.sort_unstable();
    nodes.dedup();
    nodes
  }

  fn successors(&self, label: u32) -> Vec<u32> {
    if Some(label) == self.virtual_exit_label() {
      return match (&self.direction, &self.virtual_exit) {
        (Direction::Forward, _) => Vec::new(),
        (Direction::Backward, Some(exit)) => exit.predecessors.clone(),
        (Direction::Backward, None) => unreachable!("missing virtual exit"),
      };
    }

    let mut nodes = match self.direction {
      Direction::Forward => self.cfg.graph.children_sorted(label),
      Direction::Backward => self.cfg.graph.parents_sorted(label),
    };
    if self.direction == Direction::Forward {
      if let Some(exit) = &self.virtual_exit {
        if exit.predecessors.binary_search(&label).is_ok() {
          nodes.push(exit.label);
        }
      }
    }
    nodes.sort_unstable();
    nodes.dedup();
    nodes
  }
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
