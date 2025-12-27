use crate::analysis::dataflow::{AnalysisBoundary, DataFlowAnalysis, Direction};
use crate::cfg::cfg::Cfg;
use crate::il::inst::{Arg, Inst};
use ahash::{HashMap, HashSet};

#[derive(Clone, PartialEq, Eq)]
struct BitSet {
  bits: Vec<u64>,
}

impl BitSet {
  fn new(size: usize) -> Self {
    Self {
      bits: vec![0; (size.saturating_add(63)) / 64],
    }
  }

  fn insert(&mut self, idx: usize) {
    let (word, bit) = Self::word_bit(idx);
    self.bits[word] |= 1u64 << bit;
  }

  fn remove(&mut self, idx: usize) {
    let (word, bit) = Self::word_bit(idx);
    self.bits[word] &= !(1u64 << bit);
  }

  fn union_with(&mut self, other: &Self) {
    debug_assert_eq!(self.bits.len(), other.bits.len());
    for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
      *a |= *b;
    }
  }

  fn iter_indices(&self) -> impl Iterator<Item = usize> + '_ {
    self
      .bits
      .iter()
      .enumerate()
      .flat_map(|(word_idx, word)| Self::iter_word(*word).map(move |bit| word_idx * 64 + bit))
  }

  fn iter_word(mut word: u64) -> impl Iterator<Item = usize> {
    std::iter::from_fn(move || {
      if word == 0 {
        return None;
      }
      let bit = word.trailing_zeros() as usize;
      word &= word - 1;
      Some(bit)
    })
  }

  const fn word_bit(idx: usize) -> (usize, usize) {
    (idx / 64, idx % 64)
  }
}

struct LivenessAnalysis {
  additional_uses: HashMap<(u32, usize), BitSet>,
  inlined_insts: HashSet<(u32, usize)>,
  var_to_bit: HashMap<u32, usize>,
  bit_to_var: Vec<u32>,
  width: usize,
}

impl LivenessAnalysis {
  fn new(
    cfg: &Cfg,
    inlines: &HashMap<(u32, usize), (u32, usize)>,
    inlined_vars: &HashSet<u32>,
  ) -> Self {
    let inlined_insts = inlines.keys().copied().collect();
    let additional_use_vars = compute_additional_use_vars(cfg, inlines, inlined_vars);
    let mut all_vars = collect_tracked_vars(cfg, &inlined_insts, inlined_vars);
    for vars in additional_use_vars.values() {
      all_vars.extend(vars.iter().copied());
    }
    let mut bit_to_var: Vec<u32> = all_vars.into_iter().collect();
    bit_to_var.sort_unstable();
    let var_to_bit: HashMap<u32, usize> = bit_to_var
      .iter()
      .enumerate()
      .map(|(idx, var)| (*var, idx))
      .collect();
    let width = bit_to_var.len();
    let mut additional_uses = HashMap::default();
    for (loc, vars) in additional_use_vars {
      let mut bits = BitSet::new(width);
      for var in vars {
        if let Some(idx) = var_to_bit.get(&var) {
          bits.insert(*idx);
        }
      }
      additional_uses.insert(loc, bits);
    }
    Self {
      additional_uses,
      inlined_insts,
      var_to_bit,
      bit_to_var,
      width,
    }
  }

  fn bitset_to_vars(&self, bits: &BitSet) -> HashSet<u32> {
    let mut vars = HashSet::default();
    for idx in bits.iter_indices() {
      if let Some(var) = self.bit_to_var.get(idx) {
        vars.insert(*var);
      }
    }
    vars
  }
}

impl DataFlowAnalysis for LivenessAnalysis {
  type State = BitSet;

  const DIRECTION: Direction = Direction::Backward;

  fn bottom(&self, _cfg: &Cfg) -> Self::State {
    BitSet::new(self.width)
  }

  fn meet(&mut self, states: &[(u32, &Self::State)]) -> Self::State {
    let mut merged = BitSet::new(self.width);
    for (_, state) in states {
      merged.union_with(state);
    }
    merged
  }

  fn apply_to_instruction(
    &mut self,
    label: u32,
    inst_idx: usize,
    inst: &Inst,
    state: &mut Self::State,
  ) {
    if self.inlined_insts.contains(&(label, inst_idx)) {
      return;
    }
    for &var in inst.tgts.iter() {
      if let Some(idx) = self.var_to_bit.get(&var) {
        state.remove(*idx);
      }
    }
    for arg in inst.args.iter() {
      if let Arg::Var(var) = arg {
        if let Some(idx) = self.var_to_bit.get(var) {
          state.insert(*idx);
        }
      }
    }
    if let Some(additional) = self.additional_uses.get(&(label, inst_idx)) {
      state.union_with(additional);
    }
  }
}

fn compute_additional_use_vars(
  cfg: &Cfg,
  inlines: &HashMap<(u32, usize), (u32, usize)>,
  inlined_vars: &HashSet<u32>,
) -> HashMap<(u32, usize), HashSet<u32>> {
  let mut additional: HashMap<(u32, usize), HashSet<u32>> = HashMap::default();
  let mut inline_edges: Vec<_> = inlines.iter().collect();
  inline_edges.sort_by_key(|(src, dest)| (*src, *dest));
  for (src, next) in inline_edges {
    let mut dest = *next;
    while let Some(next) = inlines.get(&dest) {
      dest = *next;
    }
    for arg in cfg.bblocks.get(src.0)[src.1].args.iter() {
      if let Arg::Var(var) = arg {
        if !inlined_vars.contains(var) {
          additional.entry(dest).or_default().insert(*var);
        }
      }
    }
  }
  additional
}

fn collect_tracked_vars(
  cfg: &Cfg,
  inlined_insts: &HashSet<(u32, usize)>,
  inlined_vars: &HashSet<u32>,
) -> HashSet<u32> {
  let mut vars = HashSet::default();
  for (label, block) in cfg.bblocks.all() {
    for (idx, inst) in block.iter().enumerate() {
      if inlined_insts.contains(&(label, idx)) {
        continue;
      }
      for &tgt in inst.tgts.iter() {
        if !inlined_vars.contains(&tgt) {
          vars.insert(tgt);
        }
      }
      for arg in inst.args.iter() {
        if let Arg::Var(var) = arg {
          if !inlined_vars.contains(var) {
            vars.insert(*var);
          }
        }
      }
    }
  }
  vars
}

pub fn calculate_live_ins(
  cfg: &Cfg,
  inlines: &HashMap<(u32, usize), (u32, usize)>,
  inlined_vars: &HashSet<u32>,
) -> HashMap<(u32, usize), HashSet<u32>> {
  let mut analysis = LivenessAnalysis::new(cfg, inlines, inlined_vars);
  let result = analysis.analyze(cfg, AnalysisBoundary::VirtualExit);

  let mut live_ins = HashMap::default();
  for label in cfg.graph.labels_sorted() {
    let mut state = result
      .blocks
      .get(&label)
      .map(|b| b.exit.clone())
      .unwrap_or_else(|| analysis.bottom(cfg));
    for (inst_idx, inst) in cfg.bblocks.get(label).iter().enumerate().rev() {
      if analysis.inlined_insts.contains(&(label, inst_idx)) {
        continue;
      }
      analysis.apply_to_instruction(label, inst_idx, inst, &mut state);
      live_ins.insert((label, inst_idx), analysis.bitset_to_vars(&state));
    }
  }
  live_ins
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};

  fn cfg_with_blocks(blocks: &[(u32, Vec<Inst>)], edges: &[(u32, u32)]) -> Cfg {
    let labels: Vec<u32> = blocks.iter().map(|(label, _)| *label).collect();
    let mut graph = CfgGraph::default();
    for &(from, to) in edges {
      graph.connect(from, to);
    }
    for &label in &labels {
      if !graph.contains(label) {
        graph.connect(label, label);
        graph.disconnect(label, label);
      }
    }
    let mut bblocks = CfgBBlocks::default();
    for (label, insts) in blocks.iter() {
      bblocks.add(*label, insts.clone());
    }
    Cfg {
      graph,
      bblocks,
      entry: 0,
    }
  }

  #[test]
  fn calculates_live_in_per_instruction() {
    let cfg = cfg_with_blocks(
      &[(
        0,
        vec![
          Inst::var_assign(0, Arg::Var(1)),
          Inst::var_assign(2, Arg::Var(0)),
        ],
      )],
      &[],
    );
    let live_ins = calculate_live_ins(&cfg, &HashMap::default(), &HashSet::default());
    assert_eq!(
      live_ins.get(&(0, 1)).cloned().unwrap_or_default(),
      HashSet::from_iter([0])
    );
    assert_eq!(
      live_ins.get(&(0, 0)).cloned().unwrap_or_default(),
      HashSet::from_iter([1])
    );
  }

  #[test]
  fn extends_uses_for_inlined_instructions() {
    let cfg = cfg_with_blocks(
      &[(
        0,
        vec![
          Inst::var_assign(0, Arg::Var(1)),
          Inst::var_assign(2, Arg::Var(0)),
        ],
      )],
      &[],
    );
    let inlines = HashMap::from_iter([((0, 0), (0, 1))]);
    let inlined_vars = HashSet::from_iter([0]);
    let live_ins = calculate_live_ins(&cfg, &inlines, &inlined_vars);
    assert_eq!(
      live_ins.get(&(0, 1)).cloned().unwrap_or_default(),
      HashSet::from_iter([1])
    );
    assert!(!live_ins.contains_key(&(0, 0)));
  }
}
