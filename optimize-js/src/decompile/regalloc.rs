use crate::analysis::interference::calculate_interference_graph;
use crate::analysis::liveness::calculate_live_ins;
use crate::analysis::registers::allocate_registers;
use crate::analysis::single_use_insts::analyse_single_use_defs;
use crate::cfg::cfg::Cfg;
use crate::il::inst::Arg;
use ahash::{HashMap, HashSet, RandomState};

#[derive(Debug, Clone)]
pub struct RegAlloc {
  pub temp_to_reg: HashMap<u32, u32>,
  pub reg_count: u32,
  pub inlines: HashMap<(u32, usize), (u32, usize)>,
  pub inlined_temps: HashSet<u32>,
}

fn collect_temps(cfg: &Cfg, inlined_temps: &HashSet<u32>) -> Vec<u32> {
  let mut temps = HashSet::<u32>::default();
  let mut labels: Vec<_> = cfg.bblocks.all().map(|(label, _)| label).collect();
  labels.sort_unstable();
  for label in labels {
    for inst in cfg.bblocks.get(label) {
      for &tgt in inst.tgts.iter() {
        if !inlined_temps.contains(&tgt) {
          temps.insert(tgt);
        }
      }
      for arg in inst.args.iter() {
        if let Arg::Var(t) = arg {
          if !inlined_temps.contains(t) {
            temps.insert(*t);
          }
        }
      }
    }
  }
  let mut temps: Vec<_> = temps.into_iter().collect();
  temps.sort_unstable();
  temps
}

fn determinize_intgraph(intgraph: HashMap<u32, HashSet<u32>>) -> HashMap<u32, HashSet<u32>> {
  let mut nodes: Vec<_> = intgraph.keys().copied().collect();
  nodes.sort_unstable();
  let mut deterministic = HashMap::with_hasher(RandomState::with_seeds(0, 0, 0, 0));
  for node in nodes {
    let mut neighbours: Vec<_> = intgraph.get(&node).unwrap().iter().copied().collect();
    neighbours.sort_unstable();
    let mut set = HashSet::with_hasher(RandomState::with_seeds(0, 0, 0, 0));
    set.extend(neighbours);
    deterministic.insert(node, set);
  }
  deterministic
}

fn normalise_registers(
  alloc: HashMap<u32, u32>,
  inlined_temps: &HashSet<u32>,
) -> (HashMap<u32, u32>, u32) {
  let mut ordered: Vec<_> = alloc
    .into_iter()
    .filter(|(temp, _)| !inlined_temps.contains(temp))
    .collect();
  ordered.sort_unstable_by_key(|(temp, _)| *temp);

  let mut reg_remap = HashMap::with_hasher(RandomState::with_seeds(0, 0, 0, 0));
  let mut next_reg = 0u32;
  for (_, reg) in ordered.iter() {
    reg_remap.entry(*reg).or_insert_with(|| {
      let r = next_reg;
      next_reg += 1;
      r
    });
  }

  let mut temp_to_reg = HashMap::with_hasher(RandomState::with_seeds(0, 0, 0, 0));
  for (temp, reg) in ordered.into_iter() {
    let mapped = *reg_remap.get(&reg).unwrap();
    temp_to_reg.insert(temp, mapped);
  }
  (temp_to_reg, next_reg)
}

pub fn compute_regalloc(cfg: &Cfg) -> RegAlloc {
  let (inlines, inlined_temps) = analyse_single_use_defs(cfg);
  let live_ins = calculate_live_ins(cfg, &inlines, &inlined_temps);
  let mut intgraph = calculate_interference_graph(&live_ins);

  for temp in collect_temps(cfg, &inlined_temps) {
    intgraph.entry(temp).or_default();
  }

  let intgraph = determinize_intgraph(intgraph);
  let (temp_to_reg, reg_count) = normalise_registers(allocate_registers(&intgraph), &inlined_temps);

  RegAlloc {
    temp_to_reg,
    reg_count,
    inlines,
    inlined_temps,
  }
}
