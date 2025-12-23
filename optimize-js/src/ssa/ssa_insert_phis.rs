use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::il::inst::Inst;
use ahash::HashMap;
use ahash::HashSet;
use itertools::Itertools;
use std::collections::VecDeque;

pub fn insert_phis_for_ssa_construction(
  defs: &mut HashMap<u32, HashSet<u32>>,
  cfg: &mut Cfg,
  dom: &Dom,
) {
  let domfront = dom.dominance_frontiers(cfg);
  let mut vars = defs.keys().cloned().collect_vec();
  vars.sort_unstable();
  for v in vars {
    let mut already_inserted = HashSet::default();
    // We'll start with these blocks but add more as we process, so we can't just use `defs[v].iter()`.
    let mut queue_items: Vec<_> = defs[&v].iter().copied().collect();
    queue_items.sort_unstable();
    let mut q = VecDeque::from(queue_items);
    let mut seen = HashSet::from_iter(q.clone());
    while let Some(d) = q.pop_front() {
      // Look at the blocks in the dominance frontier for block `d`.
      let Some(blocks) = domfront.get(&d) else {
        continue;
      };
      let mut labels: Vec<_> = blocks.iter().copied().collect();
      labels.sort_unstable();
      for label in labels {
        if already_inserted.contains(&label) {
          continue;
        };
        already_inserted.insert(label);
        // We'll populate this new Phi inst later.
        cfg.bblocks.get_mut(label).insert(0, Inst::phi_empty(v));
        defs.get_mut(&v).unwrap().insert(label);
        if seen.insert(label) {
          q.push_back(label);
        };
      }
    }
  }
}
