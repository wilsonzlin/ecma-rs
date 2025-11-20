use crate::cfg::cfg::Cfg;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;

// Find which bblocks assign to what vars.
pub fn calculate_defs(cfg: &Cfg) -> HashMap<u32, HashSet<u32>> {
  let mut defs = HashMap::<u32, HashSet<u32>>::new();
  for (label, bblock) in cfg.bblocks.all() {
    for inst in bblock.iter() {
      for &var in inst.tgts.iter() {
        defs.entry(var).or_default().insert(label);
      }
    }
  }
  defs
}
