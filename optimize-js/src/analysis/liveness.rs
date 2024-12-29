use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use std::collections::VecDeque;

use crate::cfg::cfg::Cfg;
use crate::il::inst::Arg;

// TODO Use DataFlowAnalysis
pub fn calculate_live_ins(
  cfg: &Cfg,
  inlines: &HashMap<(u32, usize), (u32, usize)>,
  inlined_vars: &HashSet<u32>,
) -> HashMap<(u32, usize), HashSet<u32>> {
  // Some preparation of inlines is required. If an inst is inlined, then that inst no longer has any lifetime at all, and its args' lifetimes get extended (because they move to a later inst). Insts may inline recursively, so follow the "chain" of inlining to find the ultimate inst that the arg lifetimes will be extended to.
  let mut additional_uses_at = HashMap::<(u32, usize), HashSet<u32>>::new();
  for (src, next) in inlines {
    let mut dest = next;
    while let Some(next) = inlines.get(dest) {
      dest = next;
    }
    for arg in cfg.bblocks.get(src.0)[src.1].args.iter() {
      if let Arg::Var(t) = arg {
        if !inlined_vars.contains(t) {
          additional_uses_at.entry(dest.clone()).or_default().insert(*t);
        }
      }
    }
  }

  // Worklist algorithm.
  let mut live_in_at = HashMap::<(u32, usize), HashSet<u32>>::new();
  // This is necessary as inst 0 may be inlined so won't exist in `live_in_at`.
  let mut live_in_at_top_of_bblock = HashMap::<u32, HashSet<u32>>::new();
  let mut worklist = cfg.graph.labels().collect::<VecDeque<_>>();
  while let Some(label) = worklist.pop_front() {
    let mut cur = cfg.graph.children(label)
      .filter_map(|c| live_in_at_top_of_bblock.get(&c))
      .cloned()
      .reduce(|r, p| r.union(&p).cloned().collect::<HashSet<_>>())
      .unwrap_or_default();
    // TODO We go inst by inst to avoid another loop to calculate each inst, but also because it may be possible to use before def if self-loop. Is the latter true?
    // WARNING: Remove def first, then add usages, in case args contains the same var (although this isn't possible when using SSA).
    let mut did_change = false;
    for (inst_no, inst) in cfg.bblocks.get(label).iter().enumerate().rev() {
      let loc = (label, inst_no);
      if inlines.contains_key(&loc) {
        // This inst has been inlined, pretend it doesn't exist (and don't add to `live_in_at`).
        continue;
      };
      for &var in inst.tgts.iter() {
        cur.remove(&var);
      }
      for arg in inst.args.iter() {
        if let &Arg::Var(t) = arg {
          cur.insert(t);
        }
      }
      if let Some(add_uses) = additional_uses_at.get(&loc) {
        // `add_uses` contains all other vars that will be in this inst after inlining.
        cur.extend(add_uses);
      };
      let ex = live_in_at.entry((label, inst_no)).or_default();
      if ex != &cur {
        *ex = cur.clone();
        did_change = true;
      };
    }
    live_in_at_top_of_bblock.insert(label, cur);
    if did_change {
      for p in cfg.graph.parents(label) {
        worklist.push_back(p);
      }
    };
  }
  live_in_at
}
