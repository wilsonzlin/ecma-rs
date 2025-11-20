use crate::cfg::cfg::Cfg;
use crate::il::inst::Arg;
use crate::il::inst::InstTyp;
use ahash::HashMap;
use ahash::HashSet;
use ahash::HashSetExt;

pub fn optpass_trivial_dce(changed: &mut bool, cfg: &mut Cfg) {
  let mut used = HashSet::new();
  for (_, bblock) in cfg.bblocks.all() {
    for inst in bblock.iter() {
      for arg in inst.args.iter() {
        let Arg::Var(t) = arg else {
          continue;
        };
        used.insert(*t);
      }
    }
  }
  for (_, bblock) in cfg.bblocks.all_mut() {
    for i in (0..bblock.len()).rev() {
      // We should delete if all targets are unused. (There should only ever be zero or one targets.)
      let should_delete =
        !bblock[i].tgts.is_empty() && bblock[i].tgts.iter().all(|var| !used.contains(var));
      if should_delete {
        if bblock[i].t == InstTyp::Call {
          // We pessimistically assume all functions are non-pure and therefore cannot be removed. Therefore, we can only remove the target.
          bblock[i].tgts.clear();
        } else {
          bblock.remove(i);
        };
        *changed = true;
      };
    }
  }
}
