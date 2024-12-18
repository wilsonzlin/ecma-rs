use ahash::HashMap;
use ahash::HashMapExt;

use crate::cfg::cfg::Cfg;
use crate::il::inst::Arg;
use crate::il::inst::Inst;
use crate::il::inst::InstTyp;

// VarAssigns are always useless in strict SSA. However, dominator-based value numbering doesn't manage to detect and remove all such insts, with one reason being that DVNT only traverses domtree children.
// My theory for correctness:
// - Strict SSA requires all defs to dominate all their uses.
// - Targets are only assigned in one place globally.
pub fn optpass_redundant_assigns(changed: &mut bool, cfg: &mut Cfg) {
  let mut tgt_to_arg = HashMap::new();
  for (_, bblock) in cfg.bblocks.all_mut() {
    let mut to_delete = Vec::new();
    for (i, inst) in bblock.iter().enumerate() {
      if inst.t != InstTyp::VarAssign {
        continue;
      }
      let (tgt, value) = inst.as_var_assign();
      to_delete.push(i);
      assert!(tgt_to_arg.insert(tgt, value.clone()).is_none());
    }
    for i in to_delete.into_iter().rev() {
      bblock.remove(i);
      *changed = true;
    }
  }
  for (_, bblock) in cfg.bblocks.all_mut() {
    for inst in bblock.iter_mut() {
      for arg in inst.args.iter_mut() {
        let Arg::Var(t) = arg else {
          continue;
        };
        let Some(new_arg) = tgt_to_arg.get(t) else {
          continue;
        };
        *arg = new_arg.clone();
      };
    }
  }
}
