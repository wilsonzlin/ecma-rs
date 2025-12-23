use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::il::inst::Arg;
use crate::il::inst::InstTyp;
use crate::util::counter::Counter;
use ahash::HashMap;
use ahash::HashMapExt;
use itertools::Itertools;

fn inner(
  rename_stacks: &mut HashMap<u32, Vec<u32>>,
  cfg: &mut Cfg,
  phi_orig_tgts: &HashMap<(u32, usize), u32>,
  dom: &Dom,
  label: u32,
  c_temp: &mut Counter,
) {
  let mut to_pop = HashMap::<u32, usize>::new();

  // Replace arguments and targets in instructions.
  for inst in cfg.bblocks.get_mut(label).iter_mut() {
    if inst.t != InstTyp::Phi {
      for arg in inst.args.iter_mut() {
        if let Some(tgt) = arg.maybe_var() {
          let new_arg = Arg::Var(*rename_stacks.get(&tgt).unwrap().last().unwrap());
          *arg = new_arg;
        };
      }
    };
    for var in inst.tgts.iter_mut() {
      let new_var = c_temp.bump();
      rename_stacks.entry(*var).or_default().push(new_var);
      *to_pop.entry(*var).or_default() += 1;
      *var = new_var;
    }
  }

  let mut children = cfg.graph.children(label).collect_vec();
  children.sort_unstable();
  for s in children {
    for (inst_no, inst) in cfg.bblocks.get_mut(s).iter_mut().enumerate() {
      if inst.t != InstTyp::Phi {
        // No more phi nodes.
        break;
      };
      let orig_tgt = phi_orig_tgts[&(s, inst_no)];
      let Some(&new_tgt) = rename_stacks.get(&orig_tgt).and_then(|s| s.last()) else {
        // TODO Delete phi now?
        continue;
      };
      inst.insert_phi(label, Arg::Var(new_tgt));
    }
  }

  for c in dom.immediately_dominated_by(label) {
    inner(rename_stacks, cfg, phi_orig_tgts, dom, c, c_temp);
  }

  for (tgt, cnt) in to_pop {
    let s = rename_stacks.get_mut(&tgt).unwrap();
    for _ in 0..cnt {
      s.pop().unwrap();
    }
  }
}

pub fn rename_targets_for_ssa_construction(cfg: &mut Cfg, dom: &Dom, c_temp: &mut Counter) {
  // Store the original `tgt` field values from all Inst::Phi.
  let mut phi_orig_tgts = HashMap::<(u32, usize), u32>::new();
  for (label, bblock) in cfg.bblocks.all() {
    for (inst_no, inst) in bblock.iter().enumerate() {
      if inst.t != InstTyp::Phi {
        // No more Phi insts.
        break;
      };
      let tgt = inst.tgts[0];
      assert!(phi_orig_tgts.insert((label, inst_no), tgt).is_none());
    }
  }

  let mut rename_stacks = HashMap::<u32, Vec<u32>>::new();
  inner(&mut rename_stacks, cfg, &phi_orig_tgts, dom, 0, c_temp);
  // Prune phi nodes.
  // WARNING: It's not logically correct to do this during the previous rename processing at any time.
  // TODO Do we need to replace usages of these pruned phi nodes?
  for (_, bblock) in cfg.bblocks.all_mut() {
    let mut to_delete = Vec::new();
    for (i, inst) in bblock.iter().enumerate() {
      if inst.t != InstTyp::Phi {
        // No more phi nodes.
        break;
      };
      // TODO Why is it possible for there to be exactly one entry? What does that mean? How does that happen?
      if inst.labels.len() <= 1 {
        to_delete.push(i);
      };
    }
    for &i in to_delete.iter().rev() {
      bblock.remove(i);
    }
  }
}
