use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::il::inst::Arg;
use crate::il::inst::Const;
use crate::il::inst::InstTyp;
use crate::util::counter::Counter;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;

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
          let stack = rename_stacks.entry(tgt).or_default();
          if stack.is_empty() {
            stack.push(tgt);
          }
          let new_arg = Arg::Var(*stack.last().unwrap());
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

  for s in cfg.graph.children_sorted(label) {
    for (inst_no, inst) in cfg.bblocks.get_mut(s).iter_mut().enumerate() {
      if inst.t != InstTyp::Phi {
        // No more phi nodes.
        break;
      };
      let orig_tgt = phi_orig_tgts[&(s, inst_no)];
      // If we haven't seen a definition of this variable along this path, use the original
      // pre-SSA variable as the incoming value so every predecessor contributes exactly one
      // argument.
      let stack = rename_stacks.entry(orig_tgt).or_default();
      if stack.is_empty() {
        stack.push(orig_tgt);
      }
      inst.insert_phi(label, Arg::Var(*stack.last().unwrap()));
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

fn resolve_replacement(arg: &Arg, replacements: &HashMap<u32, Arg>) -> Arg {
  match arg {
    Arg::Var(v) => {
      let mut current = *v;
      let mut seen = HashSet::default();
      loop {
        if !seen.insert(current) {
          // Cycle; bail out with the last seen variable.
          return Arg::Var(current);
        }
        let Some(next) = replacements.get(&current) else {
          return Arg::Var(current);
        };
        match next {
          Arg::Var(next_v) => current = *next_v,
          other => return other.clone(),
        }
      }
    }
    _ => arg.clone(),
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
  // Prune phi nodes that no longer need to exist and rewrite all uses of their targets to the
  // surviving incoming value to avoid dangling SSA variables.
  let mut replacements = HashMap::<u32, Arg>::new();
  for (label, bblock) in cfg.bblocks.all_mut() {
    let mut i = 0;
    while i < bblock.len() {
      if bblock[i].t != InstTyp::Phi {
        break;
      }
      let inst = &mut bblock[i];
      #[cfg(debug_assertions)]
      let parents = cfg.graph.parents_sorted(label);
      debug_assert!(
        inst.labels.len() == parents.len() || inst.labels.len() <= 1,
        "phi node at block {label} expected one incoming per parent {:?}, got {:?}",
        parents,
        inst.labels
      );
      if inst.labels.len() <= 1 {
        let tgt = inst.tgts[0];
        let replacement = inst
          .args
          .get(0)
          .cloned()
          .unwrap_or(Arg::Const(Const::Undefined));
        replacements.insert(tgt, replacement);
        bblock.remove(i);
        continue;
      }
      i += 1;
    }
  }
  if !replacements.is_empty() {
    for (_, bblock) in cfg.bblocks.all_mut() {
      for inst in bblock.iter_mut() {
        for arg in inst.args.iter_mut() {
          *arg = resolve_replacement(arg, &replacements);
        }
      }
    }
  }
}
