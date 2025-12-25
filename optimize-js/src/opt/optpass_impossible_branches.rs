use crate::cfg::cfg::Cfg;
use crate::eval::consteval::coerce_to_bool;
use crate::il::inst::Arg;
use crate::il::inst::Inst;
use crate::il::inst::InstTyp;
use itertools::Itertools;

// Correctness:
// - When we detach bblocks A and B (because A can never branch to B in reality e.g. const eval is always true/false), we move all bblocks in subgraph G, which contains all bblocks only reachable from B.
// - We must then detach all bblocks within G i.e. remove all edges to bblocks outside of G. This isn't recursive, as the bblocks only reachable from B doesn't change as we remove these bblocks or their edges.
// - We must clean up any usages of defs within G outside of G. Outside of G, these uses can only appear in Phi nodes.
pub fn optpass_impossible_branches(changed: &mut bool, cfg: &mut Cfg) {
  loop {
    for label in cfg.graph.labels_sorted() {
      let Some(inst) = cfg.bblocks.get_mut(label).last_mut() else {
        continue;
      };
      if inst.t != InstTyp::CondGoto {
        continue;
      };
      let (cond, true_label, false_label) = inst.as_cond_goto();
      if true_label == false_label {
        // Drop the CondGoto.
        // No need to update the graph, it's connected correctly, it's just a redundant inst.
        // TODO Should this optimization be part of optapss_impossible_branches?
        cfg.bblocks.get_mut(label).pop().unwrap();
        *changed = true;
        continue;
      }
      let Arg::Const(cond) = cond else {
        continue;
      };
      let never_child = if coerce_to_bool(cond) {
        false_label
      } else {
        true_label
      };
      // Drop CondGoto inst.
      cfg.bblocks.get_mut(label).pop().unwrap();
      // Detach from child.
      cfg.graph.disconnect(label, never_child);
      // Update Phi insts in child.
      // NOTE: This is not the same as the subsequent Phi pruning for each `to_delete`, as `never_child` may still reachable (e.g. CondGoto was for if-with-no-else stmt, and never_child was for after if stmt).
      for inst in cfg.bblocks.get_mut(never_child).iter_mut() {
        if inst.t != InstTyp::Phi {
          // No more Phi insts.
          break;
        };
        inst.remove_phi(label);
      }
      *changed = true;
    }

    // Detaching bblocks means that we may have removed entire subgraphs (i.e. its descendants). Therefore, we must recalculate again the accessible bblocks.
    // NOTE: We cannot delete now, as we need to access the children of these deleted nodes first. (They won't have children after deleting.)
    let mut to_delete = cfg.graph.find_unreachable().collect_vec();
    to_delete.sort_unstable();
    // All defs in now-deleted bblocks must be cleared. Since we are in strict SSA, they should only ever appear outside of the deleted bblocks in Phi insts.
    for &n in to_delete.iter() {
      // Update Phi insts in children.
      for c in cfg.graph.children_sorted(n) {
        for inst in cfg.bblocks.get_mut(c).iter_mut() {
          if inst.t != InstTyp::Phi {
            // No more Phi insts.
            break;
          };
          // NOTE: We don't try to remove the Phi insts or transform into a VarAssign (if it only has one entry in `from_blocks`) right now out of abundance of caution for correctness, since `from_blocks` could still be modified during these loops.
          inst.remove_phi(n);
        }
      }
    }

    // Delete bblocks now so that only valid bblocks remain, which is the set of bblocks to iterate for pruning Phi insts.
    let did_delete = !to_delete.is_empty();
    cfg.graph.delete_many(to_delete.clone());
    cfg.bblocks.remove_many(to_delete);

    // Prune Phi insts in remaining bblocks.
    for (_, bblock) in cfg.bblocks.all_mut() {
      let mut phis_to_delete = Vec::new();
      for (i, inst) in bblock.iter_mut().enumerate() {
        if inst.t != InstTyp::Phi {
          // No more Phi insts.
          break;
        };
        let tgt = inst.tgts[0];
        if inst.labels.is_empty() {
          // TODO Is this always safe?
          phis_to_delete.push(i);
        }
        if inst.labels.len() == 1 {
          let arg = inst.args[0].clone();
          *inst = Inst::var_assign(tgt, arg);
        };
      }
      for i in phis_to_delete.into_iter().rev() {
        bblock.remove(i);
      }
    }

    if !did_delete {
      break;
    }
    *changed = true;
  }
}
