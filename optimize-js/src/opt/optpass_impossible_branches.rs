use crate::cfg::cfg::Cfg;
use crate::eval::consteval::coerce_to_bool;
use crate::il::inst::Arg;
use crate::il::inst::InstTyp;
use crate::opt::PassResult;
use crate::ssa::phi_simplify::simplify_phis;
use itertools::Itertools;

// Correctness:
// - When we detach bblocks A and B (because A can never branch to B in reality e.g. const eval is always true/false), we move all bblocks in subgraph G, which contains all bblocks only reachable from B.
// - We must then detach all bblocks within G i.e. remove all edges to bblocks outside of G. This isn't recursive, as the bblocks only reachable from B doesn't change as we remove these bblocks or their edges.
// - We must clean up any usages of defs within G outside of G. Outside of G, these uses can only appear in Phi nodes.
pub fn optpass_impossible_branches(cfg: &mut Cfg) -> PassResult {
  let mut result = PassResult::default();
  loop {
    let mut iteration_changed = false;
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
        result.mark_changed();
        iteration_changed = true;
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
      result.mark_cfg_changed();
      iteration_changed = true;
    }

    // Detaching bblocks means that we may have removed entire subgraphs (i.e. its descendants). Therefore, we must recalculate again the accessible bblocks.
    // NOTE: We cannot delete now, as we need to access the children of these deleted nodes first. (They won't have children after deleting.)
    let mut to_delete = cfg.graph.find_unreachable(cfg.entry).collect_vec();
    to_delete.sort_unstable();

    // Delete bblocks now so that only valid bblocks remain, which is the set of bblocks to iterate for pruning Phi insts.
    let did_delete = !to_delete.is_empty();
    cfg.graph.delete_many(to_delete.clone());
    cfg.bblocks.remove_many(to_delete);
    if did_delete {
      result.mark_cfg_changed();
      iteration_changed = true;
    }

    if simplify_phis(cfg) {
      result.mark_changed();
      iteration_changed = true;
    }

    #[cfg(debug_assertions)]
    {
      crate::ssa::phi_simplify::validate_phis(cfg)
        .expect("phi validation failed after impossible branches");
    }

    if !iteration_changed {
      break;
    }
    result.mark_changed();
  }
  result
}
