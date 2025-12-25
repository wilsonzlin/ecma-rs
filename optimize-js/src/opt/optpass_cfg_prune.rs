use crate::cfg::cfg::Cfg;
use crate::il::inst::InstTyp;
use itertools::Itertools;

/**
 * WARNING: Read comment in cfg.rs.
 */
fn can_prune_bblock(
  parents: &[u32],
  children: &[u32],
  is_only_child_of_all_parents: bool,
  is_empty: bool,
) -> bool {
  // If we're the only child of exactly one parent, control flows straight through us, so we can merge with the parent.
  if parents.len() == 1 && is_only_child_of_all_parents {
    return true;
  }
  // If we're empty and only have one child, control flows straight through us from all parents, so we can be removed.
  if children.len() == 1 && is_empty {
    return true;
  };
  // If we're empty and are the only child of all parents, control flows unconditionally to us from parents, but we do nothing, so we can be removed.
  // If we're empty, we cannot have multiple children, because we would have a CondGoto.
  if is_empty && is_only_child_of_all_parents {
    return true;
  }
  false
}

pub fn optpass_cfg_prune(changed: &mut bool, cfg: &mut Cfg) {
  // Iterate until convergence, instead of waiting for another optimisation pass.
  loop {
    // Merge all empty leaf bblocks into one, so that we can detect CondGoto that actually go to both empty leaves.
    let mut empty_leaves = Vec::new();
    // WARNING: We must update graph within this loop, instead of simply marking and then removing afterwards, as we possibly pop instructions which could make a non-empty bblock empty, but if we don't then immediately update the graph some invariants won't hold (e.g. empty bblocks have <= 1 children). This means we can't use common utility graph functions.
    let mut converged = true;
    for cur in cfg.graph.labels_sorted() {
      // TODO Figure out how to delete node 0 (i.e. re-root).
      if cur == 0 {
        continue;
      };

      let parents = cfg.graph.parents_sorted(cur);
      let children = cfg.graph.children_sorted(cur);
      let is_only_child_of_all_parents = parents
        .iter()
        .all(|&parent| cfg.graph.children_sorted(parent).len() == 1);
      let is_empty = cfg.bblocks.get(cur).is_empty();
      let is_leaf = children.is_empty();

      // Self-loops are not safe to prune; they have an effect (e.g. busy loop).
      if children.contains(&cur) {
        continue;
      }

      if is_empty && is_leaf {
        empty_leaves.push(cur);
      }

      if !can_prune_bblock(&parents, &children, is_only_child_of_all_parents, is_empty) {
        continue;
      }

      for &c in children.iter() {
        // Detach from children.
        cfg.graph.disconnect(cur, c);
        // Connect parents to children.
        for &parent in parents.iter() {
          cfg.graph.connect(parent, c);
        }
      }
      // Detach from parents.
      for &parent in parents.iter() {
        cfg.graph.disconnect(parent, cur);
      }

      // Pop from graph and bblocks.
      let insts = cfg.pop(cur);
      // Move insts to parents, before any CondGoto, and update that CondGoto.
      for &parent in parents.iter() {
        let p_bblock = cfg.bblocks.get_mut(parent);
        let p_condgoto = if p_bblock.last().is_some_and(|i| i.t == InstTyp::CondGoto) {
          Some(p_bblock.pop().unwrap())
        } else {
          None
        };
        p_bblock.extend(insts.clone());
        if let Some(mut inst) = p_condgoto {
          let child = *children.iter().exactly_one().unwrap();
          for l in inst.labels.iter_mut() {
            if *l == cur {
              *l = child;
            };
          }
          // Don't insert CondGoto if it's redundant now.
          // (Other code, including within this function, assume CondGoto means 2 children.)
          if inst.labels[0] == inst.labels[1] {
            continue;
          };
          p_bblock.push(inst);
        }
      }
      // Update phi nodes in children.
      for &c in children.iter() {
        for c_inst in cfg.bblocks.get_mut(c) {
          if c_inst.t != InstTyp::Phi {
            // No more phi nodes.
            break;
          };
          if let Some(ex) = c_inst.remove_phi(cur) {
            for &parent in parents.iter() {
              c_inst.insert_phi(parent, ex.clone());
            }
          };
        }
      }
      *changed = true;
      converged = false;
    }

    // Now that we've found all empty leaves, replace all CondGoto labels that go to any of them with one bblock label.
    if empty_leaves.len() > 1 {
      empty_leaves.sort_unstable();
      empty_leaves.dedup();
      let mut existing_labels = cfg.graph.labels().collect_vec();
      existing_labels.sort_unstable();
      existing_labels.dedup();
      empty_leaves.retain(|label| existing_labels.binary_search(label).is_ok());
      if empty_leaves.len() > 1 {
        for (label, bblocks) in cfg.bblocks.all_mut() {
          let Some(inst) = bblocks.last_mut() else {
            continue;
          };
          if inst.t != InstTyp::CondGoto {
            continue;
          }
          let mut all_children_empty = true;
          for child in inst.labels.iter_mut() {
            if empty_leaves.contains(child) {
              let new_child = empty_leaves[0];
              cfg.graph.disconnect(label, *child);
              cfg.graph.connect(label, new_child);
              *child = new_child;
            } else {
              all_children_empty = false;
            };
          }
          if all_children_empty {
            // Drop the CondGoto.
            bblocks.pop().unwrap();
          };
        }
        // For all other empty leaves, remove them. They should be unreachable.
        for label in empty_leaves.into_iter().skip(1) {
          if cfg.bblocks.maybe_get(label).is_some() {
            cfg.pop(label);
          }
        }
        *changed = true;
      }
    }

    if converged {
      break;
    }
  }
}
