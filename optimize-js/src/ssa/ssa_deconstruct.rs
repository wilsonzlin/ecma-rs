use crate::cfg::cfg::Cfg;
use crate::il::inst::Inst;
use crate::il::inst::InstTyp;
use crate::util::counter::Counter;
use std::collections::BTreeMap;
use std::iter::zip;

pub fn deconstruct_ssa(cfg: &mut Cfg, c_label: &mut Counter) {
  struct NewBblock {
    label: u32,
    parent: u32,
    child: u32,
    insts: Vec<Inst>,
  }
  let mut new_bblocks = Vec::<NewBblock>::new();
  let mut labels: Vec<u32> = cfg.bblocks.all().map(|(label, _)| label).collect();
  labels.sort_unstable();
  for label in labels {
    let bblock = cfg.bblocks.get_mut(label);
    let mut new_bblocks_by_parent = BTreeMap::<u32, NewBblock>::new();
    while bblock.first().is_some_and(|i| i.t == InstTyp::Phi) {
      let removed_phi_inst = bblock.remove(0);
      let tgt = removed_phi_inst.tgts[0];
      for (parent, value) in zip(removed_phi_inst.labels, removed_phi_inst.args) {
        new_bblocks_by_parent
          .entry(parent)
          .or_insert_with(|| NewBblock {
            label: c_label.bump(),
            parent,
            child: label,
            insts: Vec::new(),
          })
          .insts
          .push(Inst::var_assign(tgt, value));
      }
    }
    new_bblocks.extend(new_bblocks_by_parent.into_values());
  }
  new_bblocks.sort_by_key(|b| b.label);
  for mut b in new_bblocks {
    // Detach parent from child.
    cfg.graph.disconnect(b.parent, b.child);
    // Update any CondGoto inst in parent.
    if let Some(parent_goto) = cfg.bblocks.get_mut(b.parent).last_mut() {
      if parent_goto.t == InstTyp::CondGoto {
        for l in parent_goto.labels.iter_mut() {
          if *l == b.child {
            *l = b.label;
          };
        }
      };
    };
    // Attach new bblock.
    cfg.graph.connect(b.parent, b.label);
    cfg.graph.connect(b.label, b.child);
    // Insert new bblock.
    cfg.bblocks.add(b.label, b.insts);
  }
}
