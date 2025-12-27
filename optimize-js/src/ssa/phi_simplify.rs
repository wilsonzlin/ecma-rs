use crate::cfg::cfg::Cfg;
use crate::il::inst::{Arg, Const, Inst, InstTyp};
use ahash::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};

#[derive(Debug, PartialEq, Eq)]
pub enum PhiValidationError {
  NonPhiBeforePhi {
    block: u32,
    inst: usize,
  },
  LabelsArgsLengthMismatch {
    block: u32,
    inst: usize,
    labels_len: usize,
    args_len: usize,
  },
  UnknownPredecessor {
    block: u32,
    inst: usize,
    label: u32,
  },
  DuplicatePredecessor {
    block: u32,
    inst: usize,
    label: u32,
  },
  UnsortedPredecessors {
    block: u32,
    inst: usize,
    previous: u32,
    label: u32,
  },
}

impl Display for PhiValidationError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::NonPhiBeforePhi { block, inst } => write!(
        f,
        "block {block} has Phi at {inst} after a non-Phi instruction"
      ),
      Self::LabelsArgsLengthMismatch {
        block,
        inst,
        labels_len,
        args_len,
      } => write!(
        f,
        "block {block} Phi {inst} has {labels_len} labels but {args_len} args"
      ),
      Self::UnknownPredecessor { block, inst, label } => write!(
        f,
        "block {block} Phi {inst} references non-predecessor {label}"
      ),
      Self::DuplicatePredecessor { block, inst, label } => write!(
        f,
        "block {block} Phi {inst} references predecessor {label} more than once"
      ),
      Self::UnsortedPredecessors {
        block,
        inst,
        previous,
        label,
      } => write!(
        f,
        "block {block} Phi {inst} predecessors are not sorted: {previous} then {label}"
      ),
    }
  }
}

impl std::error::Error for PhiValidationError {}

pub fn validate_phis(cfg: &Cfg) -> Result<(), PhiValidationError> {
  for (label, block) in cfg.bblocks.all() {
    let mut seen_non_phi = false;
    let parents: HashSet<u32> = cfg.graph.parents(label).collect();
    for (idx, inst) in block.iter().enumerate() {
      if inst.t != InstTyp::Phi {
        seen_non_phi = true;
        continue;
      }
      if seen_non_phi {
        return Err(PhiValidationError::NonPhiBeforePhi {
          block: label,
          inst: idx,
        });
      }
      if inst.labels.len() != inst.args.len() {
        return Err(PhiValidationError::LabelsArgsLengthMismatch {
          block: label,
          inst: idx,
          labels_len: inst.labels.len(),
          args_len: inst.args.len(),
        });
      }
      let mut seen_labels = HashSet::default();
      let mut last = None;
      for &pred in inst.labels.iter() {
        if !parents.contains(&pred) {
          return Err(PhiValidationError::UnknownPredecessor {
            block: label,
            inst: idx,
            label: pred,
          });
        }
        if !seen_labels.insert(pred) {
          return Err(PhiValidationError::DuplicatePredecessor {
            block: label,
            inst: idx,
            label: pred,
          });
        }
        if let Some(previous) = last {
          if pred < previous {
            return Err(PhiValidationError::UnsortedPredecessors {
              block: label,
              inst: idx,
              previous,
              label: pred,
            });
          }
        }
        last = Some(pred);
      }
    }
  }
  Ok(())
}

fn count_var_uses(cfg: &Cfg) -> HashMap<u32, usize> {
  let mut uses = HashMap::default();
  for (_, block) in cfg.bblocks.all() {
    for inst in block {
      for arg in inst.args.iter() {
        if let Arg::Var(var) = arg {
          *uses.entry(*var).or_default() += 1;
        }
      }
    }
  }
  uses
}

pub fn simplify_phis(cfg: &mut Cfg) -> bool {
  let mut changed = false;
  let use_counts = count_var_uses(cfg);

  for (label, block) in cfg.bblocks.all_mut() {
    let phi_len = block.iter().take_while(|i| i.t == InstTyp::Phi).count();
    let mut rest = block.split_off(phi_len);
    let mut phis: Vec<_> = block.drain(..).collect();
    let mut reordered_rest = Vec::new();
    for inst in rest.drain(..) {
      if inst.t == InstTyp::Phi {
        phis.push(inst);
        changed = true;
      } else {
        reordered_rest.push(inst);
      }
    }
    rest = reordered_rest;

    debug_assert!(
      rest.iter().all(|inst| inst.t != InstTyp::Phi),
      "Phi nodes should be hoisted to the start of blocks"
    );

    let parents: HashSet<u32> = cfg.graph.parents(label).collect();

    let mut new_phis = Vec::new();
    let mut lowered = Vec::new();

    for mut inst in phis {
      let original_labels = inst.labels.clone();
      let original_args = inst.args.clone();
      let original_labels_len = inst.labels.len();
      let original_args_len = inst.args.len();

      let mut entries: Vec<_> = inst
        .labels
        .into_iter()
        .zip(inst.args.into_iter())
        .filter(|(pred, _)| parents.contains(pred))
        .collect();

      let mut deduped = Vec::new();
      entries.sort_by_key(|(pred, _)| *pred);
      for (pred, arg) in entries {
        if let Some((last_pred, last_arg)) = deduped.last_mut() {
          if *last_pred == pred {
            *last_arg = arg;
            continue;
          }
        }
        deduped.push((pred, arg));
      }

      inst.labels = deduped.iter().map(|(pred, _)| *pred).collect();
      inst.args = deduped.iter().map(|(_, arg)| arg.clone()).collect();

      if inst.labels.is_empty() {
        let tgt = inst.tgts[0];
        if *use_counts.get(&tgt).unwrap_or(&0) > 0 {
          lowered.push(Inst::var_assign(tgt, Arg::Const(Const::Undefined)));
        }
        changed = true;
      } else if inst.labels.len() == 1 {
        let tgt = inst.tgts[0];
        lowered.push(Inst::var_assign(tgt, inst.args.pop().unwrap()));
        changed = true;
      } else {
        if inst.labels.len() != original_labels_len || inst.args.len() != original_args_len {
          changed = true;
        } else if inst.labels != original_labels || inst.args != original_args {
          changed = true;
        }
        new_phis.push(inst);
      }
    }

    block.clear();
    block.extend(new_phis);
    block.extend(lowered);
    block.append(&mut rest);
  }

  #[cfg(debug_assertions)]
  {
    if let Err(err) = validate_phis(cfg) {
      panic!("validate_phis failed: {err}");
    }
  }

  changed
}
