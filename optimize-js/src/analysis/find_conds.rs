use ahash::{HashMap, HashSet};

use crate::{cfg::cfg::Cfg, dom::{Dom, PostDom}};

/// Finds conditional expressions/statements in the CFG.
/// Returns a map from the condition node to the set of nodes that it controls.
pub fn find_conds(
  cfg: &Cfg,
  dom: &Dom,
  postdom: &PostDom,
) -> HashMap<u32, HashSet<u32>> {
  todo!()
}
