use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::dom::PostDom;
use ahash::HashMap;
use ahash::HashSet;

/// Finds conditional expressions/statements in the CFG.
/// Returns a map from the condition node to the set of nodes that it controls.
pub fn find_conds(_cfg: &Cfg, _dom: &Dom, _postdom: &PostDom) -> HashMap<u32, HashSet<u32>> {
  todo!()
}
