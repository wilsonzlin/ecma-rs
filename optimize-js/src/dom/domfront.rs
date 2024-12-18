use ahash::{HashMap, HashMapExt, HashSet};
use itertools::Itertools;

use crate::cfg::cfg::Cfg;

// A's dominance frontier contains B if A doesn't dominate B, but does dominate a parent of B.
// One way of thinking about it: it's the nodes immediately adjacent to the subgraph of A's domination.
// Another way to think about it: B is dominated by A if all of B's parents are dominated by A (see comments further up). On the other hand, if it's in the fringe, at least one parent is dominated by A, but not all of them.
// https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
// Other implementations: https://github.com/sampsyo/bril/blob/34133101a68bb50ae0fc8083857a3e3bd6bae260/bril-llvm/dom.py#L69
pub fn calculate_domfront(
  cfg: &Cfg,
  idom_by: &HashMap<u32, u32>,
  postorder: &[u32],
) -> HashMap<u32, HashSet<u32>> {
  let mut domfront = HashMap::<u32, HashSet<u32>>::new();
  for &b in postorder.iter().rev() {
    let parents = cfg.graph.parents(b).collect_vec();
    if parents.len() < 2 {
      continue;
    };
    for &p in parents.iter() {
      let mut runner = p;
      while runner != idom_by[&b] {
        domfront.entry(runner).or_default().insert(b);
        runner = idom_by[&runner];
      }
    }
  }
  domfront
}
