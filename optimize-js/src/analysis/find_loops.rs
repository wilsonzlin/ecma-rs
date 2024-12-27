use std::collections::VecDeque;

use ahash::{HashMap, HashMapExt, HashSet};

use crate::{cfg::cfg::Cfg, dom::Dom};


// - Given backedge from B -> A, A is the loop header.
// - Multiple backedges may point to the same tail (i.e. loop header) but have different heads.
//   - Consider: `continue` statements.
// - A backedge may point to a loop header outside its own loop.
//   - Consider: labelled `continue` statements.
// - A loop may be inside another loop; therefore, nodes may be part of multiple loops.
pub fn find_loops(
  cfg: &Cfg,
  dom: &Dom,
) -> HashMap<u32, HashSet<u32>> {
  let dominates = dom.dominates_graph();
  // Map from header -> nodes (including the header).
  let mut loops = HashMap::<u32, HashSet<u32>>::new();
  // Iterate all edges. We're looking for backedges, so we call an a->b edge tail->header (which isn't true until we check it is a backedge).
  for tail in cfg.graph.labels() {
    for header in cfg.graph.children(tail) {
      // If `header` dominates `tail`, then tail->header is a backedge.
      if !dominates.dominates(header, tail) {
        continue;
      };
      let l = loops.entry(header).or_default();
      l.insert(header);
      l.insert(tail);
      // Traverse backwards from tail to find nodes dominated by header.
      let mut queue = VecDeque::from([tail]);
      while let Some(n) = queue.pop_front() {
        // We have reducible CFGs, so all parents must be part of the loop; they can't magically enter from outside the loop.
        for p in cfg.graph.parents(n) {
          if !l.insert(p) {
            // Already visited.
            continue;
          };
          queue.push_back(p);
        };
      };
    }
  };
  loops
}
