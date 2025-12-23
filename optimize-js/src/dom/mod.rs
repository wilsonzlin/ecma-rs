use crate::cfg::cfg::Cfg;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use itertools::Itertools;

pub struct DominatesGraph(HashMap<u32, HashSet<u32>>);

impl DominatesGraph {
  pub fn dominates(&self, a: u32, b: u32) -> bool {
    self.0.get(&a).is_some_and(|s| s.contains(&b))
  }
}

pub struct DominatedByGraph(HashMap<u32, HashSet<u32>>);

impl DominatedByGraph {
  pub fn dominated_by(&self, a: u32, b: u32) -> bool {
    self.0.get(&a).is_some_and(|s| s.contains(&b))
  }
}

pub type PostDom = Dom<true>;

/// If `POST`, calculates postdominance instead of dominance.
pub struct Dom<const POST: bool = false> {
  postorder: Vec<u32>,
  // Inverse of `domtree`, child => parent.
  idom_by: HashMap<u32, u32>,
  // Parent => children, where parent is the immediate dominator of each child.
  // Yes, the name is dominator tree, even though it's only nodes it immediate dominates and not all nodes it dominates. See https://en.wikipedia.org/wiki/Dominator_(graph_theory).
  domtree: HashMap<u32, HashSet<u32>>,
  entry: u32,
}

impl<const POST: bool> Dom<POST> {
  // A dominates B if A will **always** execute some time at or before B. (All paths to B go through A.)
  // B is dominated by A if A also dominates **all** of B's parents. (Think about it.)
  // Dominance tree: edges represent only "immediate" dominations. A immediately dominates B iff A dominates B and doesn't strictly dominate any other node that strictly dominates B. (Strictly dominates means A dominates B and A != B.)
  // NOTE: Every node, except the entry node, has exactly one immediate dominator: https://en.wikipedia.org/wiki/Dominator_(graph_theory).
  //
  // https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
  // - This paper also contains an explanation on how to calculate what a node dominates given `idom_by`, which is much faster than other dominance calculation algorithms.
  // Other implementations:
  // - https://github.com/sampsyo/bril/blob/34133101a68bb50ae0fc8083857a3e3bd6bae260/bril-llvm/dom.py#L47
  // To calculate the post dominators, reverse the edges and run any dominator algorithm. This is what we do when `POST` is true.
  pub fn calculate(cfg: &Cfg) -> Self {
    let entry = if POST {
      // TODO This does not exist.
      u32::MAX
    } else {
      0
    };
    let (postorder, label_to_postorder) = if POST {
      cfg.graph.calculate_reversed_graph_postorder(entry)
    } else {
      cfg.graph.calculate_postorder(entry)
    };

    let mut idom_by = HashMap::<u32, u32>::new();
    let mut domtree = HashMap::<u32, HashSet<u32>>::new();
    {
      macro_rules! intersect {
        ($b1:expr, $b2:expr) => {{
          // WARNING: We're getting the position in postorder, NOT reverse postorder.
          let mut finger1 = label_to_postorder[&$b1];
          let mut finger2 = label_to_postorder[&$b2];
          while finger1 != finger2 {
            while finger1 < finger2 {
              finger1 = label_to_postorder[&idom_by[&postorder[finger1]]];
            }
            while finger2 < finger1 {
              finger2 = label_to_postorder[&idom_by[&postorder[finger2]]];
            }
          }
          postorder[finger1]
        }};
      }
      idom_by.insert(entry, entry);
      loop {
        let mut changed = false;
        for &b in postorder.iter().rev().filter(|b| **b != entry) {
          let parents = if POST {
            cfg.graph.children(b)
          } else {
            cfg.graph.parents(b)
          }
          .collect_vec();
          let Some(mut new_idom) = parents.iter().find(|n| idom_by.contains_key(n)).cloned() else {
            continue;
          };
          let to_skip = new_idom;
          for p in parents.iter().filter(|&&p| p != to_skip) {
            if idom_by.get(&p).is_some() {
              new_idom = intersect!(p, new_idom);
            };
          }
          if idom_by.get(&b) != Some(&new_idom) {
            idom_by.insert(b, new_idom);
            changed = true;
          }
        }
        if !changed {
          break;
        };
      }
      idom_by.remove(&entry);
      for (&c, &p) in idom_by.iter() {
        domtree.entry(p).or_default().insert(c);
      }
    };
    Self {
      postorder,
      idom_by,
      domtree,
      entry,
    }
  }

  // Node => nodes that dominate it (are its dominator). Also called the dominator graph.
  // https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
  pub fn dominated_by_graph(&self) -> DominatedByGraph {
    let mut dom = HashMap::<u32, HashSet<u32>>::new();
    for label in self.idom_by.keys().cloned() {
      let e = dom.entry(label).or_default();
      let mut n = label;
      loop {
        e.insert(n);
        if n == self.entry {
          break;
        };
        n = self.idom_by[&n];
      }
    }
    DominatedByGraph(dom)
  }

  /// Node => nodes that it dominates.
  /// The inverse of `dominated_bys`.
  pub fn dominates_graph(&self) -> DominatesGraph {
    let dom_bys = self.dominated_by_graph();
    let mut doms = HashMap::<u32, HashSet<u32>>::new();
    for (child, dominated_by) in dom_bys.0 {
      for parent in dominated_by {
        doms.entry(parent).or_default().insert(child);
      }
    }
    DominatesGraph(doms)
  }

  // A's dominance frontier contains B if A doesn't dominate B, but does dominate a parent of B.
  // One way of thinking about it: it's the nodes immediately adjacent to the subgraph of A's domination.
  // Another way to think about it: B is dominated by A if all of B's parents are dominated by A (see comments further up). On the other hand, if it's in the fringe, at least one parent is dominated by A, but not all of them.
  // https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf
  // Other implementations: https://github.com/sampsyo/bril/blob/34133101a68bb50ae0fc8083857a3e3bd6bae260/bril-llvm/dom.py#L69
  // It'd be nice to store `cfg` on `Dom`, but that'd keep it borrowed, and usually we want to mutate the CFG using dominance information (and not recalculate every time).
  pub fn dominance_frontiers(&self, cfg: &Cfg) -> HashMap<u32, HashSet<u32>> {
    let mut domfront = HashMap::<u32, HashSet<u32>>::new();
    for &b in self.postorder.iter().rev() {
      let mut parents = cfg.graph.parents(b).collect_vec();
      parents.sort_unstable();
      if parents.len() < 2 {
        continue;
      };
      for &p in parents.iter() {
        let mut runner = p;
        while runner != self.idom_by[&b] {
          domfront.entry(runner).or_default().insert(b);
          runner = self.idom_by[&runner];
        }
      }
    }
    domfront
  }

  /// Yields the child nodes that are immediately dominated by the parent node.
  pub fn immediately_dominated_by(&self, parent: u32) -> impl Iterator<Item = u32> + '_ {
    self
      .domtree
      .get(&parent)
      .map(|s| {
        let mut children = s.iter().copied().collect_vec();
        children.sort_unstable();
        children
      })
      .into_iter()
      .flatten()
  }
}

#[cfg(test)]
mod tests {
  use crate::cfg::cfg::Cfg;
  use crate::cfg::cfg::CfgGraph;
  use crate::dom::Dom;

  /*
    ```mermaid
      graph TD
        0[Block 0: Entry] --> 1[Block 1: First Loop Header]
        1 --> 2[Block 2: Nested Loop Header]
        2 --> 3[Block 3: Conditional]
        3 --> 4[Block 4: Continue Path]
        4 --> 2
        3 --> 5[Block 5: Break Handler]
        5 --> 1
        1 --> 6[Block 6: Post-Loop Block]
        6 --> 7[Block 7: Final Block]
        7 --> MAX[Block MAX: Exit Path]
        7 --> 2

        style 1 fill:#f9f,stroke:#333
        style 2 fill:#f9f,stroke:#333
        style 3 fill:#bbf,stroke:#333
    ```
  */
  fn create_complex_cfg() -> Cfg {
    let mut graph = CfgGraph::default();
    // First loop header
    graph.connect(0, 1);

    // Nested loop header
    graph.connect(1, 2);

    // Some conditional
    graph.connect(2, 3);

    // Continue path back to nested loop
    graph.connect(3, 4);
    graph.connect(4, 2);

    // Break from nested loop to next step
    graph.connect(3, 5);

    // Outer loop continue
    graph.connect(5, 1);

    // Exit first loop
    graph.connect(1, 6);

    // Another block after loops
    graph.connect(6, 7);

    // A final conditional branch
    graph.connect(7, u32::MAX);
    graph.connect(7, 2); // Jump back to nested loop (labeled break scenario)

    Cfg {
      bblocks: Default::default(),
      graph,
    }
  }

  #[test]
  fn test_dom() {
    let cfg = create_complex_cfg();

    let dom = Dom::<false>::calculate(&cfg);
    let postdom = Dom::<true>::calculate(&cfg);

    let dominates = dom.dominates_graph();
    let postdominates = postdom.dominates_graph();

    assert!(dominates.dominates(0, 1));
    assert!(dominates.dominates(2, 4));
    assert!(postdominates.dominates(6, 5));
  }
}
