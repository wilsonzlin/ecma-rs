use optimize_js::cfg::cfg::Cfg;
use optimize_js::cfg::cfg::CfgGraph;
use optimize_js::dom::PostDom;

fn cfg_from_edges(edges: &[(u32, u32)]) -> Cfg {
  let mut graph = CfgGraph::default();
  for &(from, to) in edges {
    graph.connect(from, to);
  }
  Cfg {
    bblocks: Default::default(),
    graph,
  }
}

#[test]
fn postdom_linear_without_explicit_exit() {
  let cfg = cfg_from_edges(&[(0, 1), (1, 2)]);
  let postdom = PostDom::calculate(&cfg);

  assert_eq!(postdom.entry_label(), u32::MAX);
  assert_eq!(postdom.idom_of(0), Some(1));
  assert_eq!(postdom.idom_of(1), Some(2));
  assert_eq!(postdom.idom_of(2), Some(u32::MAX));
}

#[test]
fn postdom_diamond_branch_immediate_postdom() {
  let cfg = cfg_from_edges(&[(0, 1), (0, 2), (1, 3), (2, 3)]);
  let postdom = PostDom::calculate(&cfg);

  assert_eq!(postdom.idom_of(1), Some(3));
  assert_eq!(postdom.idom_of(2), Some(3));
  assert_eq!(postdom.idom_of(0), Some(3));
  assert_eq!(postdom.idom_of(3), Some(u32::MAX));
}

#[test]
fn postdom_handles_infinite_loop() {
  // 0 -> 1 -> 1, no terminal blocks.
  let cfg = cfg_from_edges(&[(0, 1), (1, 1)]);
  let postdom = PostDom::calculate(&cfg);

  assert_eq!(postdom.entry_label(), u32::MAX);
  assert_eq!(postdom.idom_of(1), Some(u32::MAX));
  assert_eq!(postdom.idom_of(0), Some(u32::MAX));
}
