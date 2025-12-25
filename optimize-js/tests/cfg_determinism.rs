use ahash::HashMap;
use ahash::HashSet;
use optimize_js::analysis::find_loops::find_loops;
use optimize_js::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use optimize_js::dom::Dom;
use optimize_js::il::inst::{Arg, Const, Inst};
use optimize_js::opt::optpass_cfg_prune::optpass_cfg_prune;
use optimize_js::opt::optpass_impossible_branches::optpass_impossible_branches;
use parse_js::num::JsNumber;
use serde::Serialize;
use std::collections::BTreeMap;

fn sample_block(label: u32) -> Vec<Inst> {
  match label {
    0 => vec![Inst::cond_goto(Arg::Const(Const::Bool(true)), 1, 2)],
    1 => vec![Inst::var_assign(10, Arg::Const(Const::Num(JsNumber(1.0))))],
    2 => vec![Inst::var_assign(11, Arg::Const(Const::Num(JsNumber(2.0))))],
    3 => vec![Inst::var_assign(12, Arg::Var(10))],
    _ => vec![],
  }
}

fn build_cfg(label_insertion: &[u32], edge_order: &[(u32, u32)]) -> Cfg {
  let mut graph = CfgGraph::default();
  for &(parent, child) in edge_order {
    graph.connect(parent, child);
  }
  let mut bblocks = CfgBBlocks::default();
  for &label in label_insertion {
    bblocks.add(label, sample_block(label));
  }
  Cfg { graph, bblocks }
}

fn canonicalize_dom(dom: &Dom, cfg: &Cfg) -> BTreeMap<u32, Vec<u32>> {
  let mut domtree = BTreeMap::new();
  for label in cfg.graph.labels_sorted() {
    let children = dom.immediately_dominated_by(label).collect::<Vec<_>>();
    if !children.is_empty() {
      domtree.insert(label, children);
    }
  }
  domtree
}

fn canonicalize_loops(loops: &HashMap<u32, HashSet<u32>>) -> BTreeMap<u32, Vec<u32>> {
  let mut out = BTreeMap::new();
  for (header, nodes) in loops {
    let mut members: Vec<_> = nodes.iter().copied().collect();
    members.sort_unstable();
    out.insert(*header, members);
  }
  out
}

#[derive(Serialize)]
struct SerializableCfg {
  bblocks: BTreeMap<u32, Vec<Inst>>,
  edges: BTreeMap<u32, Vec<u32>>,
}

fn serialize_cfg(cfg: &Cfg) -> String {
  let mut edges = BTreeMap::new();
  for label in cfg.graph.labels_sorted() {
    edges.insert(label, cfg.graph.children_sorted(label));
  }

  let mut bblocks = BTreeMap::new();
  for (label, insts) in cfg.bblocks.all() {
    bblocks.insert(label, insts.clone());
  }

  serde_json::to_string(&SerializableCfg { bblocks, edges }).unwrap()
}

fn run_once(mut cfg: Cfg) -> (BTreeMap<u32, Vec<u32>>, BTreeMap<u32, Vec<u32>>, String) {
  let mut changed = false;
  optpass_impossible_branches(&mut changed, &mut cfg);

  let dom = Dom::calculate(&cfg);
  let dom_tree = canonicalize_dom(&dom, &cfg);
  let loops = canonicalize_loops(&find_loops(&cfg, &dom));

  optpass_cfg_prune(&mut changed, &mut cfg);

  (dom_tree, loops, serialize_cfg(&cfg))
}

#[test]
fn cfg_algorithms_are_deterministic() {
  let first = build_cfg(&[0, 1, 2, 3], &[(0, 1), (0, 2), (1, 3), (2, 3), (3, 1)]);
  let second = build_cfg(&[3, 2, 1, 0], &[(3, 1), (2, 3), (1, 3), (0, 2), (0, 1)]);

  let first_result = run_once(first);
  let second_result = run_once(second);

  assert_eq!(
    first_result.0, second_result.0,
    "dominator trees should match"
  );
  assert_eq!(
    first_result.1, second_result.1,
    "loop detection should match"
  );
  assert_eq!(first_result.2, second_result.2, "final CFG should match");
}
