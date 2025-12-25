use optimize_js::cfg::cfg::Cfg;
use optimize_js::Program;
use parse_js::parse;
use serde_json::to_string;
use symbol_js::compute_symbols;
use symbol_js::TopLevelMode;

fn canonical_cfg_json(cfg: &Cfg) -> String {
  let mut labels: Vec<_> = cfg.graph.labels().collect();
  labels.sort_unstable();
  let blocks: Vec<_> = labels
    .into_iter()
    .map(|label| {
      let mut children: Vec<_> = cfg.graph.children(label).collect();
      children.sort_unstable();
      (label, children, cfg.bblocks.get(label).clone())
    })
    .collect();
  to_string(&blocks).expect("serialize cfg")
}

fn compile_cfg(source: &str) -> String {
  let mut node = parse(source).expect("parse source");
  compute_symbols(&mut node, TopLevelMode::Module);
  let program = Program::compile(node, false).expect("compile source");
  canonical_cfg_json(&program.top_level.body)
}

#[test]
fn cfg_pruning_is_deterministic() {
  // Nested empty if/else blocks create multiple prunable basic blocks.
  let source = r#"
    let flag = 1;
    if (flag) {
    } else {
    }
    if (false) {
    } else {
    }
    if (flag) {
      if (flag) {
      } else {
      }
    } else {
      if (true) {
      } else {
      }
    }
  "#;

  let first = compile_cfg(source);
  let second = compile_cfg(source);

  assert_eq!(
    first, second,
    "CFG pruning should produce deterministic results across runs"
  );
}
