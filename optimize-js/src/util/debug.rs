use crate::cfg::cfg::Cfg;
use crate::il::inst::Inst;
use ahash::HashMap;
use ahash::HashSet;
use serde::Serialize;

#[derive(Serialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct OptimizerDebugStep {
  pub name: String,
  pub bblock_order: Vec<u32>,
  pub bblocks: HashMap<u32, Vec<Inst>>,
  pub cfg_children: HashMap<u32, HashSet<u32>>,
}

#[derive(Serialize, Debug)]
pub struct OptimizerDebug {
  steps: Vec<OptimizerDebugStep>,
}

impl OptimizerDebug {
  pub fn new() -> Self {
    Self { steps: Vec::new() }
  }

  pub fn add_step(&mut self, name: impl AsRef<str>, cfg: &Cfg) {
    self.steps.push(OptimizerDebugStep {
      name: name.as_ref().to_string(),
      // We always recalculate as some steps may prune or add bblocks.
      bblock_order: cfg.graph.calculate_postorder(0).0,
      bblocks: cfg.bblocks.all().map(|(k, v)| (k, v.clone())).collect(),
      cfg_children: cfg
        .graph
        .labels()
        .map(|k| (k, cfg.graph.children(k).collect()))
        .collect(),
    });
  }
}
