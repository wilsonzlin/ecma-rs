use crate::cfg::cfg::Cfg;
use crate::il::inst::Inst;
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct OptimizerDebugStep {
  pub name: String,
  pub bblock_order: Vec<u32>,
  pub bblocks: BTreeMap<u32, Vec<Inst>>,
  pub cfg_children: BTreeMap<u32, Vec<u32>>,
}

#[derive(Serialize, Debug, Clone)]
pub struct OptimizerDebug {
  steps: Vec<OptimizerDebugStep>,
}

impl OptimizerDebug {
  pub fn new() -> Self {
    Self { steps: Vec::new() }
  }

  pub fn steps(&self) -> &[OptimizerDebugStep] {
    &self.steps
  }

  pub fn add_step(&mut self, name: impl AsRef<str>, cfg: &Cfg) {
    self.steps.push(OptimizerDebugStep {
      name: name.as_ref().to_string(),
      // We always recalculate as some steps may prune or add bblocks.
      bblock_order: cfg.graph.calculate_postorder(0).0,
      bblocks: cfg.bblocks.all().map(|(k, v)| (k, v.clone())).collect(),
      cfg_children: cfg
        .graph
        .labels_sorted()
        .into_iter()
        .map(|k| (k, cfg.graph.children_sorted(k)))
        .collect(),
    });
  }
}
