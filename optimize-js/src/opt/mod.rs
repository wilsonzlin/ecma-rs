pub mod optpass_cfg_prune;
pub mod optpass_dvn;
pub mod optpass_impossible_branches;
pub mod optpass_redundant_assigns;
pub mod optpass_trivial_dce;

#[derive(Default, Clone, Copy, Debug)]
pub struct PassResult {
  pub changed: bool,
  pub cfg_changed: bool,
}

impl PassResult {
  pub fn any_change(&self) -> bool {
    self.changed
  }

  pub fn mark_changed(&mut self) {
    self.changed = true;
  }

  pub fn mark_cfg_changed(&mut self) {
    self.cfg_changed = true;
    self.mark_changed();
  }

  pub fn merge(&mut self, other: PassResult) {
    self.changed |= other.changed;
    self.cfg_changed |= other.cfg_changed;
  }
}
