use clap::ValueEnum;

#[derive(Debug, Clone, Copy, Default, ValueEnum, PartialEq, Eq)]
pub enum FailOn {
  /// Non-zero on any mismatch.
  All,
  /// Non-zero only for mismatches not covered by manifest (default).
  #[default]
  New,
  /// Always zero.
  None,
}

impl FailOn {
  pub fn should_fail(&self, unexpected_mismatches: usize, total_mismatches: usize) -> bool {
    match self {
      FailOn::All => total_mismatches > 0,
      FailOn::New => unexpected_mismatches > 0,
      FailOn::None => false,
    }
  }
}
