use serde::Deserialize;
use serde::Serialize;

/// Options that influence type semantics and canonicalization.
///
/// This is intentionally a minimal subset of a full `CompilerOptions` to avoid
/// additional dependencies while still allowing callers to control core
/// behaviors such as null/undefined handling.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct TypeOptions {
  /// Whether `null`/`undefined` are distinct from other types.
  pub strict_null_checks: bool,
}

impl Default for TypeOptions {
  fn default() -> Self {
    Self {
      strict_null_checks: true,
    }
  }
}
