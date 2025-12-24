use serde::Deserialize;
use serde::Serialize;

/// Options that influence type semantics and canonicalization.
///
/// This is intentionally a minimal subset of a full `CompilerOptions` to avoid
/// additional dependencies while still allowing callers to control core
/// behaviors such as null/undefined handling or function parameter variance.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct TypeOptions {
  /// Whether `null`/`undefined` are distinct from other types.
  pub strict_null_checks: bool,
  /// Whether function parameters are checked contravariantly (`true`) or with
  /// the legacy bivariant behavior (`false`).
  pub strict_function_types: bool,
}

impl Default for TypeOptions {
  fn default() -> Self {
    Self {
      strict_null_checks: true,
      strict_function_types: true,
    }
  }
}
