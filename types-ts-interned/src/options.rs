use serde::Deserialize;
use serde::Serialize;

/// Options that influence type semantics and canonicalization.
///
/// This is intentionally a minimal subset of a full `CompilerOptions` to avoid
/// additional dependencies while still allowing callers to control core
/// behaviors such as null/undefined handling or function parameter variance.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeOptions {
  /// Whether `null`/`undefined` are distinct from other types.
  pub strict_null_checks: bool,
  /// Whether function parameters are checked contravariantly (when `true`) or
  /// bivariantly (when `false`, mirroring `strictFunctionTypes: false`).
  pub strict_function_types: bool,
  /// Whether optional properties implicitly include `undefined` in their type
  /// (`false`, the default) or are treated as "exact" without an added
  /// `undefined` (`true`).
  pub exact_optional_property_types: bool,
  /// Whether indexed access types implicitly include `undefined`, mirroring
  /// TypeScript's `noUncheckedIndexedAccess`.
  pub no_unchecked_indexed_access: bool,
}

impl Default for TypeOptions {
  fn default() -> Self {
    Self {
      strict_null_checks: true,
      strict_function_types: true,
      exact_optional_property_types: false,
      no_unchecked_indexed_access: false,
    }
  }
}
