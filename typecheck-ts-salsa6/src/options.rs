/// JSX transformation mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JsxMode {
  /// Leave JSX intact.
  Preserve,
  /// Transform using the classic React runtime.
  React,
  /// Transform using the automatic JSX runtime.
  ReactAutomatic,
  /// Disable JSX parsing.
  NoJsx,
}

/// ECMAScript target version.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Target {
  /// ES5 output.
  Es5,
  /// ES2015 output.
  Es2015,
  /// ES2020 output.
  Es2020,
  /// ES2022 output.
  Es2022,
  /// Always use the newest supported target.
  Latest,
}

/// Compiler options that materially affect type checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompilerOptions {
  /// Whether `null`/`undefined` are distinct from other types.
  pub strict_null_checks: bool,
  /// Whether implicit `any` is allowed.
  pub no_implicit_any: bool,
  /// Whether function type variance follows `--strictFunctionTypes` rules.
  pub strict_function_types: bool,
  /// Whether optional properties are exact (`?` does not include `undefined`).
  pub exact_optional_property_types: bool,
  /// Whether indexed access adds `undefined` when property may not exist.
  pub no_unchecked_indexed_access: bool,
  /// JSX transform mode.
  pub jsx_mode: JsxMode,
  /// ECMAScript target.
  pub target: Target,
}

impl Default for CompilerOptions {
  fn default() -> Self {
    Self {
      strict_null_checks: true,
      no_implicit_any: true,
      strict_function_types: true,
      exact_optional_property_types: true,
      no_unchecked_indexed_access: true,
      jsx_mode: JsxMode::Preserve,
      target: Target::Latest,
    }
  }
}
