use crate::TopLevelMode;

/// Strategy for declaring temporaries/registers emitted by the decompiler.
///
/// `Auto` uses a scope-aware default:
/// - inside functions, `var` is used
/// - at the program top-level, `TopLevelMode::Global` prefers `let ... = void 0`
///   to avoid mutating the global object, while modules default to `var`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TempDeclStyle {
  Auto,
  Var,
  LetWithVoidInit,
}

impl Default for TempDeclStyle {
  fn default() -> Self {
    TempDeclStyle::Auto
  }
}

#[derive(Debug, Clone)]
pub struct DecompileOptions {
  pub temp_decl_style: TempDeclStyle,
  /// Whether to insert explicit declarations for SSA registers before they are used.
  pub declare_registers: bool,
  /// Whether to emit bindings for captured/foreign variables so the output is runnable
  /// without providing an external environment.
  pub emit_foreign_bindings: bool,
}

impl Default for DecompileOptions {
  fn default() -> Self {
    DecompileOptions {
      temp_decl_style: TempDeclStyle::Auto,
      declare_registers: false,
      emit_foreign_bindings: true,
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TempDeclScope {
  Function,
  TopLevel(TopLevelMode),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolvedTempDeclStyle {
  Var,
  LetWithVoidInit,
}

impl DecompileOptions {
  pub fn resolve_temp_decl_style(&self, scope: TempDeclScope) -> ResolvedTempDeclStyle {
    match self.temp_decl_style {
      TempDeclStyle::Var => ResolvedTempDeclStyle::Var,
      TempDeclStyle::LetWithVoidInit => ResolvedTempDeclStyle::LetWithVoidInit,
      TempDeclStyle::Auto => match scope {
        TempDeclScope::Function => ResolvedTempDeclStyle::Var,
        TempDeclScope::TopLevel(mode) => match mode {
          TopLevelMode::Module => ResolvedTempDeclStyle::Var,
          TopLevelMode::Global => ResolvedTempDeclStyle::LetWithVoidInit,
        },
      },
    }
  }
}
