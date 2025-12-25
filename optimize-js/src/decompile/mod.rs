pub mod foreign;
pub mod il;
pub mod structurer;
pub mod top_level;

use crate::Program;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

pub use foreign::{collect_foreign_bindings, ForeignBinding, ForeignBindings};
pub use il::{
  lower_function, lower_program, LoweredArg, LoweredBlock, LoweredFunction, LoweredInst,
  LoweredProgram,
};
pub use structurer::{structure_cfg, BreakTarget, ControlTree, LoopLabel};
pub use top_level::{build_top_level, foreign_var_decl, prepend_foreign_decls};

/// Controls how an optimized [`Program`] is decompiled back into syntax.
#[derive(Clone, Copy, Debug)]
pub struct DecompileOptions {
  /// Whether to insert explicit declarations for SSA registers before they are used.
  pub declare_registers: bool,
  /// Whether to emit bindings for captured/foreign variables so the output is runnable
  /// without providing an external environment.
  pub emit_foreign_bindings: bool,
}

impl Default for DecompileOptions {
  fn default() -> Self {
    Self {
      declare_registers: false,
      emit_foreign_bindings: true,
    }
  }
}

/// Converts an optimized [`Program`] into a `parse-js` [`TopLevel`] AST.
///
/// This sets up a deterministic, public API surface for downstream consumers. The actual
/// control-flow structurization is delegated to dedicated helpers; this function wires
/// together the pieces so callers have a stable entry point today.
pub fn program_to_ast(program: &Program, opts: &DecompileOptions) -> Node<TopLevel> {
  // TODO Convert CFG back into structured AST statements.
  let body = Vec::new();

  if opts.emit_foreign_bindings {
    let bindings = collect_foreign_bindings(program);
    build_top_level(body, &bindings)
  } else {
    Node::new(Loc(0, 0), TopLevel { body })
  }
}

/// Converts the optimized [`Program`] into emitted JS bytes using `emit-js`.
///
/// Requires the `emit` Cargo feature.
#[cfg(feature = "emit")]
pub fn program_to_js(
  program: &Program,
  decompile: &DecompileOptions,
  emit: emit_js::EmitOptions,
) -> Result<Vec<u8>, emit_js::EmitError> {
  let ast = program_to_ast(program, decompile);
  let mut emitter = emit_js::Emitter::new(emit);
  emit_js::emit_top_level(&mut emitter, ast.stx.as_ref())?;
  Ok(emitter.into_bytes())
}
