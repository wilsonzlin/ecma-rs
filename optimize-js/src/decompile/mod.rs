pub mod foreign;
pub mod il;
pub mod names;
pub mod regalloc;
pub mod structurer;
pub mod top_level;

mod options;

use crate::il::inst::Arg;
use crate::{Program, ProgramFunction};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

pub use foreign::{collect_foreign_bindings, ForeignBinding, ForeignBindings};
pub use il::{
  lower_function, lower_program, LoweredArg, LoweredBlock, LoweredFunction, LoweredInst,
  LoweredProgram,
};
pub use names::{collect_reserved_from_cfg, collect_reserved_from_insts, NameMangler};
pub use options::{DecompileOptions, ResolvedTempDeclStyle, TempDeclScope, TempDeclStyle};
pub use structurer::{structure_cfg, BreakTarget, ControlTree, LoopLabel};
pub use top_level::{build_top_level, foreign_var_decl, prepend_foreign_decls};

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

fn collect_temps(func: &ProgramFunction) -> Vec<u32> {
  let mut temps = Vec::new();
  for (_, insts) in func.body.bblocks.all() {
    for inst in insts {
      temps.extend(inst.tgts.iter().copied());
      for arg in &inst.args {
        if let Arg::Var(var) = arg {
          temps.push(*var);
        }
      }
    }
  }
  temps.sort_unstable();
  temps.dedup();
  temps
}

fn format_temp_decls(temps: &[u32], style: ResolvedTempDeclStyle) -> Option<String> {
  if temps.is_empty() {
    return None;
  }

  let mut out = String::new();
  match style {
    ResolvedTempDeclStyle::Var => out.push_str("var "),
    ResolvedTempDeclStyle::LetWithVoidInit => out.push_str("let "),
  }

  for (idx, temp) in temps.iter().enumerate() {
    if idx > 0 {
      out.push_str(", ");
    }
    out.push('r');
    out.push_str(&temp.to_string());
    if matches!(style, ResolvedTempDeclStyle::LetWithVoidInit) {
      out.push_str("=void 0");
    }
  }
  out.push(';');
  Some(out)
}

/// Emits a declaration statement for the temporaries used inside `func`.
///
/// The declaration style is resolved using the provided `scope`; callers should
/// pass [`TempDeclScope::TopLevel`] for program-level code so `Auto` can take
/// [`crate::TopLevelMode`] into account.
pub fn temp_decls_for_function(
  func: &ProgramFunction,
  scope: TempDeclScope,
  options: &DecompileOptions,
) -> Option<String> {
  let temps = collect_temps(func);
  let style = options.resolve_temp_decl_style(scope);
  format_temp_decls(&temps, style)
}

/// Convenience wrapper for the program top-level that uses [`Program::top_level_mode`]
/// when resolving the declaration style.
pub fn temp_decls_for_top_level(program: &Program, options: &DecompileOptions) -> Option<String> {
  temp_decls_for_function(
    &program.top_level,
    TempDeclScope::TopLevel(program.top_level_mode),
    options,
  )
}

/// Emits a `var`-style declaration for nested functions unless overridden by
/// options.
pub fn temp_decls_for_nested_function(
  func: &ProgramFunction,
  options: &DecompileOptions,
) -> Option<String> {
  temp_decls_for_function(func, TempDeclScope::Function, options)
}
