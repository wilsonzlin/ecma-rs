mod emitter;
mod escape;
mod expr;
mod expr_ts;
mod jsx;
mod pat;
mod precedence;
mod stmt_start;
mod ts_stmt;
mod ts_type;

use diagnostics::{Diagnostic, FileId, Span, TextRange};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;

pub use emitter::{EmitError, EmitErrorKind, EmitMode, EmitOptions, EmitResult, Emitter};
pub use escape::emit_string_literal_double_quoted;
pub use escape::emit_template_raw_segment;
pub use expr::{emit_expr, ExprEmitter};
pub use jsx::{emit_jsx_elem, emit_jsx_expr_container};
pub use pat::{emit_param_decl, emit_pat, emit_pat_decl};
pub use stmt_start::{emit_expr_stmt, emit_expr_stmt_with, expr_stmt_needs_parens};
pub use ts_stmt::{emit_top_level, emit_ts_stmt};
pub use ts_type::{
  emit_interface_decl,
  emit_ts_type,
  emit_type_alias_decl,
  emit_type_expr,
  emit_type_members,
  ts_type_to_string,
};

/// Emit a top-level AST into JavaScript/TypeScript, returning a diagnostic on
/// failure with a best-effort span describing where emission failed.
pub fn emit_top_level_diagnostic(
  file: FileId,
  ast: &Node<TopLevel>,
  options: EmitOptions,
) -> Result<String, Diagnostic> {
  let mut emitter = Emitter::new(options);
  match emit_top_level(&mut emitter, ast.stx.as_ref()) {
    Ok(()) => Ok(String::from_utf8(emitter.into_bytes()).expect("Emitter output is UTF-8")),
    Err(err) => Err(diagnostic_from_emit_error(file, err)),
  }
}

fn diagnostic_from_emit_error(file: FileId, err: EmitError) -> Diagnostic {
  let (mut range, mut notes) = err
    .loc
    .map(|loc| loc.to_diagnostics_range_with_note())
    .unwrap_or((TextRange::new(0, 1), None));
  if range.is_empty() {
    range.end = range.start.saturating_add(1);
  }
  let mut collected_notes = Vec::new();
  if let Some(note) = notes.take() {
    collected_notes.push(note);
  }

  let (code, message, extra_note): (&'static str, String, Option<String>) = match err.kind {
    EmitErrorKind::Unsupported(reason) => {
      ("EMIT0001", format!("unsupported syntax: {reason}"), None)
    }
    EmitErrorKind::MissingTypeAnnotation => (
      "EMIT0002",
      "type annotation required for emission".into(),
      None,
    ),
    EmitErrorKind::Fmt(_) => (
      "EMIT0003",
      "failed to format emitted output".into(),
      Some("formatter returned an error while emitting code".into()),
    ),
  };

  let mut diagnostic = Diagnostic::error(code, message, Span { file, range });
  for note in collected_notes {
    diagnostic = diagnostic.with_note(note);
  }
  if let Some(note) = extra_note {
    diagnostic = diagnostic.with_note(note);
  }
  diagnostic
}
