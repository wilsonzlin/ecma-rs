pub use diagnostics::{Diagnostic, FileId, Severity, Span, TextRange};
#[cfg(feature = "emit-minify")]
use emit_js::{emit_hir_file_diagnostic, emit_top_level_diagnostic, EmitOptions};
#[cfg(feature = "emit-minify")]
use hir_js::{lower_file, FileKind};
#[cfg(feature = "emit-minify")]
use parse_js::ast::node::Node;
#[cfg(feature = "emit-minify")]
use parse_js::ast::stx::TopLevel;
use parse_js::{parse_with_options, ParseOptions, SourceType};
#[cfg(not(feature = "emit-minify"))]
use rename::rewrite_source;
use rename::{apply_renames, assign_names, collect_usages};
use semantic_js::js::bind_js;
pub use semantic_js::js::TopLevelMode;
#[cfg(all(test, feature = "emit-minify"))]
use std::cell::Cell;
use ts_erase::erase_types;

pub use parse_js::Dialect;
#[cfg(feature = "fuzzing")]
mod fuzz;
#[cfg(feature = "emit-minify")]
mod opt;
mod rename;
#[cfg(test)]
mod tests;
mod ts_erase;
#[cfg(feature = "fuzzing")]
pub use fuzz::fuzz_minify_pipeline;
mod ts_lower;

#[cfg(feature = "emit-minify")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EmitBackend {
  Hir,
  Ast,
}

#[cfg(all(test, feature = "emit-minify"))]
thread_local! {
  static LAST_EMIT_BACKEND: Cell<Option<EmitBackend>> = Cell::new(None);
  static FORCE_HIR_FAILURE: Cell<bool> = Cell::new(false);
}

#[cfg(all(test, feature = "emit-minify"))]
fn set_last_emit_backend(backend: EmitBackend) {
  LAST_EMIT_BACKEND.with(|cell| cell.set(Some(backend)));
}

#[cfg(all(test, feature = "emit-minify"))]
pub(crate) fn clear_last_emit_backend_for_tests() {
  LAST_EMIT_BACKEND.with(|cell| cell.set(None));
}

#[cfg(all(test, feature = "emit-minify"))]
pub(crate) fn last_emit_backend_for_tests() -> Option<EmitBackend> {
  LAST_EMIT_BACKEND.with(|cell| cell.get())
}

#[cfg(all(test, feature = "emit-minify"))]
pub(crate) fn force_hir_emit_failure_for_tests() {
  FORCE_HIR_FAILURE.with(|flag| flag.set(true));
}

#[cfg(feature = "emit-minify")]
fn emit_minified(
  file: FileId,
  file_kind: FileKind,
  top_level_node: &Node<TopLevel>,
  emit_opts: &EmitOptions,
) -> Result<(String, EmitBackend), Vec<Diagnostic>> {
  #[cfg(all(test, feature = "emit-minify"))]
  let force_failure = FORCE_HIR_FAILURE.with(|flag| flag.replace(false));
  #[cfg(not(all(test, feature = "emit-minify")))]
  let force_failure = false;

  // Prefer emitting from HIR. Only fall back to the AST emitter when the HIR
  // emission path reports an error (typically due to unsupported syntax).
  //
  // Production output is always emitted from HIR so that unsupported syntax is
  // surfaced as an error instead of silently falling back to a different
  // printer. The AST emitter is only used in tests via
  // `force_hir_emit_failure_for_tests` to validate parity between backends.
  let (emitted, backend) = if force_failure {
    let ast_output = emit_top_level_diagnostic(file, top_level_node, emit_opts.clone())
      .map_err(|diag| vec![diag])?;
    (ast_output, EmitBackend::Ast)
  } else {
    let lowered = lower_file(file, file_kind, top_level_node);
    match emit_hir_file_diagnostic(&lowered, emit_opts.clone()) {
      Ok(code) => (code, EmitBackend::Hir),
      Err(hir_diag) => return Err(vec![hir_diag]),
    }
  };

  #[cfg(all(test, feature = "emit-minify"))]
  set_last_emit_backend(backend);

  Ok((emitted, backend))
}

/// Minifies UTF-8 JavaScript or TypeScript code.
///
/// The input must be valid UTF-8; spans, identifiers, and renaming decisions
/// are computed over UTF-8 byte offsets. If you start from raw bytes, validate
/// them at the boundary and convert to a `&str` before calling this function.
///
/// # Arguments
///
/// * `top_level_mode` - How to parse the provided code.
/// * `source` - A string slice representing the source code to process.
/// * `output` - Destination to write output JavaScript code.
///
/// TypeScript/TSX inputs are parsed and stripped of type-only syntax before
/// minification so the emitted output is always valid JavaScript.
///
/// Returns `Ok(())` on success, or a list of diagnostics describing any
/// failures (e.g. parse errors).
///
/// # Examples
///
/// ```
/// use minify_js::{TopLevelMode, minify};
///
/// let code: &str = "const main = () => { let my_first_variable = 1; return my_first_variable; };";
/// let mut out = Vec::new();
/// minify(TopLevelMode::Global, code, &mut out).unwrap();
/// assert_eq!(out.as_slice(), b"const main=()=>{let a=1;return a;};");
/// ```
/// Options controlling how input is parsed before minification.
pub struct MinifyOptions {
  /// Whether to parse the file as a script or module.
  pub top_level_mode: TopLevelMode,
  /// Explicit parser dialect. When omitted, TypeScript is attempted first with
  /// a TSX fallback for JSX-heavy inputs.
  pub dialect: Option<Dialect>,
}

impl MinifyOptions {
  pub fn new(top_level_mode: TopLevelMode) -> Self {
    Self {
      top_level_mode,
      dialect: None,
    }
  }

  pub fn with_dialect(mut self, dialect: Dialect) -> Self {
    self.dialect = Some(dialect);
    self
  }
}

pub fn minify(
  top_level_mode: TopLevelMode,
  source: &str,
  output: &mut Vec<u8>,
) -> Result<(), Vec<Diagnostic>> {
  minify_with_options(MinifyOptions::new(top_level_mode), source, output)
}

pub fn minify_with_options(
  options: MinifyOptions,
  source: &str,
  output: &mut Vec<u8>,
) -> Result<(), Vec<Diagnostic>> {
  #[cfg(all(test, feature = "emit-minify"))]
  clear_last_emit_backend_for_tests();

  let file = FileId(0);
  let parse_dialects = match options.dialect {
    Some(dialect) => vec![dialect],
    None => vec![Dialect::Ts, Dialect::Tsx],
  };

  let mut last_error = None;
  let mut parsed = None;
  #[cfg(feature = "emit-minify")]
  let mut used_dialect = None;
  for dialect in parse_dialects {
    let parse_opts = ParseOptions {
      dialect,
      source_type: match options.top_level_mode {
        TopLevelMode::Global => SourceType::Script,
        TopLevelMode::Module => SourceType::Module,
      },
    };
    match parse_with_options(source, parse_opts) {
      Ok(ast) => {
        #[cfg(feature = "emit-minify")]
        {
          used_dialect = Some(dialect);
        }
        parsed = Some(ast);
        break;
      }
      Err(err) => last_error = Some(err),
    }
  }

  let mut top_level_node = match parsed {
    Some(ast) => ast,
    None => return Err(vec![last_error.unwrap().to_diagnostic(file)]),
  };
  #[cfg(feature = "emit-minify")]
  let used_dialect = used_dialect.expect("successful parse must set dialect");

  erase_types(file, options.top_level_mode, source, &mut top_level_node)?;

  let sem = {
    #[cfg(feature = "emit-minify")]
    {
      // Collect binding diagnostics before running AST-rewriting optimizations so
      // errors point at the original source.
      let (_sem, diagnostics) = bind_js(&mut top_level_node, options.top_level_mode, file);
      if !diagnostics.is_empty() {
        return Err(diagnostics);
      }

      opt::optimize(file, options.top_level_mode, &mut top_level_node);
      let (sem, diagnostics) = bind_js(&mut top_level_node, options.top_level_mode, file);
      if !diagnostics.is_empty() {
        return Err(diagnostics);
      }
      sem
    }
    #[cfg(not(feature = "emit-minify"))]
    {
      let (sem, diagnostics) = bind_js(&mut top_level_node, options.top_level_mode, file);
      if !diagnostics.is_empty() {
        return Err(diagnostics);
      }
      sem
    }
  };

  let usage = collect_usages(&mut top_level_node, &sem, options.top_level_mode);
  let renames = assign_names(&sem, &usage);
  #[cfg(feature = "emit-minify")]
  {
    apply_renames(&mut top_level_node, &renames);
    let file_kind = match used_dialect {
      Dialect::Js => FileKind::Js,
      Dialect::Jsx => FileKind::Jsx,
      Dialect::Ts => FileKind::Ts,
      Dialect::Tsx => FileKind::Tsx,
      Dialect::Dts => FileKind::Dts,
    };
    let emit_opts = EmitOptions::minified();
    let (emitted, _) = emit_minified(file, file_kind, &top_level_node, &emit_opts)?;
    output.clear();
    output.extend_from_slice(emitted.as_bytes());
    return Ok(());
  }
  #[cfg(not(feature = "emit-minify"))]
  {
    let mut replacements = apply_renames(&mut top_level_node, &renames);
    let result = rewrite_source(source, &mut replacements);
    output.clear();
    output.extend_from_slice(result.as_bytes());
    Ok(())
  }
}
