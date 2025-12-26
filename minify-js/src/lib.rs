pub use diagnostics::{Diagnostic, FileId, Severity, Span, TextRange};
#[cfg(feature = "emit-minify")]
use emit_js::{
  emit_hir_file_diagnostic, emit_top_level_diagnostic, EmitOptions,
};
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
use ts_erase::erase_types;

pub use parse_js::Dialect;
mod rename;
#[cfg(test)]
mod tests;
mod ts_erase;

#[cfg(feature = "emit-minify")]
fn hir_can_emit(top: &Node<TopLevel>) -> bool {
  let _ = top;
  false
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
/// let code: &str = "const main = () => { let my_first_variable = 1; };";
/// let mut out = Vec::new();
/// minify(TopLevelMode::Global, code, &mut out).unwrap();
/// assert_eq!(out.as_slice(), b"const main=()=>{let a=1;};");
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

  erase_types(file, &mut top_level_node)?;

  let (sem, _) = bind_js(&mut top_level_node, options.top_level_mode);
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
    let emitted = if hir_can_emit(&top_level_node) {
      match emit_hir_file_diagnostic(&lower_file(file, file_kind, &top_level_node), emit_opts.clone()) {
        Ok(code) => code,
        Err(_) => emit_top_level_diagnostic(file, &top_level_node, emit_opts)
          .map_err(|diag| vec![diag])?,
      }
    } else {
      emit_top_level_diagnostic(file, &top_level_node, emit_opts).map_err(|diag| vec![diag])?
    };
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
