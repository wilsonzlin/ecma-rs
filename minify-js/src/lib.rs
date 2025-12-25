pub use diagnostics::{Diagnostic, FileId, Severity, Span, TextRange};
#[cfg(feature = "emit-minify")]
use emit_js::{emit_top_level_diagnostic, EmitOptions};
use parse_js::parse;
#[cfg(not(feature = "emit-minify"))]
use rename::rewrite_source;
use rename::{apply_renames, assign_names, collect_usages};
use semantic_js::js::bind_js;
pub use semantic_js::js::TopLevelMode;

mod rename;
#[cfg(test)]
mod tests;

/// Minifies UTF-8 JavaScript code.
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
pub fn minify(
  top_level_mode: TopLevelMode,
  source: &str,
  output: &mut Vec<u8>,
) -> Result<(), Vec<Diagnostic>> {
  let mut top_level_node = parse(source).map_err(|err| vec![err.to_diagnostic(FileId(0))])?;
  let (sem, _) = bind_js(&mut top_level_node, top_level_mode);
  let usage = collect_usages(&mut top_level_node, &sem, top_level_mode);
  let renames = assign_names(&sem, &usage);
  #[cfg(feature = "emit-minify")]
  {
    apply_renames(&mut top_level_node, &renames);
    let emitted = emit_top_level_diagnostic(FileId(0), &top_level_node, EmitOptions::minified())
      .map_err(|diag| vec![diag])?;
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
