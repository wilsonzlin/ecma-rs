use err::MinifyError;
use parse_js::parse;
use rename::{apply_renames, assign_names, collect_usages, rewrite_source};
use symbol_js::compute_symbols;
pub use symbol_js::TopLevelMode;

mod err;
mod rename;
#[cfg(test)]
mod tests;

/// Minifies UTF-8 JavaScript code.
///
/// # Arguments
///
/// * `top_level_mode` - How to parse the provided code.
/// * `source` - A string slice representing the source code to process.
/// * `output` - Destination to write output JavaScript code.
///
/// # Examples
///
/// ```
/// use minify_js::{TopLevelMode, minify};
///
/// let code: &str = "const main = () => { let my_first_variable = 1; };";
/// let mut out = Vec::new();
/// minify(TopLevelMode::Global, code, &mut out).unwrap();
/// assert_eq!(out.as_slice(), b"const main = () => { let a = 1; };");
/// ```
pub fn minify(
  top_level_mode: TopLevelMode,
  source: &str,
  output: &mut Vec<u8>,
) -> Result<(), MinifyError> {
  let mut top_level_node = parse(source).map_err(MinifyError::Syntax)?;
  compute_symbols(&mut top_level_node, top_level_mode);
  let usage = collect_usages(&mut top_level_node, top_level_mode);
  let renames = assign_names(&usage);
  let mut replacements = apply_renames(&mut top_level_node, &renames);
  let result = rewrite_source(source, &mut replacements);
  output.clear();
  output.extend_from_slice(result.as_bytes());
  Ok(())
}
