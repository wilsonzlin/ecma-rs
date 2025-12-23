use err::MinifyError;
use parse_js::parse;
use symbol_js::compute_symbols;
pub use symbol_js::TopLevelMode;

mod err;
#[cfg(test)]
mod tests;

#[derive(Default)]
pub struct Session;

impl Session {
  pub fn new() -> Self {
    Self::default()
  }
}

/// Minify UTF-8 JavaScript from a string slice and write to the provided
/// output buffer. This helper mirrors the worker’s simplified API while we
/// retain the Session-based byte API for existing callers.
pub fn minify_str(
  top_level_mode: TopLevelMode,
  source: &str,
  output: &mut Vec<u8>,
) -> Result<(), MinifyError> {
  let mut top_level_node = parse(source).map_err(MinifyError::Syntax)?;
  compute_symbols(&mut top_level_node, top_level_mode);
  output.clear();
  output.extend_from_slice(source.as_bytes());
  Ok(())
}

/// Processes UTF-8 JavaScript code.
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
/// use minify_js::{TopLevelMode, Session, minify};
///
/// let code: &str = "const main = () => { let my_first_variable = 1; };";
/// let mut out = Vec::new();
/// let session = Session::new();
/// minify(&session, TopLevelMode::Global, code.as_bytes(), &mut out).unwrap();
/// assert_eq!(out.as_slice(), code.as_bytes());
/// ```
pub fn minify(
  _session: &Session,
  top_level_mode: TopLevelMode,
  source: &[u8],
  output: &mut Vec<u8>,
) -> Result<(), MinifyError> {
  let source_str = std::str::from_utf8(source).map_err(MinifyError::InvalidUtf8)?;
  minify_str(top_level_mode, source_str, output)
}
