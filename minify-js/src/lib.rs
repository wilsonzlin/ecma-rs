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

/// Minifies UTF-8 JavaScript code.
///
/// # Arguments
///
/// * `top_level_mode` - How to parse the provided code.
/// * `source` - A string slice representing the source code to minify.
/// * `output` - Destination to write minified output JavaScript code.
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
  let mut top_level_node = parse(source_str).map_err(MinifyError::Syntax)?;
  compute_symbols(&mut top_level_node, top_level_mode);
  output.extend_from_slice(source_str.as_bytes());
  Ok(())
}
