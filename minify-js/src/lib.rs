use optimize_js::Program;
use serialize::emit_js;
use err::MinifyError;
use parse_js::parse;

mod serialize;
mod err;
mod reconstruct;
#[cfg(test)]
mod tests;

use reconstruct::reconstruct_ast_from_program;
pub use symbol_js::TopLevelMode;
use symbol_js::compute_symbols;

/// Minifies UTF-8 JavaScript code, represented as an array of bytes.
///
/// # Arguments
///
/// * `top_level_mode` - How to parse the provided code.
/// * `source` - A slice of bytes representing the source code to minify.
/// * `output` - Destination to write minified output JavaScript code.
///
/// # Examples
///
/// ```
/// use minify_js::{Session, TopLevelMode, minify};
///
/// let mut code: &[u8] = b"const main = () => { let my_first_variable = 1; };";
/// let mut out = Vec::new();
/// minify(TopLevelMode::Global, code, &mut out).unwrap();
/// assert_eq!(out.as_slice(), b"const main=()=>{let a=1}");
/// ```
pub fn minify(
  top_level_mode: TopLevelMode,
  source: &[u8],
  output: &mut Vec<u8>,
) -> Result<(), MinifyError> {
  let mut top_level_node = parse(source).map_err(MinifyError::Syntax)?;
  compute_symbols(&mut top_level_node, top_level_mode);
  let program = Program::compile(top_level_node, false);
  let minified = reconstruct_ast_from_program(program);
  emit_js(output, &minified);
  Ok(())
}
