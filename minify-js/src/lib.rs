use err::MinifyError;
use optimize_js::Program;
use parse_js::parse;
use serialize::emit_js;

mod err;
mod reconstruct;
mod serialize;
#[cfg(test)]
mod tests;

use reconstruct::reconstruct_ast_from_program;
use symbol_js::compute_symbols;
pub use symbol_js::TopLevelMode;

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
/// use minify_js::{TopLevelMode, minify};
///
/// let code: &str = "const main = () => { let my_first_variable = 1; };";
/// let mut out = Vec::new();
/// minify(TopLevelMode::Global, code, &mut out).unwrap();
/// assert_eq!(out.as_slice(), b"const main=()=>{let a=1}");
/// ```
pub fn minify(
  top_level_mode: TopLevelMode,
  source: &str,
  output: &mut Vec<u8>,
) -> Result<(), MinifyError> {
  let mut top_level_node = parse(source).map_err(MinifyError::Syntax)?;
  compute_symbols(&mut top_level_node, top_level_mode);
  let program = Program::compile(top_level_node, false);
  let minified = reconstruct_ast_from_program(program);
  emit_js(output, &minified);
  Ok(())
}
