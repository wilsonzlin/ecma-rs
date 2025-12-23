use tracing::instrument;

/// Identifier for a lowered body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BodyId(pub u32);

#[derive(Debug, Clone)]
pub struct HirFile {
  pub path: String,
  pub bodies: Vec<BodyId>,
  pub text_len: usize,
}

/// Lower a source file into a tiny HIR representation.
#[instrument(level = "info", skip(source), fields(file = %path))]
pub fn lower_to_hir(path: &str, source: &str) -> HirFile {
  // Count the number of bodies by looking for the `function` keyword.
  let function_count = source.matches("function").count() as u32;
  let body_count = function_count.max(1);
  let bodies = (0..body_count).map(BodyId).collect();
  HirFile {
    path: path.to_string(),
    bodies,
    text_len: source.len(),
  }
}
