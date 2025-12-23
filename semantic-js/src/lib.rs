use hir_js_trace23::BodyId;
use hir_js_trace23::HirFile;
use tracing::instrument;

#[derive(Debug, Clone)]
pub struct BoundFile {
  pub path: String,
  pub bodies: Vec<BodyId>,
  pub symbols: usize,
}

/// Bind a lowered file. The real implementation will build scopes and symbols;
/// here we keep it intentionally small while still emitting useful tracing.
#[instrument(level = "info", skip(file), fields(file = %file.path))]
pub fn bind_file(file: &HirFile) -> BoundFile {
  // Derive a stable symbol count from the file length so profiling has
  // something deterministic to report.
  let symbols = (file.text_len / 8).max(1);
  BoundFile {
    path: file.path.clone(),
    bodies: file.bodies.clone(),
    symbols,
  }
}
