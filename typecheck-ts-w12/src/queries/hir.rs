use crate::FileId;
use crate::Program;
use hir_js::HirFile;
use std::sync::Arc;

impl Program {
  pub fn hir(&self, file_id: FileId) -> Option<Arc<HirFile>> {
    if let Some(existing) = self.hir_cache.borrow().get(&file_id) {
      return Some(existing.clone());
    }
    let file = self.file_record(file_id)?;
    let ast = self.parse(file_id)?;
    let hir = Arc::new(hir_js::lower(file_id, file.kind, ast));
    self.hir_cache.borrow_mut().insert(file_id, hir.clone());
    Some(hir)
  }
}
