use crate::FileId;
use crate::Program;
use semantic_js::BoundFile;
use std::sync::Arc;

impl Program {
  pub fn bind(&self, file_id: FileId) -> Option<Arc<BoundFile>> {
    if let Some(existing) = self.bind_cache.borrow().get(&file_id) {
      return Some(existing.clone());
    }
    let hir = self.hir(file_id)?;
    let bound = Arc::new(semantic_js::bind_file(&hir));
    self.bind_cache.borrow_mut().insert(file_id, bound.clone());
    Some(bound)
  }
}
