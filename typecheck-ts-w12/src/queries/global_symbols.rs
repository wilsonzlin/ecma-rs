use crate::Program;
use semantic_js::GlobalSymbols;
use std::sync::Arc;

impl Program {
  pub fn global_symbols(&self) -> GlobalSymbols {
    if let Some(existing) = self.global_symbols.borrow().clone() {
      return existing;
    }

    let mut bound_files = Vec::new();
    for idx in 0..self.files.len() {
      let file_id = hir_js::FileId(idx as u32);
      if let Some(bound) = self.bind(file_id) {
        bound_files.push(bound);
      }
    }

    let bound_refs: Vec<Arc<_>> = bound_files.into_iter().collect();
    let globals = GlobalSymbols::from_bound_files(&bound_refs);
    self.global_symbols.borrow_mut().replace(globals.clone());
    globals
  }
}
