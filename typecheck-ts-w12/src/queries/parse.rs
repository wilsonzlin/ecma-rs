use crate::FileId;
use crate::Program;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use std::sync::Arc;

impl Program {
  pub fn parse(&self, file_id: FileId) -> Option<Arc<Node<TopLevel>>> {
    if let Some(existing) = self.parse_cache.borrow().get(&file_id) {
      return Some(existing.clone());
    }
    let file = self.file_record(file_id)?;
    match parse_js::parse(&file.text) {
      Ok(ast) => {
        let arc = Arc::new(ast);
        self.parse_cache.borrow_mut().insert(file_id, arc.clone());
        Some(arc)
      }
      Err(err) => {
        self.push_diagnostic(crate::diagnostics::Diagnostic::from_syntax_error(
          file_id, &err,
        ));
        None
      }
    }
  }
}
