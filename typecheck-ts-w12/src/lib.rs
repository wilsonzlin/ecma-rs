mod diagnostics;
mod queries;
pub mod types;

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;
use types_ts::TypeStore;

#[derive(Clone, Copy, Debug)]
pub struct CompilerOptions {
  pub no_implicit_any: bool,
}

impl Default for CompilerOptions {
  fn default() -> Self {
    CompilerOptions {
      no_implicit_any: false,
    }
  }
}

struct FileRecord {
  kind: hir_js::FileKind,
  text: Arc<str>,
}

pub struct Program {
  options: CompilerOptions,
  files: Vec<FileRecord>,
  parse_cache:
    RefCell<HashMap<hir_js::FileId, Arc<parse_js::ast::node::Node<parse_js::ast::stx::TopLevel>>>>,
  hir_cache: RefCell<HashMap<hir_js::FileId, Arc<hir_js::HirFile>>>,
  bind_cache: RefCell<HashMap<hir_js::FileId, Arc<semantic_js::BoundFile>>>,
  global_symbols: RefCell<Option<semantic_js::GlobalSymbols>>,
  diagnostics: RefCell<Vec<diagnostics::Diagnostic>>,
  type_store: RefCell<TypeStore>,
}

impl Program {
  pub fn new(options: CompilerOptions) -> Self {
    Program {
      options,
      files: Vec::new(),
      parse_cache: RefCell::new(HashMap::new()),
      hir_cache: RefCell::new(HashMap::new()),
      bind_cache: RefCell::new(HashMap::new()),
      global_symbols: RefCell::new(None),
      diagnostics: RefCell::new(Vec::new()),
      type_store: RefCell::new(TypeStore::new()),
    }
  }

  pub fn add_file(&mut self, kind: hir_js::FileKind, text: impl Into<Arc<str>>) -> hir_js::FileId {
    let id = hir_js::FileId(self.files.len() as u32);
    self.files.push(FileRecord {
      kind,
      text: text.into(),
    });
    id
  }

  pub fn options(&self) -> &CompilerOptions {
    &self.options
  }

  pub fn diagnostics(&self) -> Vec<Diagnostic> {
    self.diagnostics.borrow().clone()
  }

  pub fn type_store(&self) -> std::cell::Ref<'_, TypeStore> {
    self.type_store.borrow()
  }

  pub(crate) fn type_store_mut(&self) -> std::cell::RefMut<'_, TypeStore> {
    self.type_store.borrow_mut()
  }

  pub(crate) fn push_diagnostic(&self, diagnostic: Diagnostic) {
    self.diagnostics.borrow_mut().push(diagnostic);
  }

  pub(crate) fn file_record(&self, file_id: FileId) -> Option<&FileRecord> {
    self.files.get(file_id.0 as usize)
  }
}

pub use diagnostics::Diagnostic;
pub use diagnostics::Span;
pub use hir_js::FileId;
pub use hir_js::FileKind;
pub use semantic_js::BoundFile;
pub use semantic_js::DefId;
pub use semantic_js::DefKind;
pub use semantic_js::GlobalSymbols;
pub use types_ts::TypeDisplay;
pub use types_ts::TypeId;
