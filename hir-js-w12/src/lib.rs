use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileKind {
  Js,
  Jsx,
  Ts,
  Tsx,
  Dts,
}

#[derive(Clone, Debug)]
pub struct HirFile {
  pub file_id: FileId,
  pub kind: FileKind,
  pub ast: Arc<Node<TopLevel>>,
}

impl HirFile {
  pub fn new(file_id: FileId, kind: FileKind, ast: Arc<Node<TopLevel>>) -> Self {
    HirFile { file_id, kind, ast }
  }
}

pub fn lower(file_id: FileId, kind: FileKind, ast: Arc<Node<TopLevel>>) -> HirFile {
  HirFile::new(file_id, kind, ast)
}
