use hir_js::FileId;
use hir_js::FileKind;
use hir_js::HirFile;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::decl::VarDeclarator;
use parse_js::ast::stmt::Stmt;
use parse_js::loc::Loc;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DefId {
  pub file_id: FileId,
  pub index: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DefKind {
  TypeAlias,
  Interface,
  Enum,
  Class,
  Function,
  FunctionSignature,
  Var,
  Let,
  Const,
}

#[derive(Clone, Debug)]
pub enum DefSource {
  Stmt(usize),
  VarDecl { stmt: usize, decl: usize },
}

#[derive(Clone, Debug)]
pub struct DefInfo {
  pub id: DefId,
  pub name: String,
  pub kind: DefKind,
  pub span: Loc,
  pub source: DefSource,
}

#[derive(Clone, Debug)]
pub struct BoundFile {
  pub file_id: FileId,
  pub kind: FileKind,
  pub defs: Vec<DefInfo>,
}

impl BoundFile {
  pub fn new(file_id: FileId, kind: FileKind, defs: Vec<DefInfo>) -> Self {
    Self {
      file_id,
      kind,
      defs,
    }
  }

  pub fn get_def(&self, id: DefId) -> Option<&DefInfo> {
    if id.file_id == self.file_id {
      self.defs.get(id.index as usize)
    } else {
      None
    }
  }
}

#[derive(Default, Clone, Debug)]
pub struct GlobalSymbols {
  pub by_name: HashMap<String, Vec<DefId>>,
}

impl GlobalSymbols {
  pub fn from_bound_files(files: &[Arc<BoundFile>]) -> Self {
    let mut by_name: HashMap<String, Vec<DefId>> = HashMap::new();
    for file in files {
      for def in &file.defs {
        by_name.entry(def.name.clone()).or_default().push(def.id);
      }
    }
    GlobalSymbols { by_name }
  }

  pub fn lookup(&self, name: &str) -> Option<&[DefId]> {
    self.by_name.get(name).map(|v| v.as_slice())
  }
}

pub fn bind_file(hir: &HirFile) -> BoundFile {
  let mut defs = Vec::new();
  for (idx, stmt) in hir.ast.stx.body.iter().enumerate() {
    match &*stmt.stx {
      Stmt::TypeAliasDecl(alias) => {
        push_def(
          &mut defs,
          hir.file_id,
          DefKind::TypeAlias,
          alias.stx.name.clone(),
          stmt.loc,
          DefSource::Stmt(idx),
        );
      }
      Stmt::InterfaceDecl(interface) => {
        push_def(
          &mut defs,
          hir.file_id,
          DefKind::Interface,
          interface.stx.name.clone(),
          stmt.loc,
          DefSource::Stmt(idx),
        );
      }
      Stmt::EnumDecl(enum_decl) => {
        push_def(
          &mut defs,
          hir.file_id,
          DefKind::Enum,
          enum_decl.stx.name.clone(),
          stmt.loc,
          DefSource::Stmt(idx),
        );
      }
      Stmt::ClassDecl(class_decl) => {
        bind_class_decl(&mut defs, hir.file_id, class_decl, stmt.loc, idx)
      }
      Stmt::FunctionDecl(func_decl) => {
        bind_func_decl(&mut defs, hir.file_id, func_decl, stmt.loc, idx)
      }
      Stmt::AmbientVarDecl(ambient) => {
        push_def(
          &mut defs,
          hir.file_id,
          DefKind::Var,
          ambient.stx.name.clone(),
          stmt.loc,
          DefSource::Stmt(idx),
        );
      }
      Stmt::AmbientFunctionDecl(func) => {
        push_def(
          &mut defs,
          hir.file_id,
          DefKind::FunctionSignature,
          func.stx.name.clone(),
          stmt.loc,
          DefSource::Stmt(idx),
        );
      }
      Stmt::AmbientClassDecl(class_decl) => {
        push_def(
          &mut defs,
          hir.file_id,
          DefKind::Class,
          class_decl.stx.name.clone(),
          stmt.loc,
          DefSource::Stmt(idx),
        );
      }
      Stmt::VarDecl(var_decl) => bind_var_decl(&mut defs, hir.file_id, var_decl, stmt.loc, idx),
      _ => {}
    }
  }

  BoundFile::new(hir.file_id, hir.kind, defs)
}

fn push_def(
  defs: &mut Vec<DefInfo>,
  file_id: FileId,
  kind: DefKind,
  name: String,
  span: Loc,
  source: DefSource,
) {
  let id = DefId {
    file_id,
    index: defs.len() as u32,
  };
  defs.push(DefInfo {
    id,
    name,
    kind,
    span,
    source,
  });
}

fn bind_class_decl(
  defs: &mut Vec<DefInfo>,
  file_id: FileId,
  class_decl: &Node<ClassDecl>,
  span: Loc,
  stmt_idx: usize,
) {
  if let Some(name) = &class_decl.stx.name {
    push_def(
      defs,
      file_id,
      DefKind::Class,
      name.stx.name.clone(),
      span,
      DefSource::Stmt(stmt_idx),
    );
  }
}

fn bind_func_decl(
  defs: &mut Vec<DefInfo>,
  file_id: FileId,
  func_decl: &Node<FuncDecl>,
  span: Loc,
  stmt_idx: usize,
) {
  if let Some(name) = &func_decl.stx.name {
    let kind = if func_decl.stx.function.stx.body.is_some() {
      DefKind::Function
    } else {
      DefKind::FunctionSignature
    };
    push_def(
      defs,
      file_id,
      kind,
      name.stx.name.clone(),
      span,
      DefSource::Stmt(stmt_idx),
    );
  }
}

fn bind_var_decl(
  defs: &mut Vec<DefInfo>,
  file_id: FileId,
  var_decl: &Node<parse_js::ast::stmt::decl::VarDecl>,
  span: Loc,
  stmt_idx: usize,
) {
  for (decl_idx, declarator) in var_decl.stx.declarators.iter().enumerate() {
    if let Some((name, kind)) = var_decl_name_kind(var_decl, declarator) {
      push_def(
        defs,
        file_id,
        kind,
        name,
        span,
        DefSource::VarDecl {
          stmt: stmt_idx,
          decl: decl_idx,
        },
      );
    }
  }
}

fn var_decl_name_kind(
  var_decl: &Node<parse_js::ast::stmt::decl::VarDecl>,
  declarator: &VarDeclarator,
) -> Option<(String, DefKind)> {
  let name = match &*declarator.pattern.stx.pat.stx {
    Pat::Id(id) => id.stx.name.clone(),
    _ => return None,
  };
  let kind = match var_decl.stx.mode {
    VarDeclMode::Const => DefKind::Const,
    VarDeclMode::Let | VarDeclMode::AwaitUsing => DefKind::Let,
    _ => DefKind::Var,
  };
  Some((name, kind))
}
