use crate::intern::NameId;
use crate::intern::NameTable;
use bitflags::bitflags;
use hir_js_w8::DefId;
use hir_js_w8::ExprId;
use hir_js_w8::FileId;
use hir_js_w8::HirFile;
use hir_js_w8::TextRange;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScopeKind {
  Global,
  Module,
  Function,
  ArrowFunction,
  Class,
  Block,
  Catch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolKind {
  Var,
  Let,
  Const,
  Function,
  Class,
  Import,
  Param,
  Catch,
}

bitflags! {
  #[derive(Default, Clone, Copy, Debug, PartialEq, Eq, Hash)]
  pub struct SymbolFlags: u32 {
    const VAR = 1 << 0;
    const LET = 1 << 1;
    const CONST = 1 << 2;
    const FUNCTION = 1 << 3;
    const CLASS = 1 << 4;
    const IMPORT = 1 << 5;
    const PARAMETER = 1 << 6;
    const CATCH = 1 << 7;
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolData {
  pub name: NameId,
  pub kind: SymbolKind,
  pub flags: SymbolFlags,
  pub decls: Vec<DefId>,
  pub scope: ScopeId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopeData {
  pub parent: Option<ScopeId>,
  pub kind: ScopeKind,
  pub symbols: Vec<SymbolId>,
  pub symbol_map: FxHashMap<NameId, SymbolId>,
}

impl ScopeData {
  pub fn new(parent: Option<ScopeId>, kind: ScopeKind) -> Self {
    Self {
      parent,
      kind,
      symbols: Vec::new(),
      symbol_map: FxHashMap::default(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundFile {
  pub file: FileId,
  pub root_scope: ScopeId,
  pub scopes: Vec<ScopeData>,
  pub symbols: Vec<SymbolData>,
  pub uses: Vec<(ExprId, SymbolId)>,
  pub expr_scopes: FxHashMap<ExprId, ScopeId>,
  pub names: NameTable,
  pub def_spans: FxHashMap<DefId, TextRange>,
}

impl BoundFile {
  pub fn name(&self, id: NameId) -> Option<&str> {
    self.names.resolve(id)
  }
}

pub fn resolve_in_scope(bound: &BoundFile, mut scope: ScopeId, name: NameId) -> Option<SymbolId> {
  loop {
    let data = &bound.scopes[scope.0 as usize];
    if let Some(sym) = data.symbol_map.get(&name) {
      return Some(*sym);
    }
    match data.parent {
      Some(parent) => scope = parent,
      None => break,
    }
  }
  None
}

pub fn symbol_at_offset(bound: &BoundFile, hir: &HirFile, offset: u32) -> Option<SymbolId> {
  let mut best: Option<(TextRange, SymbolId)> = None;
  for (expr, sym) in bound.uses.iter().copied() {
    if let Some(range) = hir.expr_range(expr) {
      if range.contains(offset) {
        let update = match best {
          None => true,
          Some((current, _)) => range.len() <= current.len(),
        };
        if update {
          best = Some((range, sym));
        }
      }
    }
  }
  best.map(|(_, sym)| sym)
}
