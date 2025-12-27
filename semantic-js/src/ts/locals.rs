use super::model::{Namespace, SymbolId, TsProgramSemantics};
use crate::assoc::ts::{
  self, declared_symbol, scope_id, DeclaredSymbol, ResolvedSymbol, ScopeInfo,
};
use crate::hash::stable_hash;
use derive_visitor::{Drive, DriveMut};
use diagnostics::{FileId, TextRange};
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat as AstPat};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::import_export::{ImportName, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::{VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  BlockStmt, CatchBlock, ForBody, ForInOfLhs, ForInStmt, ForOfStmt, ForTripleStmt,
  ForTripleStmtInit, Stmt as AstStmt,
};
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{ImportEqualsDecl, ModuleDecl, NamespaceDecl};
use parse_js::ast::type_expr::{
  TypeConstructor, TypeEntityName, TypeExpr, TypeFunction, TypeReference,
};
use std::collections::BTreeMap;

/// Deterministic identifier for a lexical scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ScopeId(pub u64);

impl ScopeId {
  pub fn raw(self) -> u64 {
    self.0
  }
}

impl Default for ScopeId {
  fn default() -> Self {
    ScopeId(0)
  }
}

/// Deterministic identifier for an interned name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub u64);

impl NameId {
  pub fn raw(self) -> u64 {
    self.0
  }
}

const LOCAL_SYMBOL_TAG: &str = "TS_LOCAL_SYMBOL";

fn name_id_for(file: FileId, name: &str) -> NameId {
  NameId(stable_hash(&(file, name)))
}

fn scope_id_for(
  file: FileId,
  parent: Option<ScopeId>,
  kind: ScopeKind,
  span: TextRange,
) -> ScopeId {
  ScopeId(stable_hash(&(
    file,
    parent.map(|p| p.raw()),
    kind,
    span.start,
    span.end,
  )))
}

fn symbol_id_for(file: FileId, scope: ScopeId, name: NameId, namespaces: Namespace) -> SymbolId {
  SymbolId(stable_hash(&(
    LOCAL_SYMBOL_TAG,
    file,
    scope.raw(),
    name.raw(),
    namespaces.bits(),
  )))
}

fn range_of<T: Drive + DriveMut>(node: &Node<T>) -> TextRange {
  TextRange::new(node.loc.0 as u32, node.loc.1 as u32)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScopeKind {
  Module,
  Script,
  Function,
  Block,
  Class,
  TypeParams,
}

impl ScopeKind {
  fn is_hoist_target(&self) -> bool {
    matches!(
      self,
      ScopeKind::Module | ScopeKind::Script | ScopeKind::Function | ScopeKind::Class
    )
  }
}

#[derive(Clone, Debug)]
pub struct ScopeData {
  pub parent: Option<ScopeId>,
  pub kind: ScopeKind,
  pub children: Vec<ScopeId>,
  bindings: BTreeMap<NameId, [Option<SymbolId>; 3]>,
}

impl ScopeData {
  fn new(parent: Option<ScopeId>, kind: ScopeKind) -> Self {
    Self {
      parent,
      kind,
      children: Vec::new(),
      bindings: BTreeMap::new(),
    }
  }
}

#[derive(Clone, Debug)]
pub struct SymbolData {
  pub id: SymbolId,
  pub name: NameId,
  pub namespaces: Namespace,
  pub decl_scope: ScopeId,
  pub span: Option<TextRange>,
}

/// Local TS semantics: lexical scopes, symbols, and side tables for identifier
/// and type resolutions keyed by their spans.
#[derive(Default, Debug)]
pub struct TsLocalSemantics {
  root: ScopeId,
  pub names: BTreeMap<NameId, String>,
  #[allow(dead_code)]
  name_lookup: BTreeMap<String, NameId>,
  pub scopes: BTreeMap<ScopeId, ScopeData>,
  pub symbols: BTreeMap<SymbolId, SymbolData>,
  expr_resolutions: BTreeMap<TextRange, SymbolId>,
  type_resolutions: BTreeMap<TextRange, SymbolId>,
}

impl TsLocalSemantics {
  /// The root scope for the file. This is always the first allocated scope.
  pub fn root_scope(&self) -> ScopeId {
    self.root
  }

  pub fn scope(&self, id: ScopeId) -> &ScopeData {
    self.scopes.get(&id).expect("scope exists for id")
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    self.symbols.get(&id).expect("symbol exists for id")
  }

  /// Resolve an expression in a lowered [`hir_js::hir::Body`] back to the local
  /// symbol it referenced, if any.
  pub fn resolve_expr(
    &self,
    body: &hir_js::hir::Body,
    expr: hir_js::ids::ExprId,
  ) -> Option<SymbolId> {
    let span = body.exprs[expr.0 as usize].span;
    self.expr_resolutions.get(&span).copied()
  }

  /// Resolve an expression span without requiring a lowered body reference.
  pub fn resolve_expr_span(&self, span: TextRange) -> Option<SymbolId> {
    self.expr_resolutions.get(&span).copied()
  }

  /// Resolve a type name in lowered HIR types.
  pub fn resolve_type_name(
    &self,
    types: &[hir_js::hir::TypeExpr],
    id: hir_js::ids::TypeExprId,
  ) -> Option<SymbolId> {
    let span = types[id.0 as usize].span;
    self.type_resolutions.get(&span).copied()
  }

  /// Resolve a type reference by its span.
  pub fn resolve_type_span(&self, span: TextRange) -> Option<SymbolId> {
    self.type_resolutions.get(&span).copied()
  }

  /// Resolve the smallest expression span containing the provided offset.
  pub fn resolve_expr_at_offset(&self, offset: u32) -> Option<(TextRange, SymbolId)> {
    resolve_span_at_offset(&self.expr_resolutions, offset)
  }

  /// Resolve the smallest type span containing the provided offset.
  pub fn resolve_type_at_offset(&self, offset: u32) -> Option<(TextRange, SymbolId)> {
    resolve_span_at_offset(&self.type_resolutions, offset)
  }

  /// All expression resolutions recorded for the file, sorted by span.
  pub fn expr_resolutions(&self) -> impl Iterator<Item = (&TextRange, &SymbolId)> {
    self.expr_resolutions.iter()
  }

  /// All type resolutions recorded for the file, sorted by span.
  pub fn type_resolutions(&self) -> impl Iterator<Item = (&TextRange, &SymbolId)> {
    self.type_resolutions.iter()
  }
}

fn resolve_span_at_offset(
  map: &BTreeMap<TextRange, SymbolId>,
  offset: u32,
) -> Option<(TextRange, SymbolId)> {
  map
    .iter()
    .filter(|(range, _)| {
      (range.start <= offset && offset < range.end) || (range.is_empty() && range.start == offset)
    })
    .min_by_key(|(range, sym)| (range.len(), range.start, range.end, sym.raw() as u32))
    .map(|(range, sym)| (*range, *sym))
}

/// Map module-scope local symbols to their program binder counterparts for the
/// same name/namespace, if available. Only symbols declared in the root scope
/// are considered; nested namespaces/modules and ambiguous namespace splits are
/// left unmapped because the program binder does not currently expose them.
pub fn map_module_scope_locals_to_program(
  locals: &TsLocalSemantics,
  program: &TsProgramSemantics,
  file: FileId,
) -> BTreeMap<SymbolId, SymbolId> {
  let mut mapping = BTreeMap::new();
  for (local_id, symbol) in locals.symbols.iter() {
    if symbol.decl_scope != locals.root_scope() {
      continue;
    }
    let Some(name) = locals.names.get(&symbol.name) else {
      continue;
    };
    let mut resolved = Vec::new();
    for ns in symbol.namespaces.iter_bits() {
      if let Some(sym) = program.resolve_in_module(file, name, ns) {
        resolved.push(sym);
      }
    }
    if let Some(first) = resolved.first().copied() {
      if resolved.iter().all(|sym| *sym == first) {
        mapping.insert(*local_id, first);
      }
    }
  }
  mapping
}

#[derive(Clone, Copy)]
enum DeclTarget {
  Lexical,
  Hoisted,
}

struct SemanticsBuilder {
  file: FileId,
  root: ScopeId,
  names: BTreeMap<NameId, String>,
  name_lookup: BTreeMap<String, NameId>,
  scopes: BTreeMap<ScopeId, ScopeData>,
  symbols: BTreeMap<SymbolId, SymbolData>,
}

impl SemanticsBuilder {
  fn new(file: FileId, kind: ScopeKind, span: TextRange) -> (Self, ScopeId) {
    let root_id = scope_id_for(file, None, kind, span);
    let mut scopes = BTreeMap::new();
    scopes.insert(root_id, ScopeData::new(None, kind));
    (
      Self {
        file,
        names: BTreeMap::new(),
        name_lookup: BTreeMap::new(),
        root: root_id,
        scopes,
        symbols: BTreeMap::new(),
      },
      root_id,
    )
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    let id = *self.name_lookup.entry(name.to_string()).or_insert_with(|| {
      let id = name_id_for(self.file, name);
      self.names.entry(id).or_insert_with(|| name.to_string());
      id
    });
    id
  }

  fn alloc_scope(&mut self, parent: ScopeId, kind: ScopeKind, span: TextRange) -> ScopeId {
    let id = scope_id_for(self.file, Some(parent), kind, span);
    self
      .scopes
      .entry(id)
      .or_insert_with(|| ScopeData::new(Some(parent), kind));
    if let Some(scope) = self.scopes.get_mut(&parent) {
      if !scope.children.contains(&id) {
        scope.children.push(id);
      }
    }
    id
  }

  fn alloc_symbol(
    &mut self,
    scope: ScopeId,
    name: NameId,
    namespaces: Namespace,
    span: Option<TextRange>,
  ) -> SymbolId {
    let id = symbol_id_for(self.file, scope, name, namespaces);
    self.symbols.entry(id).or_insert(SymbolData {
      id,
      name,
      namespaces,
      decl_scope: scope,
      span,
    });
    id
  }

  fn declare(
    &mut self,
    scope: ScopeId,
    name: &str,
    namespaces: Namespace,
    span: Option<TextRange>,
  ) -> SymbolId {
    let name_id = self.intern_name(name);
    let mut slots = self
      .scopes
      .get(&scope)
      .and_then(|s| s.bindings.get(&name_id).cloned())
      .unwrap_or([None, None, None]);
    let mut sym = None;
    for bit in namespaces.iter_bits() {
      if let Some(existing) = slots[ns_index(bit)] {
        sym = Some(existing);
        break;
      }
    }
    let sym = sym.unwrap_or_else(|| self.alloc_symbol(scope, name_id, namespaces, span));
    if let Some(data) = self.symbols.get_mut(&sym) {
      data.namespaces |= namespaces;
    }
    for bit in namespaces.iter_bits() {
      slots[ns_index(bit)] = Some(sym);
    }
    if let Some(scope) = self.scopes.get_mut(&scope) {
      scope.bindings.insert(name_id, slots);
    }
    sym
  }

  fn resolve(&self, scope: ScopeId, name: &str, ns: Namespace) -> Option<SymbolId> {
    let Some(name_id) = self.name_lookup.get(name) else {
      return None;
    };
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      let scope_data = self.scopes.get(&scope_id).expect("scope exists");
      if let Some(slots) = scope_data.bindings.get(name_id) {
        if let Some(sym) = slots[ns_index(ns)] {
          if self
            .symbols
            .get(&sym)
            .map(|s| s.namespaces.contains(ns))
            .unwrap_or(false)
          {
            return Some(sym);
          }
        }
      }
      current = scope_data.parent;
    }
    None
  }

  fn into_semantics(
    self,
    expr_resolutions: BTreeMap<TextRange, SymbolId>,
    type_resolutions: BTreeMap<TextRange, SymbolId>,
  ) -> TsLocalSemantics {
    TsLocalSemantics {
      root: self.root,
      names: self.names,
      name_lookup: self.name_lookup,
      scopes: self.scopes,
      symbols: self.symbols,
      expr_resolutions,
      type_resolutions,
    }
  }
}

/// Build deterministic TS local scopes and resolution tables for a parsed file.
pub fn bind_ts_locals(top: &mut Node<TopLevel>, file: FileId, is_module: bool) -> TsLocalSemantics {
  let kind = if is_module {
    ScopeKind::Module
  } else {
    ScopeKind::Script
  };
  let root_span = TextRange::new(top.loc.0 as u32, top.loc.1 as u32);
  let (builder, root) = SemanticsBuilder::new(file, kind, root_span);
  let mut decl = DeclarePass::new(builder, root);
  decl.walk_top(top);
  let builder = decl.finish();

  let (expr_resolutions, type_resolutions) = {
    let mut resolve = ResolvePass::new(&builder, root);
    resolve.walk_top(top);
    (resolve.expr_resolutions, resolve.type_resolutions)
  };
  builder.into_semantics(expr_resolutions, type_resolutions)
}

/// Build deterministic TS locals while storing attachments in side tables instead
/// of mutating [`NodeAssocData`].
pub fn bind_ts_locals_tables(
  top: &Node<TopLevel>,
  file: FileId,
  is_module: bool,
) -> (TsLocalSemantics, ts::TsAssocTables) {
  let kind = if is_module {
    ScopeKind::Module
  } else {
    ScopeKind::Script
  };
  let root_span = TextRange::new(top.loc.0 as u32, top.loc.1 as u32);
  let (builder, root) = SemanticsBuilder::new(file, kind, root_span);
  let (builder, tables) = {
    let mut decl = DeclareTablesPass::new(builder, root);
    decl.walk_top(top);
    decl.finish()
  };

  let (expr_resolutions, type_resolutions, tables) = {
    let mut resolve = ResolveTablesPass::new(&builder, root, tables);
    resolve.walk_top(top);
    (
      resolve.expr_resolutions,
      resolve.type_resolutions,
      resolve.tables,
    )
  };

  (
    builder.into_semantics(expr_resolutions, type_resolutions),
    tables,
  )
}

struct DeclarePass {
  builder: SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  decl_target: Vec<DeclTarget>,
}

impl DeclarePass {
  fn new(builder: SemanticsBuilder, root: ScopeId) -> Self {
    Self {
      builder,
      scope_stack: vec![root],
      decl_target: vec![DeclTarget::Lexical],
    }
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope(&mut self, kind: ScopeKind, span: TextRange) {
    let parent = self.current_scope();
    let id = self.builder.alloc_scope(parent, kind, span);
    self.scope_stack.push(id);
  }

  fn pop_scope(&mut self) {
    self.scope_stack.pop();
  }

  fn mark_scope(&self, assoc: &mut NodeAssocData) {
    assoc.set(ScopeInfo(self.current_scope()));
  }

  fn enter_decl_target(&mut self, target: DeclTarget) {
    self.decl_target.push(target);
  }

  fn exit_decl_target(&mut self) {
    self.decl_target.pop();
  }

  fn hoist_scope(&self) -> ScopeId {
    self
      .scope_stack
      .iter()
      .rev()
      .copied()
      .find(|scope| {
        self
          .builder
          .scopes
          .get(scope)
          .map(|s| s.kind.is_hoist_target())
          .unwrap_or(false)
      })
      .unwrap_or_else(|| self.current_scope())
  }

  fn declare(
    &mut self,
    assoc: &mut NodeAssocData,
    name: &str,
    namespaces: Namespace,
    span: Option<TextRange>,
  ) {
    let scope = match self
      .decl_target
      .last()
      .copied()
      .unwrap_or(DeclTarget::Lexical)
    {
      DeclTarget::Lexical => self.current_scope(),
      DeclTarget::Hoisted => self.hoist_scope(),
    };
    let sym = self.builder.declare(scope, name, namespaces, span);
    assoc.set(DeclaredSymbol(sym));
  }

  fn walk_top(&mut self, top: &mut Node<TopLevel>) {
    self.mark_scope(&mut top.assoc);
    for stmt in top.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_stmt(&mut self, stmt: &mut Node<AstStmt>) {
    self.mark_scope(&mut stmt.assoc);
    match &mut *stmt.stx {
      AstStmt::Block(block) => {
        self.push_scope(ScopeKind::Block, range_of(block));
        self.walk_block(block);
        self.pop_scope();
      }
      AstStmt::VarDecl(var) => self.walk_var_decl(var),
      AstStmt::FunctionDecl(func) => {
        if let Some(name) = &mut func.stx.name {
          self.declare(
            &mut name.assoc,
            &name.stx.name,
            Namespace::VALUE,
            Some(span_for_name(name.loc, &name.stx.name)),
          );
        }
        self.walk_func(&mut func.stx.function);
      }
      AstStmt::ClassDecl(class) => {
        if let Some(name) = &mut class.stx.name {
          self.declare(
            &mut name.assoc,
            &name.stx.name,
            Namespace::VALUE | Namespace::TYPE,
            Some(span_for_name(name.loc, &name.stx.name)),
          );
        }
        self.push_scope(ScopeKind::Class, range_of(class));
        for member in class.stx.members.iter_mut() {
          self.mark_scope(&mut member.assoc);
        }
        self.pop_scope();
      }
      AstStmt::Expr(expr) => self.walk_expr(&mut expr.stx.expr),
      AstStmt::Return(ret) => {
        if let Some(v) = &mut ret.stx.value {
          self.walk_expr(v);
        }
      }
      AstStmt::If(if_stmt) => {
        self.walk_expr(&mut if_stmt.stx.test);
        self.walk_stmt(&mut if_stmt.stx.consequent);
        if let Some(alt) = &mut if_stmt.stx.alternate {
          self.walk_stmt(alt);
        }
      }
      AstStmt::ForTriple(triple) => self.walk_for_triple(triple),
      AstStmt::ForIn(for_in) => self.walk_for_in(for_in),
      AstStmt::ForOf(for_of) => self.walk_for_of(for_of),
      AstStmt::Try(tr) => {
        self.walk_block_stmt(&mut tr.stx.wrapped);
        if let Some(catch) = &mut tr.stx.catch {
          self.walk_catch(catch);
        }
        if let Some(finally) = &mut tr.stx.finally {
          self.walk_block_stmt(finally);
        }
      }
      AstStmt::Switch(sw) => {
        self.walk_expr(&mut sw.stx.test);
        for branch in sw.stx.branches.iter_mut() {
          if let Some(case) = &mut branch.stx.case {
            self.walk_expr(case);
          }
          self.push_scope(ScopeKind::Block, range_of(branch));
          for stmt in branch.stx.body.iter_mut() {
            self.walk_stmt(stmt);
          }
          self.pop_scope();
        }
      }
      AstStmt::With(w) => {
        self.walk_expr(&mut w.stx.object);
        self.walk_stmt(&mut w.stx.body);
      }
      AstStmt::Label(label) => self.walk_stmt(&mut label.stx.statement),
      AstStmt::InterfaceDecl(intf) => {
        self.declare(
          &mut intf.assoc,
          &intf.stx.name,
          Namespace::TYPE,
          Some(span_for_name(intf.loc, &intf.stx.name)),
        );
        if let Some(params) = &mut intf.stx.type_parameters {
          self.push_scope(ScopeKind::TypeParams, to_range(intf.loc));
          for param in params.iter_mut() {
            self.walk_type_param(param);
          }
          self.pop_scope();
        }
        for ext in intf.stx.extends.iter_mut() {
          self.walk_type_expr(ext);
        }
      }
      AstStmt::TypeAliasDecl(alias) => {
        self.declare(
          &mut alias.assoc,
          &alias.stx.name,
          Namespace::TYPE,
          Some(span_for_name(alias.loc, &alias.stx.name)),
        );
        if let Some(params) = &mut alias.stx.type_parameters {
          self.push_scope(ScopeKind::TypeParams, to_range(alias.loc));
          for param in params.iter_mut() {
            self.walk_type_param(param);
          }
          self.walk_type_expr(&mut alias.stx.type_expr);
          self.pop_scope();
        } else {
          self.walk_type_expr(&mut alias.stx.type_expr);
        }
      }
      AstStmt::NamespaceDecl(ns) => self.walk_namespace(ns),
      AstStmt::ModuleDecl(module) => self.walk_module(module),
      AstStmt::Import(import) => self.walk_import(import),
      AstStmt::ImportEqualsDecl(import_equals) => self.walk_import_equals(import_equals),
      _ => {}
    }
  }

  fn walk_block_stmt(&mut self, block: &mut Node<BlockStmt>) {
    self.push_scope(ScopeKind::Block, range_of(block));
    self.walk_block(block);
    self.pop_scope();
  }

  fn walk_block(&mut self, block: &mut Node<BlockStmt>) {
    self.mark_scope(&mut block.assoc);
    for stmt in block.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_catch(&mut self, catch: &mut Node<CatchBlock>) {
    self.push_scope(ScopeKind::Block, range_of(catch));
    self.mark_scope(&mut catch.assoc);
    self.enter_decl_target(DeclTarget::Lexical);
    if let Some(param) = &mut catch.stx.parameter {
      self.walk_pat_decl(param, Namespace::VALUE);
    }
    for stmt in catch.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.exit_decl_target();
    self.pop_scope();
  }

  fn walk_for_body(&mut self, body: &mut Node<ForBody>) {
    self.push_scope(ScopeKind::Block, range_of(body));
    self.mark_scope(&mut body.assoc);
    for stmt in body.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope();
  }

  fn walk_for_triple(&mut self, triple: &mut Node<ForTripleStmt>) {
    self.mark_scope(&mut triple.assoc);
    match &mut triple.stx.init {
      ForTripleStmtInit::Expr(e) => self.walk_expr(e),
      ForTripleStmtInit::Decl(d) => self.walk_var_decl(d),
      ForTripleStmtInit::None => {}
    }
    if let Some(cond) = &mut triple.stx.cond {
      self.walk_expr(cond);
    }
    if let Some(post) = &mut triple.stx.post {
      self.walk_expr(post);
    }
    self.walk_for_body(&mut triple.stx.body);
  }

  fn walk_for_in(&mut self, for_in: &mut Node<ForInStmt>) {
    self.mark_scope(&mut for_in.assoc);
    match &mut for_in.stx.lhs {
      ForInOfLhs::Assign(pat) => self.walk_pat(pat, false, Namespace::VALUE),
      ForInOfLhs::Decl((mode, decl)) => {
        let target = if *mode == VarDeclMode::Var {
          DeclTarget::Hoisted
        } else {
          DeclTarget::Lexical
        };
        self.enter_decl_target(target);
        self.walk_pat_decl(decl, Namespace::VALUE);
        self.exit_decl_target();
      }
    }
    self.walk_expr(&mut for_in.stx.rhs);
    self.walk_for_body(&mut for_in.stx.body);
  }

  fn walk_for_of(&mut self, for_of: &mut Node<ForOfStmt>) {
    self.mark_scope(&mut for_of.assoc);
    match &mut for_of.stx.lhs {
      ForInOfLhs::Assign(pat) => self.walk_pat(pat, false, Namespace::VALUE),
      ForInOfLhs::Decl((mode, decl)) => {
        let target = if *mode == VarDeclMode::Var {
          DeclTarget::Hoisted
        } else {
          DeclTarget::Lexical
        };
        self.enter_decl_target(target);
        self.walk_pat_decl(decl, Namespace::VALUE);
        self.exit_decl_target();
      }
    }
    self.walk_expr(&mut for_of.stx.rhs);
    self.walk_for_body(&mut for_of.stx.body);
  }

  fn walk_var_decl(&mut self, var: &mut Node<VarDecl>) {
    self.mark_scope(&mut var.assoc);
    let target = if var.stx.mode == VarDeclMode::Var {
      DeclTarget::Hoisted
    } else {
      DeclTarget::Lexical
    };
    self.enter_decl_target(target);
    for decl in var.stx.declarators.iter_mut() {
      self.walk_pat_decl(&mut decl.pattern, Namespace::VALUE);
      if let Some(init) = &mut decl.initializer {
        self.walk_expr(init);
      }
      if let Some(annot) = &mut decl.type_annotation {
        self.walk_type_expr(annot);
      }
    }
    self.exit_decl_target();
  }

  fn walk_pat_decl(
    &mut self,
    decl: &mut Node<parse_js::ast::stmt::decl::PatDecl>,
    namespaces: Namespace,
  ) {
    self.mark_scope(&mut decl.assoc);
    self.walk_pat(&mut decl.stx.pat, true, namespaces);
  }

  fn walk_pat(&mut self, pat: &mut Node<AstPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(&mut pat.assoc);
    match &mut *pat.stx {
      AstPat::Id(id) => {
        if in_decl {
          self.declare(
            &mut id.assoc,
            &id.stx.name,
            namespaces,
            Some(span_for_name(pat.loc, &id.stx.name)),
          );
        }
      }
      AstPat::Arr(arr) => self.walk_arr_pat(arr, in_decl, namespaces),
      AstPat::Obj(obj) => self.walk_obj_pat(obj, in_decl, namespaces),
      AstPat::AssignTarget(expr) => self.walk_expr(expr),
    }
  }

  fn walk_arr_pat(&mut self, pat: &mut Node<ArrPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(&mut pat.assoc);
    for elem in pat.stx.elements.iter_mut().flatten() {
      self.walk_pat(&mut elem.target, in_decl, namespaces);
      if let Some(default) = &mut elem.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &mut pat.stx.rest {
      self.walk_pat(rest, in_decl, namespaces);
    }
  }

  fn walk_obj_pat(&mut self, pat: &mut Node<ObjPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(&mut pat.assoc);
    for prop in pat.stx.properties.iter_mut() {
      self.walk_pat(&mut prop.stx.target, in_decl, namespaces);
      if let Some(default) = &mut prop.stx.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &mut pat.stx.rest {
      self.walk_pat(rest, in_decl, namespaces);
    }
  }

  fn walk_expr(&mut self, expr: &mut Node<AstExpr>) {
    self.mark_scope(&mut expr.assoc);
    match &mut *expr.stx {
      AstExpr::Binary(bin) => {
        self.walk_expr(&mut bin.stx.left);
        self.walk_expr(&mut bin.stx.right);
      }
      AstExpr::Call(call) => {
        self.walk_expr(&mut call.stx.callee);
        for arg in call.stx.arguments.iter_mut() {
          self.walk_expr(&mut arg.stx.value);
        }
      }
      AstExpr::Member(mem) => self.walk_expr(&mut mem.stx.left),
      AstExpr::Cond(cond) => {
        self.walk_expr(&mut cond.stx.test);
        self.walk_expr(&mut cond.stx.consequent);
        self.walk_expr(&mut cond.stx.alternate);
      }
      AstExpr::Func(func) => self.walk_func(&mut func.stx.func),
      AstExpr::ArrowFunc(arrow) => self.walk_func(&mut arrow.stx.func),
      AstExpr::Class(class) => {
        self.push_scope(ScopeKind::Class, range_of(class));
        if let Some(name) = &mut class.stx.name {
          self.declare(
            &mut name.assoc,
            &name.stx.name,
            Namespace::VALUE | Namespace::TYPE,
            Some(to_range(name.loc)),
          );
        }
        self.pop_scope();
      }
      AstExpr::ArrPat(arr) => self.walk_arr_pat(arr, false, Namespace::VALUE),
      AstExpr::ObjPat(obj) => self.walk_obj_pat(obj, false, Namespace::VALUE),
      AstExpr::TaggedTemplate(tag) => {
        self.walk_expr(&mut tag.stx.function);
        for part in tag.stx.parts.iter_mut() {
          if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
            self.walk_expr(expr);
          }
        }
      }
      AstExpr::LitArr(arr) => {
        for elem in arr.stx.elements.iter_mut() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(e)
            | parse_js::ast::expr::lit::LitArrElem::Rest(e) => self.walk_expr(e),
            parse_js::ast::expr::lit::LitArrElem::Empty => {}
          }
        }
      }
      AstExpr::LitObj(obj) => {
        for member in obj.stx.members.iter_mut() {
          self.mark_scope(&mut member.assoc);
        }
      }
      AstExpr::Unary(unary) => self.walk_expr(&mut unary.stx.argument),
      AstExpr::UnaryPostfix(post) => self.walk_expr(&mut post.stx.argument),
      AstExpr::ComputedMember(mem) => {
        self.walk_expr(&mut mem.stx.object);
        self.walk_expr(&mut mem.stx.member);
      }
      _ => {}
    }
  }

  fn walk_func(&mut self, func: &mut Node<Func>) {
    self.push_scope(ScopeKind::Function, range_of(func));
    self.mark_scope(&mut func.assoc);
    self.enter_decl_target(DeclTarget::Hoisted);
    if let Some(params) = &mut func.stx.type_parameters {
      for param in params.iter_mut() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter_mut() {
      self.walk_pat_decl(&mut param.stx.pattern, Namespace::VALUE);
      if let Some(default) = &mut param.stx.default_value {
        self.walk_expr(default);
      }
      if let Some(ty) = &mut param.stx.type_annotation {
        self.walk_type_expr(ty);
      }
    }
    if let Some(ret) = &mut func.stx.return_type {
      self.walk_type_expr(ret);
    }
    if let Some(body) = &mut func.stx.body {
      match body {
        FuncBody::Block(stmts) => {
          for stmt in stmts.iter_mut() {
            self.walk_stmt(stmt);
          }
        }
        FuncBody::Expression(expr) => self.walk_expr(expr),
      }
    }
    self.exit_decl_target();
    self.pop_scope();
  }

  fn walk_type_param(&mut self, param: &mut Node<parse_js::ast::type_expr::TypeParameter>) {
    self.mark_scope(&mut param.assoc);
    self.declare(
      &mut param.assoc,
      &param.stx.name,
      Namespace::TYPE,
      Some(span_for_name(param.loc, &param.stx.name)),
    );
    if let Some(constraint) = &mut param.stx.constraint {
      self.walk_type_expr(constraint);
    }
    if let Some(default) = &mut param.stx.default {
      self.walk_type_expr(default);
    }
  }

  fn walk_type_expr(&mut self, ty: &mut Node<TypeExpr>) {
    self.mark_scope(&mut ty.assoc);
    match &mut *ty.stx {
      TypeExpr::TypeReference(reference) => self.walk_type_reference(reference),
      TypeExpr::ArrayType(arr) => self.walk_type_expr(&mut arr.stx.element_type),
      TypeExpr::UnionType(union) => {
        for t in union.stx.types.iter_mut() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::IntersectionType(inter) => {
        for t in inter.stx.types.iter_mut() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::ParenthesizedType(par) => self.walk_type_expr(&mut par.stx.type_expr),
      TypeExpr::FunctionType(func) => self.walk_type_function(func),
      TypeExpr::ConstructorType(func) => self.walk_constructor_type(func),
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter_mut() {
          self.walk_type_expr(&mut elem.stx.type_expr);
        }
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter_mut() {
          self.mark_scope(&mut member.assoc);
        }
      }
      TypeExpr::TypeQuery(query) => {
        self.resolve_type_entity_name(&query.stx.expr_name);
      }
      TypeExpr::KeyOfType(k) => self.walk_type_expr(&mut k.stx.type_expr),
      TypeExpr::IndexedAccessType(idx) => {
        self.walk_type_expr(&mut idx.stx.object_type);
        self.walk_type_expr(&mut idx.stx.index_type);
      }
      TypeExpr::ConditionalType(cond) => {
        self.walk_type_expr(&mut cond.stx.check_type);
        self.walk_type_expr(&mut cond.stx.extends_type);
        self.walk_type_expr(&mut cond.stx.true_type);
        self.walk_type_expr(&mut cond.stx.false_type);
      }
      TypeExpr::MappedType(mapped) => {
        self.push_scope(ScopeKind::TypeParams, to_range(mapped.loc));
        self.declare(
          &mut mapped.assoc,
          &mapped.stx.type_parameter,
          Namespace::TYPE,
          Some(span_for_name(mapped.loc, &mapped.stx.type_parameter)),
        );
        self.walk_type_expr(&mut mapped.stx.constraint);
        if let Some(name) = &mut mapped.stx.name_type {
          self.walk_type_expr(name);
        }
        self.walk_type_expr(&mut mapped.stx.type_expr);
        self.pop_scope();
      }
      TypeExpr::TemplateLiteralType(tmpl) => {
        for span in tmpl.stx.spans.iter_mut() {
          self.walk_type_expr(&mut span.stx.type_expr);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(annot) = &mut pred.stx.type_annotation {
          self.walk_type_expr(annot);
        }
      }
      TypeExpr::InferType(infer) => {
        self.declare(
          &mut infer.assoc,
          &infer.stx.type_parameter,
          Namespace::TYPE,
          Some(span_for_name(infer.loc, &infer.stx.type_parameter)),
        );
        if let Some(cons) = &mut infer.stx.constraint {
          self.walk_type_expr(cons);
        }
      }
      TypeExpr::ImportType(import) => {
        if let Some(qual) = &import.stx.qualifier {
          self.resolve_type_entity_name(qual);
        }
        if let Some(args) = &mut import.stx.type_arguments {
          for arg in args.iter_mut() {
            self.walk_type_expr(arg);
          }
        }
      }
      _ => {}
    }
  }

  fn walk_type_function(&mut self, func: &mut Node<TypeFunction>) {
    self.push_scope(ScopeKind::TypeParams, range_of(func));
    self.mark_scope(&mut func.assoc);
    if let Some(params) = &mut func.stx.type_parameters {
      for param in params.iter_mut() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter_mut() {
      self.walk_type_expr(&mut param.stx.type_expr);
    }
    self.walk_type_expr(&mut func.stx.return_type);
    self.pop_scope();
  }

  fn walk_constructor_type(&mut self, func: &mut Node<TypeConstructor>) {
    self.push_scope(ScopeKind::TypeParams, range_of(func));
    self.mark_scope(&mut func.assoc);
    if let Some(params) = &mut func.stx.type_parameters {
      for param in params.iter_mut() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter_mut() {
      self.walk_type_expr(&mut param.stx.type_expr);
    }
    self.walk_type_expr(&mut func.stx.return_type);
    self.pop_scope();
  }

  fn walk_type_reference(&mut self, reference: &mut Node<TypeReference>) {
    self.mark_scope(&mut reference.assoc);
    if let Some(args) = &mut reference.stx.type_arguments {
      for arg in args.iter_mut() {
        self.walk_type_expr(arg);
      }
    }
  }

  fn resolve_type_entity_name(&mut self, name: &TypeEntityName) {
    if let TypeEntityName::Qualified(q) = name {
      self.resolve_type_entity_name(&q.left);
    }
  }

  fn walk_namespace(&mut self, ns: &mut Node<NamespaceDecl>) {
    self.declare(
      &mut ns.assoc,
      &ns.stx.name,
      Namespace::VALUE | Namespace::NAMESPACE,
      Some(span_for_name(ns.loc, &ns.stx.name)),
    );
    match &mut ns.stx.body {
      parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
        self.push_scope(ScopeKind::Block, to_range(ns.loc));
        self.mark_scope(&mut ns.assoc);
        for stmt in body.iter_mut() {
          self.walk_stmt(stmt);
        }
        self.pop_scope();
      }
      parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
    }
  }

  fn walk_module(&mut self, module: &mut Node<ModuleDecl>) {
    let name = match &module.stx.name {
      parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.as_str(),
      parse_js::ast::ts_stmt::ModuleName::String(s) => s.as_str(),
    };
    self.declare(
      &mut module.assoc,
      name,
      Namespace::VALUE | Namespace::NAMESPACE,
      Some(span_for_name(module.loc, name)),
    );
    if let Some(body) = &mut module.stx.body {
      self.push_scope(ScopeKind::Module, to_range(module.loc));
      self.mark_scope(&mut module.assoc);
      for stmt in body.iter_mut() {
        self.walk_stmt(stmt);
      }
      self.pop_scope();
    }
  }

  fn walk_import(&mut self, import: &mut Node<parse_js::ast::stmt::ImportStmt>) {
    self.mark_scope(&mut import.assoc);
    let base_ns = if import.stx.type_only {
      Namespace::TYPE
    } else {
      Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
    };
    if let Some(default) = &mut import.stx.default {
      self.walk_pat_decl(default, base_ns);
    }
    if let Some(names) = &mut import.stx.names {
      match names {
        ImportNames::All(pat) => self.walk_pat_decl(pat, base_ns),
        ImportNames::Specific(list) => {
          for item in list.iter_mut() {
            let ns = if item.stx.type_only {
              Namespace::TYPE
            } else {
              base_ns
            };
            self.walk_import_name(item, ns);
          }
        }
      }
    }
  }

  fn walk_import_name(&mut self, name: &mut Node<ImportName>, ns: Namespace) {
    self.mark_scope(&mut name.assoc);
    self.walk_pat_decl(&mut name.stx.alias, ns);
    if let AstPat::Id(id) = &mut *name.stx.alias.stx.pat.stx {
      self.declare(&mut id.assoc, &id.stx.name, ns, Some(to_range(name.loc)));
    }
  }

  fn walk_import_equals(&mut self, import: &mut Node<ImportEqualsDecl>) {
    self.mark_scope(&mut import.assoc);
    let namespaces = Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE;
    self.declare(
      &mut import.assoc,
      &import.stx.name,
      namespaces,
      Some(span_for_name(import.loc, &import.stx.name)),
    );
  }

  fn finish(self) -> SemanticsBuilder {
    self.builder
  }
}

struct ResolvePass<'a> {
  builder: &'a SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  expr_resolutions: BTreeMap<TextRange, SymbolId>,
  type_resolutions: BTreeMap<TextRange, SymbolId>,
}

impl<'a> ResolvePass<'a> {
  fn new(builder: &'a SemanticsBuilder, root: ScopeId) -> Self {
    Self {
      builder,
      scope_stack: vec![root],
      expr_resolutions: BTreeMap::new(),
      type_resolutions: BTreeMap::new(),
    }
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope_from_assoc(&mut self, assoc: &NodeAssocData) {
    if let Some(id) = scope_id(assoc) {
      if self.scope_stack.last().copied() != Some(id) {
        self.scope_stack.push(id);
      }
    }
  }

  fn pop_scope_from_assoc(&mut self, assoc: &NodeAssocData) {
    if let Some(id) = scope_id(assoc) {
      if self.scope_stack.last().copied() == Some(id) {
        self.scope_stack.pop();
      }
    }
  }

  fn walk_top(&mut self, top: &mut Node<TopLevel>) {
    self.push_scope_from_assoc(&top.assoc);
    for stmt in top.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_from_assoc(&top.assoc);
  }

  fn walk_stmt(&mut self, stmt: &mut Node<AstStmt>) {
    self.push_scope_from_assoc(&stmt.assoc);
    match &mut *stmt.stx {
      AstStmt::Block(block) => {
        self.walk_block(block);
      }
      AstStmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter_mut() {
          self.walk_pat_decl(&mut decl.pattern);
          if let Some(annot) = &mut decl.type_annotation {
            self.walk_type_expr(annot);
          }
          if let Some(init) = &mut decl.initializer {
            self.walk_expr(init);
          }
        }
      }
      AstStmt::FunctionDecl(func) => {
        if let Some(name) = &mut func.stx.name {
          if let Some(sym) = declared_symbol(&name.assoc) {
            self
              .expr_resolutions
              .insert(span_for_name(name.loc, &name.stx.name), sym);
          }
        }
        self.walk_func(&mut func.stx.function);
      }
      AstStmt::ClassDecl(class) => {
        if let Some(name) = &mut class.stx.name {
          if let Some(sym) = declared_symbol(&name.assoc) {
            self
              .expr_resolutions
              .insert(span_for_name(name.loc, &name.stx.name), sym);
          }
        }
        for member in class.stx.members.iter_mut() {
          self.push_scope_from_assoc(&member.assoc);
          self.pop_scope_from_assoc(&member.assoc);
        }
      }
      AstStmt::Expr(expr) => self.walk_expr(&mut expr.stx.expr),
      AstStmt::Return(ret) => {
        if let Some(v) = &mut ret.stx.value {
          self.walk_expr(v);
        }
      }
      AstStmt::If(if_stmt) => {
        self.walk_expr(&mut if_stmt.stx.test);
        self.walk_stmt(&mut if_stmt.stx.consequent);
        if let Some(alt) = &mut if_stmt.stx.alternate {
          self.walk_stmt(alt);
        }
      }
      AstStmt::ForTriple(triple) => {
        match &mut triple.stx.init {
          ForTripleStmtInit::Expr(e) => self.walk_expr(e),
          ForTripleStmtInit::Decl(d) => {
            for decl in d.stx.declarators.iter_mut() {
              self.walk_pat_decl(&mut decl.pattern);
              if let Some(init) = &mut decl.initializer {
                self.walk_expr(init);
              }
            }
          }
          ForTripleStmtInit::None => {}
        }
        if let Some(cond) = &mut triple.stx.cond {
          self.walk_expr(cond);
        }
        if let Some(post) = &mut triple.stx.post {
          self.walk_expr(post);
        }
        self.walk_for_body(&mut triple.stx.body);
      }
      AstStmt::ForIn(for_in) => {
        match &mut for_in.stx.lhs {
          ForInOfLhs::Assign(pat) => self.walk_pat(pat),
          ForInOfLhs::Decl((_, decl)) => self.walk_pat_decl(decl),
        }
        self.walk_expr(&mut for_in.stx.rhs);
        self.walk_for_body(&mut for_in.stx.body);
      }
      AstStmt::ForOf(for_of) => {
        match &mut for_of.stx.lhs {
          ForInOfLhs::Assign(pat) => self.walk_pat(pat),
          ForInOfLhs::Decl((_, decl)) => self.walk_pat_decl(decl),
        }
        self.walk_expr(&mut for_of.stx.rhs);
        self.walk_for_body(&mut for_of.stx.body);
      }
      AstStmt::Try(tr) => {
        self.walk_block_stmt(&mut tr.stx.wrapped);
        if let Some(catch) = &mut tr.stx.catch {
          if let Some(param) = &mut catch.stx.parameter {
            self.walk_pat_decl(param);
          }
          for stmt in catch.stx.body.iter_mut() {
            self.walk_stmt(stmt);
          }
        }
        if let Some(finally) = &mut tr.stx.finally {
          self.walk_block_stmt(finally);
        }
      }
      AstStmt::Switch(sw) => {
        self.walk_expr(&mut sw.stx.test);
        for branch in sw.stx.branches.iter_mut() {
          if let Some(case) = &mut branch.stx.case {
            self.walk_expr(case);
          }
          for stmt in branch.stx.body.iter_mut() {
            self.walk_stmt(stmt);
          }
        }
      }
      AstStmt::With(w) => {
        self.walk_expr(&mut w.stx.object);
        self.walk_stmt(&mut w.stx.body);
      }
      AstStmt::InterfaceDecl(intf) => {
        if let Some(sym) = declared_symbol(&intf.assoc) {
          self
            .expr_resolutions
            .insert(span_for_name(intf.loc, &intf.stx.name), sym);
        }
        for ext in intf.stx.extends.iter_mut() {
          self.walk_type_expr(ext);
        }
      }
      AstStmt::TypeAliasDecl(alias) => {
        if let Some(sym) = declared_symbol(&alias.assoc) {
          self
            .expr_resolutions
            .insert(span_for_name(alias.loc, &alias.stx.name), sym);
        }
        self.walk_type_expr(&mut alias.stx.type_expr);
      }
      AstStmt::NamespaceDecl(ns) => match &mut ns.stx.body {
        parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
          for stmt in body.iter_mut() {
            self.walk_stmt(stmt);
          }
        }
        parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
      },
      AstStmt::ModuleDecl(module) => {
        if let Some(body) = &mut module.stx.body {
          for stmt in body.iter_mut() {
            self.walk_stmt(stmt);
          }
        }
      }
      AstStmt::Import(import) => {
        if let Some(default) = &mut import.stx.default {
          self.walk_pat_decl(default);
        }
        if let Some(names) = &mut import.stx.names {
          match names {
            ImportNames::All(pat) => self.walk_pat_decl(pat),
            ImportNames::Specific(list) => {
              for item in list.iter_mut() {
                self.walk_import_name(item);
              }
            }
          }
        }
      }
      AstStmt::ImportEqualsDecl(import) => {
        if let Some(sym) = declared_symbol(&import.assoc) {
          let span = span_for_name(import.loc, &import.stx.name);
          self.expr_resolutions.insert(span, sym);
        }
      }
      _ => {}
    }
    self.pop_scope_from_assoc(&stmt.assoc);
  }

  fn walk_namespace(&mut self, ns: &mut Node<NamespaceDecl>) {
    self.push_scope_from_assoc(&ns.assoc);
    match &mut ns.stx.body {
      parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
        for stmt in body.iter_mut() {
          self.walk_stmt(stmt);
        }
      }
      parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
    }
    self.pop_scope_from_assoc(&ns.assoc);
  }

  fn walk_block_stmt(&mut self, block: &mut Node<BlockStmt>) {
    self.push_scope_from_assoc(&block.assoc);
    for stmt in block.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_from_assoc(&block.assoc);
  }

  fn walk_block(&mut self, block: &mut Node<BlockStmt>) {
    for stmt in block.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_for_body(&mut self, body: &mut Node<ForBody>) {
    self.push_scope_from_assoc(&body.assoc);
    for stmt in body.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_from_assoc(&body.assoc);
  }

  fn walk_pat_decl(&mut self, decl: &mut Node<parse_js::ast::stmt::decl::PatDecl>) {
    self.walk_pat(&mut decl.stx.pat);
  }

  fn walk_pat(&mut self, pat: &mut Node<AstPat>) {
    match &mut *pat.stx {
      AstPat::Id(id) => {
        if declared_symbol(&id.assoc).is_none() {
          let span = span_for_name(pat.loc, &id.stx.name);
          let sym = self
            .builder
            .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
          id.assoc.set(ResolvedSymbol(sym));
          if let Some(sym) = sym {
            self.expr_resolutions.insert(span, sym);
          }
        } else if let Some(sym) = declared_symbol(&id.assoc) {
          id.assoc.set(ResolvedSymbol(Some(sym)));
          self
            .expr_resolutions
            .insert(span_for_name(pat.loc, &id.stx.name), sym);
        }
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter_mut().flatten() {
          self.walk_pat(&mut elem.target);
          if let Some(default) = &mut elem.default_value {
            self.walk_expr(default);
          }
        }
        if let Some(rest) = &mut arr.stx.rest {
          self.walk_pat(rest);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter_mut() {
          self.walk_pat(&mut prop.stx.target);
          if let Some(default) = &mut prop.stx.default_value {
            self.walk_expr(default);
          }
        }
        if let Some(rest) = &mut obj.stx.rest {
          self.walk_pat(rest);
        }
      }
      AstPat::AssignTarget(expr) => self.walk_expr(expr),
    }
  }

  fn walk_arr_pat_expr(&mut self, pat: &mut Node<ArrPat>) {
    for elem in pat.stx.elements.iter_mut().flatten() {
      self.walk_pat(&mut elem.target);
      if let Some(default) = &mut elem.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &mut pat.stx.rest {
      self.walk_pat(rest);
    }
  }

  fn walk_obj_pat_expr(&mut self, pat: &mut Node<ObjPat>) {
    for prop in pat.stx.properties.iter_mut() {
      self.walk_pat(&mut prop.stx.target);
      if let Some(default) = &mut prop.stx.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &mut pat.stx.rest {
      self.walk_pat(rest);
    }
  }

  fn walk_expr(&mut self, expr: &mut Node<AstExpr>) {
    match &mut *expr.stx {
      AstExpr::Id(id) => {
        let span = span_for_name(expr.loc, &id.stx.name);
        let sym = self
          .builder
          .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
        expr.assoc.set(ResolvedSymbol(sym));
        if let Some(sym) = sym {
          self.expr_resolutions.insert(span, sym);
        }
      }
      AstExpr::Binary(bin) => {
        self.walk_expr(&mut bin.stx.left);
        self.walk_expr(&mut bin.stx.right);
      }
      AstExpr::Call(call) => {
        self.walk_expr(&mut call.stx.callee);
        for arg in call.stx.arguments.iter_mut() {
          self.walk_expr(&mut arg.stx.value);
        }
      }
      AstExpr::Member(mem) => self.walk_expr(&mut mem.stx.left),
      AstExpr::Cond(cond) => {
        self.walk_expr(&mut cond.stx.test);
        self.walk_expr(&mut cond.stx.consequent);
        self.walk_expr(&mut cond.stx.alternate);
      }
      AstExpr::Func(func) => self.walk_func(&mut func.stx.func),
      AstExpr::ArrowFunc(arrow) => self.walk_func(&mut arrow.stx.func),
      AstExpr::Class(class) => {
        if let Some(name) = &class.stx.name {
          let span = to_range(name.loc);
          let sym = self
            .builder
            .resolve(self.current_scope(), &name.stx.name, Namespace::VALUE);
          class.assoc.set(ResolvedSymbol(sym));
          if let Some(sym) = sym {
            self.expr_resolutions.insert(span, sym);
          }
        }
      }
      AstExpr::ArrPat(arr) => self.walk_arr_pat_expr(arr),
      AstExpr::ObjPat(obj) => self.walk_obj_pat_expr(obj),
      AstExpr::TaggedTemplate(tag) => {
        self.walk_expr(&mut tag.stx.function);
        for part in tag.stx.parts.iter_mut() {
          if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
            self.walk_expr(expr);
          }
        }
      }
      AstExpr::LitArr(arr) => {
        for elem in arr.stx.elements.iter_mut() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(e)
            | parse_js::ast::expr::lit::LitArrElem::Rest(e) => self.walk_expr(e),
            parse_js::ast::expr::lit::LitArrElem::Empty => {}
          }
        }
      }
      AstExpr::LitObj(obj) => {
        for member in obj.stx.members.iter_mut() {
          self.push_scope_from_assoc(&member.assoc);
          if let ObjMemberType::Shorthand { id } = &mut member.stx.typ {
            let span = span_for_name(id.loc, &id.stx.name);
            let sym = self
              .builder
              .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
            id.assoc.set(ResolvedSymbol(sym));
            if let Some(sym) = sym {
              self.expr_resolutions.insert(span, sym);
            }
          }
          self.pop_scope_from_assoc(&member.assoc);
        }
      }
      AstExpr::Unary(unary) => self.walk_expr(&mut unary.stx.argument),
      AstExpr::UnaryPostfix(post) => self.walk_expr(&mut post.stx.argument),
      AstExpr::ComputedMember(mem) => {
        self.walk_expr(&mut mem.stx.object);
        self.walk_expr(&mut mem.stx.member);
      }
      _ => {}
    }
  }

  fn walk_func(&mut self, func: &mut Node<Func>) {
    self.push_scope_from_assoc(&func.assoc);
    if let Some(params) = &mut func.stx.type_parameters {
      for param in params.iter_mut() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter_mut() {
      self.walk_pat_decl(&mut param.stx.pattern);
      if let Some(default) = &mut param.stx.default_value {
        self.walk_expr(default);
      }
      if let Some(ty) = &mut param.stx.type_annotation {
        self.walk_type_expr(ty);
      }
    }
    if let Some(ret) = &mut func.stx.return_type {
      self.walk_type_expr(ret);
    }
    if let Some(body) = &mut func.stx.body {
      match body {
        FuncBody::Block(stmts) => {
          for stmt in stmts.iter_mut() {
            self.walk_stmt(stmt);
          }
        }
        FuncBody::Expression(expr) => self.walk_expr(expr),
      }
    }
    self.pop_scope_from_assoc(&func.assoc);
  }

  fn walk_type_param(&mut self, param: &mut Node<parse_js::ast::type_expr::TypeParameter>) {
    self.push_scope_from_assoc(&param.assoc);
    if let Some(sym) = declared_symbol(&param.assoc) {
      self
        .expr_resolutions
        .insert(span_for_name(param.loc, &param.stx.name), sym);
    }
    if let Some(constraint) = &mut param.stx.constraint {
      self.walk_type_expr(constraint);
    }
    if let Some(default) = &mut param.stx.default {
      self.walk_type_expr(default);
    }
    self.pop_scope_from_assoc(&param.assoc);
  }

  fn walk_type_expr(&mut self, ty: &mut Node<TypeExpr>) {
    match &mut *ty.stx {
      TypeExpr::TypeReference(reference) => {
        let span = to_range(ty.loc);
        if let Some(sym) = self.resolve_type_reference(reference) {
          self.type_resolutions.insert(span, sym);
        }
        if let Some(args) = &mut reference.stx.type_arguments {
          for arg in args.iter_mut() {
            self.walk_type_expr(arg);
          }
        }
      }
      TypeExpr::ArrayType(arr) => self.walk_type_expr(&mut arr.stx.element_type),
      TypeExpr::UnionType(union) => {
        for t in union.stx.types.iter_mut() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::IntersectionType(inter) => {
        for t in inter.stx.types.iter_mut() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::ParenthesizedType(par) => self.walk_type_expr(&mut par.stx.type_expr),
      TypeExpr::FunctionType(func) => self.walk_type_function(func),
      TypeExpr::ConstructorType(func) => self.walk_constructor_type(func),
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter_mut() {
          self.walk_type_expr(&mut elem.stx.type_expr);
        }
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter_mut() {
          self.push_scope_from_assoc(&member.assoc);
          self.pop_scope_from_assoc(&member.assoc);
        }
      }
      TypeExpr::TypeQuery(query) => {
        let sym = self.resolve_type_query_entity_name(&query.stx.expr_name);
        query.assoc.set(ResolvedSymbol(sym));
        ty.assoc.set(ResolvedSymbol(sym));
        if let Some(sym) = sym {
          self.type_resolutions.insert(to_range(ty.loc), sym);
        }
      }
      TypeExpr::KeyOfType(k) => self.walk_type_expr(&mut k.stx.type_expr),
      TypeExpr::IndexedAccessType(idx) => {
        self.walk_type_expr(&mut idx.stx.object_type);
        self.walk_type_expr(&mut idx.stx.index_type);
      }
      TypeExpr::ConditionalType(cond) => {
        self.walk_type_expr(&mut cond.stx.check_type);
        self.walk_type_expr(&mut cond.stx.extends_type);
        self.walk_type_expr(&mut cond.stx.true_type);
        self.walk_type_expr(&mut cond.stx.false_type);
      }
      TypeExpr::MappedType(mapped) => {
        self.walk_type_expr(&mut mapped.stx.constraint);
        if let Some(name) = &mut mapped.stx.name_type {
          self.walk_type_expr(name);
        }
        self.walk_type_expr(&mut mapped.stx.type_expr);
      }
      TypeExpr::TemplateLiteralType(tmpl) => {
        for span in tmpl.stx.spans.iter_mut() {
          self.walk_type_expr(&mut span.stx.type_expr);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(annot) = &mut pred.stx.type_annotation {
          self.walk_type_expr(annot);
        }
      }
      TypeExpr::InferType(infer) => {
        if let Some(cons) = &mut infer.stx.constraint {
          self.walk_type_expr(cons);
        }
      }
      TypeExpr::ImportType(import) => {
        if let Some(args) = &mut import.stx.type_arguments {
          for arg in args.iter_mut() {
            self.walk_type_expr(arg);
          }
        }
      }
      _ => {}
    }
  }

  fn resolve_entity_name(
    &self,
    name: &TypeEntityName,
    ident_namespace: Namespace,
    qualified_namespace: Namespace,
  ) -> Option<SymbolId> {
    match name {
      TypeEntityName::Identifier(name) => {
        self
          .builder
          .resolve(self.current_scope(), name.as_str(), ident_namespace)
      }
      TypeEntityName::Qualified(q) => {
        self.resolve_entity_name(&q.left, qualified_namespace, qualified_namespace)
      }
      TypeEntityName::Import(_) => None,
    }
  }

  fn resolve_type_query_entity_name(&self, name: &TypeEntityName) -> Option<SymbolId> {
    self.resolve_entity_name(name, Namespace::VALUE, Namespace::VALUE)
  }

  fn resolve_type_reference(&self, reference: &Node<TypeReference>) -> Option<SymbolId> {
    self.resolve_entity_name(&reference.stx.name, Namespace::TYPE, Namespace::NAMESPACE)
  }

  fn resolve_type_entity_name(&self, name: &TypeEntityName) -> Option<SymbolId> {
    self.resolve_entity_name(name, Namespace::TYPE, Namespace::NAMESPACE)
  }

  fn walk_type_function(&mut self, func: &mut Node<TypeFunction>) {
    for param in func.stx.parameters.iter_mut() {
      self.walk_type_expr(&mut param.stx.type_expr);
    }
    self.walk_type_expr(&mut func.stx.return_type);
  }

  fn walk_constructor_type(&mut self, func: &mut Node<TypeConstructor>) {
    for param in func.stx.parameters.iter_mut() {
      self.walk_type_expr(&mut param.stx.type_expr);
    }
    self.walk_type_expr(&mut func.stx.return_type);
  }

  fn walk_import_name(&mut self, name: &mut Node<ImportName>) {
    self.walk_pat_decl(&mut name.stx.alias);
  }
}

struct DeclareTablesPass {
  builder: SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  decl_target: Vec<DeclTarget>,
  tables: ts::TsAssocTables,
}

impl DeclareTablesPass {
  fn new(builder: SemanticsBuilder, root: ScopeId) -> Self {
    Self {
      builder,
      scope_stack: vec![root],
      decl_target: vec![DeclTarget::Lexical],
      tables: ts::TsAssocTables::default(),
    }
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope(&mut self, kind: ScopeKind, span: TextRange) {
    let parent = self.current_scope();
    let id = self.builder.alloc_scope(parent, kind, span);
    self.scope_stack.push(id);
  }

  fn pop_scope(&mut self) {
    self.scope_stack.pop();
  }

  fn mark_scope<T: Drive + DriveMut>(&mut self, node: &Node<T>) {
    self.tables.record_scope(node.loc, self.current_scope());
  }

  fn enter_decl_target(&mut self, target: DeclTarget) {
    self.decl_target.push(target);
  }

  fn exit_decl_target(&mut self) {
    self.decl_target.pop();
  }

  fn hoist_scope(&self) -> ScopeId {
    self
      .scope_stack
      .iter()
      .rev()
      .copied()
      .find(|scope| {
        self
          .builder
          .scopes
          .get(scope)
          .map(|s| s.kind.is_hoist_target())
          .unwrap_or(false)
      })
      .unwrap_or_else(|| self.current_scope())
  }

  fn declare(&mut self, name: &str, namespaces: Namespace, span: TextRange) -> SymbolId {
    let scope = match self
      .decl_target
      .last()
      .copied()
      .unwrap_or(DeclTarget::Lexical)
    {
      DeclTarget::Lexical => self.current_scope(),
      DeclTarget::Hoisted => self.hoist_scope(),
    };
    let sym = self.builder.declare(scope, name, namespaces, Some(span));
    self.tables.record_declared_symbol(span, sym);
    sym
  }

  fn walk_top(&mut self, top: &Node<TopLevel>) {
    self.mark_scope(top);
    for stmt in top.stx.body.iter() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_stmt(&mut self, stmt: &Node<AstStmt>) {
    self.mark_scope(stmt);
    match &*stmt.stx {
      AstStmt::Block(block) => {
        self.push_scope(ScopeKind::Block, range_of(block));
        self.walk_block(block);
        self.pop_scope();
      }
      AstStmt::VarDecl(var) => self.walk_var_decl(var),
      AstStmt::FunctionDecl(func) => {
        if let Some(name) = &func.stx.name {
          self.declare(
            &name.stx.name,
            Namespace::VALUE,
            span_for_name(name.loc, &name.stx.name),
          );
        }
        self.walk_func(&func.stx.function);
      }
      AstStmt::ClassDecl(class) => {
        if let Some(name) = &class.stx.name {
          self.declare(
            &name.stx.name,
            Namespace::VALUE | Namespace::TYPE,
            span_for_name(name.loc, &name.stx.name),
          );
        }
        self.push_scope(ScopeKind::Class, range_of(class));
        for member in class.stx.members.iter() {
          self.mark_scope(member);
        }
        self.pop_scope();
      }
      AstStmt::Expr(expr) => self.walk_expr(&expr.stx.expr),
      AstStmt::Return(ret) => {
        if let Some(v) = &ret.stx.value {
          self.walk_expr(v);
        }
      }
      AstStmt::If(if_stmt) => {
        self.walk_expr(&if_stmt.stx.test);
        self.walk_stmt(&if_stmt.stx.consequent);
        if let Some(alt) = &if_stmt.stx.alternate {
          self.walk_stmt(alt);
        }
      }
      AstStmt::ForTriple(triple) => self.walk_for_triple(triple),
      AstStmt::ForIn(for_in) => self.walk_for_in(for_in),
      AstStmt::ForOf(for_of) => self.walk_for_of(for_of),
      AstStmt::Try(tr) => {
        self.walk_block_stmt(&tr.stx.wrapped);
        if let Some(catch) = &tr.stx.catch {
          self.walk_catch(catch);
        }
        if let Some(finally) = &tr.stx.finally {
          self.walk_block_stmt(finally);
        }
      }
      AstStmt::Switch(sw) => {
        self.walk_expr(&sw.stx.test);
        for branch in sw.stx.branches.iter() {
          if let Some(case) = &branch.stx.case {
            self.walk_expr(case);
          }
          self.push_scope(ScopeKind::Block, range_of(branch));
          for stmt in branch.stx.body.iter() {
            self.walk_stmt(stmt);
          }
          self.pop_scope();
        }
      }
      AstStmt::With(w) => {
        self.walk_expr(&w.stx.object);
        self.walk_stmt(&w.stx.body);
      }
      AstStmt::Label(label) => self.walk_stmt(&label.stx.statement),
      AstStmt::InterfaceDecl(intf) => {
        self.declare(
          &intf.stx.name,
          Namespace::TYPE,
          span_for_name(intf.loc, &intf.stx.name),
        );
        if let Some(params) = &intf.stx.type_parameters {
          self.push_scope(ScopeKind::TypeParams, to_range(intf.loc));
          for param in params.iter() {
            self.walk_type_param(param);
          }
          self.pop_scope();
        }
        for ext in intf.stx.extends.iter() {
          self.walk_type_expr(ext);
        }
      }
      AstStmt::TypeAliasDecl(alias) => {
        self.declare(
          &alias.stx.name,
          Namespace::TYPE,
          span_for_name(alias.loc, &alias.stx.name),
        );
        if let Some(params) = &alias.stx.type_parameters {
          self.push_scope(ScopeKind::TypeParams, to_range(alias.loc));
          for param in params.iter() {
            self.walk_type_param(param);
          }
          self.walk_type_expr(&alias.stx.type_expr);
          self.pop_scope();
        } else {
          self.walk_type_expr(&alias.stx.type_expr);
        }
      }
      AstStmt::NamespaceDecl(ns) => self.walk_namespace(ns),
      AstStmt::ModuleDecl(module) => self.walk_module(module),
      AstStmt::Import(import) => self.walk_import(import),
      _ => {}
    }
  }

  fn walk_block_stmt(&mut self, block: &Node<BlockStmt>) {
    self.push_scope(ScopeKind::Block, range_of(block));
    self.walk_block(block);
    self.pop_scope();
  }

  fn walk_block(&mut self, block: &Node<BlockStmt>) {
    self.mark_scope(block);
    for stmt in block.stx.body.iter() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_catch(&mut self, catch: &Node<CatchBlock>) {
    self.push_scope(ScopeKind::Block, range_of(catch));
    self.mark_scope(catch);
    self.enter_decl_target(DeclTarget::Lexical);
    if let Some(param) = &catch.stx.parameter {
      self.walk_pat_decl(param, Namespace::VALUE);
    }
    for stmt in catch.stx.body.iter() {
      self.walk_stmt(stmt);
    }
    self.exit_decl_target();
    self.pop_scope();
  }

  fn walk_for_body(&mut self, body: &Node<ForBody>) {
    self.push_scope(ScopeKind::Block, range_of(body));
    self.mark_scope(body);
    for stmt in body.stx.body.iter() {
      self.walk_stmt(stmt);
    }
    self.pop_scope();
  }

  fn walk_for_triple(&mut self, triple: &Node<ForTripleStmt>) {
    self.mark_scope(triple);
    match &triple.stx.init {
      ForTripleStmtInit::Expr(e) => self.walk_expr(e),
      ForTripleStmtInit::Decl(d) => self.walk_var_decl(d),
      ForTripleStmtInit::None => {}
    }
    if let Some(cond) = &triple.stx.cond {
      self.walk_expr(cond);
    }
    if let Some(post) = &triple.stx.post {
      self.walk_expr(post);
    }
    self.walk_for_body(&triple.stx.body);
  }

  fn walk_for_in(&mut self, for_in: &Node<ForInStmt>) {
    self.mark_scope(for_in);
    match &for_in.stx.lhs {
      ForInOfLhs::Assign(pat) => self.walk_pat(pat, false, Namespace::VALUE),
      ForInOfLhs::Decl((mode, decl)) => {
        let target = if *mode == VarDeclMode::Var {
          DeclTarget::Hoisted
        } else {
          DeclTarget::Lexical
        };
        self.enter_decl_target(target);
        self.walk_pat_decl(decl, Namespace::VALUE);
        self.exit_decl_target();
      }
    }
    self.walk_expr(&for_in.stx.rhs);
    self.walk_for_body(&for_in.stx.body);
  }

  fn walk_for_of(&mut self, for_of: &Node<ForOfStmt>) {
    self.mark_scope(for_of);
    match &for_of.stx.lhs {
      ForInOfLhs::Assign(pat) => self.walk_pat(pat, false, Namespace::VALUE),
      ForInOfLhs::Decl((mode, decl)) => {
        let target = if *mode == VarDeclMode::Var {
          DeclTarget::Hoisted
        } else {
          DeclTarget::Lexical
        };
        self.enter_decl_target(target);
        self.walk_pat_decl(decl, Namespace::VALUE);
        self.exit_decl_target();
      }
    }
    self.walk_expr(&for_of.stx.rhs);
    self.walk_for_body(&for_of.stx.body);
  }

  fn walk_var_decl(&mut self, var: &Node<VarDecl>) {
    self.mark_scope(var);
    let target = if var.stx.mode == VarDeclMode::Var {
      DeclTarget::Hoisted
    } else {
      DeclTarget::Lexical
    };
    self.enter_decl_target(target);
    for decl in var.stx.declarators.iter() {
      self.walk_pat_decl(&decl.pattern, Namespace::VALUE);
      if let Some(init) = &decl.initializer {
        self.walk_expr(init);
      }
      if let Some(annot) = &decl.type_annotation {
        self.walk_type_expr(annot);
      }
    }
    self.exit_decl_target();
  }

  fn walk_pat_decl(
    &mut self,
    decl: &Node<parse_js::ast::stmt::decl::PatDecl>,
    namespaces: Namespace,
  ) {
    self.mark_scope(decl);
    self.walk_pat(&decl.stx.pat, true, namespaces);
  }

  fn walk_pat(&mut self, pat: &Node<AstPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(pat);
    match &*pat.stx {
      AstPat::Id(id) => {
        if in_decl {
          self.declare(
            &id.stx.name,
            namespaces,
            span_for_name(pat.loc, &id.stx.name),
          );
        }
      }
      AstPat::Arr(arr) => self.walk_arr_pat(arr, in_decl, namespaces),
      AstPat::Obj(obj) => self.walk_obj_pat(obj, in_decl, namespaces),
      AstPat::AssignTarget(expr) => self.walk_expr(expr),
    }
  }

  fn walk_arr_pat(&mut self, pat: &Node<ArrPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(pat);
    for elem in pat.stx.elements.iter().flatten() {
      self.walk_pat(&elem.target, in_decl, namespaces);
      if let Some(default) = &elem.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &pat.stx.rest {
      self.walk_pat(rest, in_decl, namespaces);
    }
  }

  fn walk_obj_pat(&mut self, pat: &Node<ObjPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(pat);
    for prop in pat.stx.properties.iter() {
      self.walk_pat(&prop.stx.target, in_decl, namespaces);
      if let Some(default) = &prop.stx.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &pat.stx.rest {
      self.walk_pat(rest, in_decl, namespaces);
    }
  }

  fn walk_expr(&mut self, expr: &Node<AstExpr>) {
    self.mark_scope(expr);
    match &*expr.stx {
      AstExpr::Binary(bin) => {
        self.walk_expr(&bin.stx.left);
        self.walk_expr(&bin.stx.right);
      }
      AstExpr::Call(call) => {
        self.walk_expr(&call.stx.callee);
        for arg in call.stx.arguments.iter() {
          self.walk_expr(&arg.stx.value);
        }
      }
      AstExpr::Member(mem) => self.walk_expr(&mem.stx.left),
      AstExpr::Cond(cond) => {
        self.walk_expr(&cond.stx.test);
        self.walk_expr(&cond.stx.consequent);
        self.walk_expr(&cond.stx.alternate);
      }
      AstExpr::Func(func) => self.walk_func(&func.stx.func),
      AstExpr::ArrowFunc(arrow) => self.walk_func(&arrow.stx.func),
      AstExpr::Class(class) => {
        self.push_scope(ScopeKind::Class, range_of(class));
        if let Some(name) = &class.stx.name {
          self.declare(
            &name.stx.name,
            Namespace::VALUE | Namespace::TYPE,
            to_range(name.loc),
          );
        }
        self.pop_scope();
      }
      AstExpr::ArrPat(arr) => self.walk_arr_pat(arr, false, Namespace::VALUE),
      AstExpr::ObjPat(obj) => self.walk_obj_pat(obj, false, Namespace::VALUE),
      AstExpr::TaggedTemplate(tag) => {
        self.walk_expr(&tag.stx.function);
        for part in tag.stx.parts.iter() {
          if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
            self.walk_expr(expr);
          }
        }
      }
      AstExpr::LitArr(arr) => {
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(e)
            | parse_js::ast::expr::lit::LitArrElem::Rest(e) => self.walk_expr(e),
            parse_js::ast::expr::lit::LitArrElem::Empty => {}
          }
        }
      }
      AstExpr::LitObj(obj) => {
        for member in obj.stx.members.iter() {
          self.mark_scope(member);
        }
      }
      AstExpr::Unary(unary) => self.walk_expr(&unary.stx.argument),
      AstExpr::UnaryPostfix(post) => self.walk_expr(&post.stx.argument),
      AstExpr::ComputedMember(mem) => {
        self.walk_expr(&mem.stx.object);
        self.walk_expr(&mem.stx.member);
      }
      _ => {}
    }
  }

  fn walk_func(&mut self, func: &Node<Func>) {
    self.push_scope(ScopeKind::Function, range_of(func));
    self.mark_scope(func);
    self.enter_decl_target(DeclTarget::Hoisted);
    if let Some(params) = &func.stx.type_parameters {
      for param in params.iter() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter() {
      self.walk_pat_decl(&param.stx.pattern, Namespace::VALUE);
      if let Some(default) = &param.stx.default_value {
        self.walk_expr(default);
      }
      if let Some(ty) = &param.stx.type_annotation {
        self.walk_type_expr(ty);
      }
    }
    if let Some(ret) = &func.stx.return_type {
      self.walk_type_expr(ret);
    }
    if let Some(body) = &func.stx.body {
      match body {
        FuncBody::Block(stmts) => {
          for stmt in stmts.iter() {
            self.walk_stmt(stmt);
          }
        }
        FuncBody::Expression(expr) => self.walk_expr(expr),
      }
    }
    self.exit_decl_target();
    self.pop_scope();
  }

  fn walk_type_param(&mut self, param: &Node<parse_js::ast::type_expr::TypeParameter>) {
    self.mark_scope(param);
    self.declare(
      &param.stx.name,
      Namespace::TYPE,
      span_for_name(param.loc, &param.stx.name),
    );
    if let Some(constraint) = &param.stx.constraint {
      self.walk_type_expr(constraint);
    }
    if let Some(default) = &param.stx.default {
      self.walk_type_expr(default);
    }
  }

  fn walk_type_expr(&mut self, ty: &Node<TypeExpr>) {
    self.mark_scope(ty);
    match &*ty.stx {
      TypeExpr::TypeReference(reference) => self.walk_type_reference(reference),
      TypeExpr::ArrayType(arr) => self.walk_type_expr(&arr.stx.element_type),
      TypeExpr::UnionType(union) => {
        for t in union.stx.types.iter() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::IntersectionType(inter) => {
        for t in inter.stx.types.iter() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::ParenthesizedType(par) => self.walk_type_expr(&par.stx.type_expr),
      TypeExpr::FunctionType(func) => self.walk_type_function(func),
      TypeExpr::ConstructorType(func) => self.walk_constructor_type(func),
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter() {
          self.walk_type_expr(&elem.stx.type_expr);
        }
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter() {
          self.mark_scope(member);
        }
      }
      TypeExpr::TypeQuery(query) => {
        self.resolve_type_entity_name(&query.stx.expr_name);
      }
      TypeExpr::KeyOfType(k) => self.walk_type_expr(&k.stx.type_expr),
      TypeExpr::IndexedAccessType(idx) => {
        self.walk_type_expr(&idx.stx.object_type);
        self.walk_type_expr(&idx.stx.index_type);
      }
      TypeExpr::ConditionalType(cond) => {
        self.walk_type_expr(&cond.stx.check_type);
        self.walk_type_expr(&cond.stx.extends_type);
        self.walk_type_expr(&cond.stx.true_type);
        self.walk_type_expr(&cond.stx.false_type);
      }
      TypeExpr::MappedType(mapped) => {
        self.push_scope(ScopeKind::TypeParams, to_range(mapped.loc));
        self.declare(
          &mapped.stx.type_parameter,
          Namespace::TYPE,
          span_for_name(mapped.loc, &mapped.stx.type_parameter),
        );
        self.walk_type_expr(&mapped.stx.constraint);
        if let Some(name) = &mapped.stx.name_type {
          self.walk_type_expr(name);
        }
        self.walk_type_expr(&mapped.stx.type_expr);
        self.pop_scope();
      }
      TypeExpr::TemplateLiteralType(tmpl) => {
        for span in tmpl.stx.spans.iter() {
          self.walk_type_expr(&span.stx.type_expr);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(annot) = &pred.stx.type_annotation {
          self.walk_type_expr(annot);
        }
      }
      TypeExpr::InferType(infer) => {
        self.declare(
          &infer.stx.type_parameter,
          Namespace::TYPE,
          span_for_name(infer.loc, &infer.stx.type_parameter),
        );
        if let Some(cons) = &infer.stx.constraint {
          self.walk_type_expr(cons);
        }
      }
      TypeExpr::ImportType(import) => {
        if let Some(qual) = &import.stx.qualifier {
          self.resolve_type_entity_name(qual);
        }
        if let Some(args) = &import.stx.type_arguments {
          for arg in args.iter() {
            self.walk_type_expr(arg);
          }
        }
      }
      _ => {}
    }
  }

  fn walk_type_function(&mut self, func: &Node<TypeFunction>) {
    self.push_scope(ScopeKind::TypeParams, range_of(func));
    self.mark_scope(func);
    if let Some(params) = &func.stx.type_parameters {
      for param in params.iter() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter() {
      self.walk_type_expr(&param.stx.type_expr);
    }
    self.walk_type_expr(&func.stx.return_type);
    self.pop_scope();
  }

  fn walk_constructor_type(&mut self, func: &Node<TypeConstructor>) {
    self.push_scope(ScopeKind::TypeParams, range_of(func));
    self.mark_scope(func);
    if let Some(params) = &func.stx.type_parameters {
      for param in params.iter() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter() {
      self.walk_type_expr(&param.stx.type_expr);
    }
    self.walk_type_expr(&func.stx.return_type);
    self.pop_scope();
  }

  fn walk_type_reference(&mut self, reference: &Node<TypeReference>) {
    self.mark_scope(reference);
    if let Some(args) = &reference.stx.type_arguments {
      for arg in args.iter() {
        self.walk_type_expr(arg);
      }
    }
  }

  fn resolve_type_entity_name(&mut self, name: &TypeEntityName) {
    if let TypeEntityName::Qualified(q) = name {
      self.resolve_type_entity_name(&q.left);
    }
  }

  fn walk_namespace(&mut self, ns: &Node<NamespaceDecl>) {
    self.declare(
      &ns.stx.name,
      Namespace::VALUE | Namespace::NAMESPACE,
      span_for_name(ns.loc, &ns.stx.name),
    );
    match &ns.stx.body {
      parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
        self.push_scope(ScopeKind::Block, to_range(ns.loc));
        self.mark_scope(ns);
        for stmt in body.iter() {
          self.walk_stmt(stmt);
        }
        self.pop_scope();
      }
      parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
    }
  }

  fn walk_module(&mut self, module: &Node<ModuleDecl>) {
    let name = match &module.stx.name {
      parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.as_str(),
      parse_js::ast::ts_stmt::ModuleName::String(s) => s.as_str(),
    };
    self.declare(
      name,
      Namespace::VALUE | Namespace::NAMESPACE,
      span_for_name(module.loc, name),
    );
    if let Some(body) = &module.stx.body {
      self.push_scope(ScopeKind::Module, to_range(module.loc));
      self.mark_scope(module);
      for stmt in body.iter() {
        self.walk_stmt(stmt);
      }
      self.pop_scope();
    }
  }

  fn walk_import(&mut self, import: &Node<parse_js::ast::stmt::ImportStmt>) {
    self.mark_scope(import);
    let base_ns = if import.stx.type_only {
      Namespace::TYPE
    } else {
      Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
    };
    if let Some(default) = &import.stx.default {
      self.walk_pat_decl(default, base_ns);
    }
    if let Some(names) = &import.stx.names {
      match names {
        ImportNames::All(pat) => self.walk_pat_decl(pat, base_ns),
        ImportNames::Specific(list) => {
          for item in list.iter() {
            let ns = if item.stx.type_only {
              Namespace::TYPE
            } else {
              base_ns
            };
            self.walk_import_name(item, ns);
          }
        }
      }
    }
  }

  fn walk_import_name(&mut self, name: &Node<ImportName>, ns: Namespace) {
    self.mark_scope(name);
    self.walk_pat_decl(&name.stx.alias, ns);
    if let AstPat::Id(id) = &*name.stx.alias.stx.pat.stx {
      self.declare(&id.stx.name, ns, to_range(name.loc));
    }
  }

  fn finish(self) -> (SemanticsBuilder, ts::TsAssocTables) {
    (self.builder, self.tables)
  }
}

struct ResolveTablesPass<'a> {
  builder: &'a SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  expr_resolutions: BTreeMap<TextRange, SymbolId>,
  type_resolutions: BTreeMap<TextRange, SymbolId>,
  tables: ts::TsAssocTables,
}

impl<'a> ResolveTablesPass<'a> {
  fn new(builder: &'a SemanticsBuilder, root: ScopeId, tables: ts::TsAssocTables) -> Self {
    Self {
      builder,
      scope_stack: vec![root],
      expr_resolutions: BTreeMap::new(),
      type_resolutions: BTreeMap::new(),
      tables,
    }
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope_for_node<T: Drive + DriveMut>(&mut self, node: &Node<T>) {
    if let Some(id) = ts::scope_id_in_tables(&self.tables, node.loc) {
      if self.scope_stack.last().copied() != Some(id) {
        self.scope_stack.push(id);
      }
    }
  }

  fn pop_scope_for_node<T: Drive + DriveMut>(&mut self, node: &Node<T>) {
    if let Some(id) = ts::scope_id_in_tables(&self.tables, node.loc) {
      if self.scope_stack.last().copied() == Some(id) {
        self.scope_stack.pop();
      }
    }
  }

  fn walk_top(&mut self, top: &Node<TopLevel>) {
    self.push_scope_for_node(top);
    for stmt in top.stx.body.iter() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_for_node(top);
  }

  fn walk_stmt(&mut self, stmt: &Node<AstStmt>) {
    self.push_scope_for_node(stmt);
    match &*stmt.stx {
      AstStmt::Block(block) => {
        self.walk_block(block);
      }
      AstStmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter() {
          self.walk_pat_decl(&decl.pattern);
          if let Some(annot) = &decl.type_annotation {
            self.walk_type_expr(annot);
          }
          if let Some(init) = &decl.initializer {
            self.walk_expr(init);
          }
        }
      }
      AstStmt::FunctionDecl(func) => {
        if let Some(name) = &func.stx.name {
          let span = span_for_name(name.loc, &name.stx.name);
          if let Some(sym) = ts::declared_symbol_in_tables(&self.tables, span) {
            self.expr_resolutions.insert(span, sym);
            self.tables.record_expr_resolution(span, sym);
          }
        }
        self.walk_func(&func.stx.function);
      }
      AstStmt::ClassDecl(class) => {
        if let Some(name) = &class.stx.name {
          let span = span_for_name(name.loc, &name.stx.name);
          if let Some(sym) = ts::declared_symbol_in_tables(&self.tables, span) {
            self.expr_resolutions.insert(span, sym);
            self.tables.record_expr_resolution(span, sym);
          }
        }
        for member in class.stx.members.iter() {
          self.push_scope_for_node(member);
          self.pop_scope_for_node(member);
        }
      }
      AstStmt::Expr(expr) => self.walk_expr(&expr.stx.expr),
      AstStmt::Return(ret) => {
        if let Some(v) = &ret.stx.value {
          self.walk_expr(v);
        }
      }
      AstStmt::If(if_stmt) => {
        self.walk_expr(&if_stmt.stx.test);
        self.walk_stmt(&if_stmt.stx.consequent);
        if let Some(alt) = &if_stmt.stx.alternate {
          self.walk_stmt(alt);
        }
      }
      AstStmt::ForTriple(triple) => {
        match &triple.stx.init {
          ForTripleStmtInit::Expr(e) => self.walk_expr(e),
          ForTripleStmtInit::Decl(d) => {
            for decl in d.stx.declarators.iter() {
              self.walk_pat_decl(&decl.pattern);
              if let Some(init) = &decl.initializer {
                self.walk_expr(init);
              }
            }
          }
          ForTripleStmtInit::None => {}
        }
        if let Some(cond) = &triple.stx.cond {
          self.walk_expr(cond);
        }
        if let Some(post) = &triple.stx.post {
          self.walk_expr(post);
        }
        self.walk_for_body(&triple.stx.body);
      }
      AstStmt::ForIn(for_in) => {
        match &for_in.stx.lhs {
          ForInOfLhs::Assign(pat) => self.walk_pat(pat),
          ForInOfLhs::Decl((_, decl)) => self.walk_pat_decl(decl),
        }
        self.walk_expr(&for_in.stx.rhs);
        self.walk_for_body(&for_in.stx.body);
      }
      AstStmt::ForOf(for_of) => {
        match &for_of.stx.lhs {
          ForInOfLhs::Assign(pat) => self.walk_pat(pat),
          ForInOfLhs::Decl((_, decl)) => self.walk_pat_decl(decl),
        }
        self.walk_expr(&for_of.stx.rhs);
        self.walk_for_body(&for_of.stx.body);
      }
      AstStmt::Try(tr) => {
        self.walk_block_stmt(&tr.stx.wrapped);
        if let Some(catch) = &tr.stx.catch {
          if let Some(param) = &catch.stx.parameter {
            self.walk_pat_decl(param);
          }
          for stmt in catch.stx.body.iter() {
            self.walk_stmt(stmt);
          }
        }
        if let Some(finally) = &tr.stx.finally {
          self.walk_block_stmt(finally);
        }
      }
      AstStmt::Switch(sw) => {
        self.walk_expr(&sw.stx.test);
        for branch in sw.stx.branches.iter() {
          if let Some(case) = &branch.stx.case {
            self.walk_expr(case);
          }
          for stmt in branch.stx.body.iter() {
            self.walk_stmt(stmt);
          }
        }
      }
      AstStmt::With(w) => {
        self.walk_expr(&w.stx.object);
        self.walk_stmt(&w.stx.body);
      }
      AstStmt::InterfaceDecl(intf) => {
        let span = span_for_name(intf.loc, &intf.stx.name);
        if let Some(sym) = ts::declared_symbol_in_tables(&self.tables, span) {
          self.expr_resolutions.insert(span, sym);
          self.tables.record_expr_resolution(span, sym);
        }
        for ext in intf.stx.extends.iter() {
          self.walk_type_expr(ext);
        }
      }
      AstStmt::TypeAliasDecl(alias) => {
        let span = span_for_name(alias.loc, &alias.stx.name);
        if let Some(sym) = ts::declared_symbol_in_tables(&self.tables, span) {
          self.expr_resolutions.insert(span, sym);
          self.tables.record_expr_resolution(span, sym);
        }
        self.walk_type_expr(&alias.stx.type_expr);
      }
      AstStmt::NamespaceDecl(ns) => match &ns.stx.body {
        parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
          for stmt in body.iter() {
            self.walk_stmt(stmt);
          }
        }
        parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
      },
      AstStmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          for stmt in body.iter() {
            self.walk_stmt(stmt);
          }
        }
      }
      AstStmt::Import(import) => {
        if let Some(default) = &import.stx.default {
          self.walk_pat_decl(default);
        }
        if let Some(names) = &import.stx.names {
          match names {
            ImportNames::All(pat) => self.walk_pat_decl(pat),
            ImportNames::Specific(list) => {
              for item in list.iter() {
                self.walk_import_name(item);
              }
            }
          }
        }
      }
      _ => {}
    }
    self.pop_scope_for_node(stmt);
  }

  fn walk_namespace(&mut self, ns: &Node<NamespaceDecl>) {
    self.push_scope_for_node(ns);
    match &ns.stx.body {
      parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
        for stmt in body.iter() {
          self.walk_stmt(stmt);
        }
      }
      parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
    }
    self.pop_scope_for_node(ns);
  }

  fn walk_block_stmt(&mut self, block: &Node<BlockStmt>) {
    self.push_scope_for_node(block);
    for stmt in block.stx.body.iter() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_for_node(block);
  }

  fn walk_block(&mut self, block: &Node<BlockStmt>) {
    for stmt in block.stx.body.iter() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_for_body(&mut self, body: &Node<ForBody>) {
    self.push_scope_for_node(body);
    for stmt in body.stx.body.iter() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_for_node(body);
  }

  fn walk_pat_decl(&mut self, decl: &Node<parse_js::ast::stmt::decl::PatDecl>) {
    self.walk_pat(&decl.stx.pat);
  }

  fn walk_pat(&mut self, pat: &Node<AstPat>) {
    match &*pat.stx {
      AstPat::Id(id) => {
        let span = span_for_name(pat.loc, &id.stx.name);
        if let Some(sym) = ts::declared_symbol_in_tables(&self.tables, span) {
          self.expr_resolutions.insert(span, sym);
          self.tables.record_expr_resolution(span, sym);
        } else {
          let sym = self
            .builder
            .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
          if let Some(sym) = sym {
            self.expr_resolutions.insert(span, sym);
            self.tables.record_expr_resolution(span, sym);
          }
        }
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.walk_pat(&elem.target);
          if let Some(default) = &elem.default_value {
            self.walk_expr(default);
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.walk_pat(rest);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.walk_pat(&prop.stx.target);
          if let Some(default) = &prop.stx.default_value {
            self.walk_expr(default);
          }
        }
        if let Some(rest) = &obj.stx.rest {
          self.walk_pat(rest);
        }
      }
      AstPat::AssignTarget(expr) => self.walk_expr(expr),
    }
  }

  fn walk_arr_pat_expr(&mut self, pat: &Node<ArrPat>) {
    for elem in pat.stx.elements.iter().flatten() {
      self.walk_pat(&elem.target);
      if let Some(default) = &elem.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &pat.stx.rest {
      self.walk_pat(rest);
    }
  }

  fn walk_obj_pat_expr(&mut self, pat: &Node<ObjPat>) {
    for prop in pat.stx.properties.iter() {
      self.walk_pat(&prop.stx.target);
      if let Some(default) = &prop.stx.default_value {
        self.walk_expr(default);
      }
    }
    if let Some(rest) = &pat.stx.rest {
      self.walk_pat(rest);
    }
  }

  fn walk_expr(&mut self, expr: &Node<AstExpr>) {
    match &*expr.stx {
      AstExpr::Id(id) => {
        let span = span_for_name(expr.loc, &id.stx.name);
        let sym = self
          .builder
          .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
        if let Some(sym) = sym {
          self.expr_resolutions.insert(span, sym);
          self.tables.record_expr_resolution(span, sym);
        }
      }
      AstExpr::Binary(bin) => {
        self.walk_expr(&bin.stx.left);
        self.walk_expr(&bin.stx.right);
      }
      AstExpr::Call(call) => {
        self.walk_expr(&call.stx.callee);
        for arg in call.stx.arguments.iter() {
          self.walk_expr(&arg.stx.value);
        }
      }
      AstExpr::Member(mem) => self.walk_expr(&mem.stx.left),
      AstExpr::Cond(cond) => {
        self.walk_expr(&cond.stx.test);
        self.walk_expr(&cond.stx.consequent);
        self.walk_expr(&cond.stx.alternate);
      }
      AstExpr::Func(func) => self.walk_func(&func.stx.func),
      AstExpr::ArrowFunc(arrow) => self.walk_func(&arrow.stx.func),
      AstExpr::Class(class) => {
        if let Some(name) = &class.stx.name {
          let span = to_range(name.loc);
          let sym = self
            .builder
            .resolve(self.current_scope(), &name.stx.name, Namespace::VALUE);
          if let Some(sym) = sym {
            self.expr_resolutions.insert(span, sym);
            self.tables.record_expr_resolution(span, sym);
          }
        }
      }
      AstExpr::ArrPat(arr) => self.walk_arr_pat_expr(arr),
      AstExpr::ObjPat(obj) => self.walk_obj_pat_expr(obj),
      AstExpr::TaggedTemplate(tag) => {
        self.walk_expr(&tag.stx.function);
        for part in tag.stx.parts.iter() {
          if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
            self.walk_expr(expr);
          }
        }
      }
      AstExpr::LitArr(arr) => {
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(e)
            | parse_js::ast::expr::lit::LitArrElem::Rest(e) => self.walk_expr(e),
            parse_js::ast::expr::lit::LitArrElem::Empty => {}
          }
        }
      }
      AstExpr::LitObj(obj) => {
        for member in obj.stx.members.iter() {
          self.push_scope_for_node(member);
          self.pop_scope_for_node(member);
        }
      }
      AstExpr::Unary(unary) => self.walk_expr(&unary.stx.argument),
      AstExpr::UnaryPostfix(post) => self.walk_expr(&post.stx.argument),
      AstExpr::ComputedMember(mem) => {
        self.walk_expr(&mem.stx.object);
        self.walk_expr(&mem.stx.member);
      }
      _ => {}
    }
  }

  fn walk_func(&mut self, func: &Node<Func>) {
    self.push_scope_for_node(func);
    if let Some(params) = &func.stx.type_parameters {
      for param in params.iter() {
        self.walk_type_param(param);
      }
    }
    for param in func.stx.parameters.iter() {
      self.walk_pat_decl(&param.stx.pattern);
      if let Some(default) = &param.stx.default_value {
        self.walk_expr(default);
      }
      if let Some(ty) = &param.stx.type_annotation {
        self.walk_type_expr(ty);
      }
    }
    if let Some(ret) = &func.stx.return_type {
      self.walk_type_expr(ret);
    }
    if let Some(body) = &func.stx.body {
      match body {
        FuncBody::Block(stmts) => {
          for stmt in stmts.iter() {
            self.walk_stmt(stmt);
          }
        }
        FuncBody::Expression(expr) => self.walk_expr(expr),
      }
    }
    self.pop_scope_for_node(func);
  }

  fn walk_type_param(&mut self, param: &Node<parse_js::ast::type_expr::TypeParameter>) {
    self.push_scope_for_node(param);
    let span = span_for_name(param.loc, &param.stx.name);
    if let Some(sym) = ts::declared_symbol_in_tables(&self.tables, span) {
      self.expr_resolutions.insert(span, sym);
      self.tables.record_expr_resolution(span, sym);
    }
    if let Some(constraint) = &param.stx.constraint {
      self.walk_type_expr(constraint);
    }
    if let Some(default) = &param.stx.default {
      self.walk_type_expr(default);
    }
    self.pop_scope_for_node(param);
  }

  fn walk_type_expr(&mut self, ty: &Node<TypeExpr>) {
    match &*ty.stx {
      TypeExpr::TypeReference(reference) => {
        let span = to_range(ty.loc);
        if let Some(sym) = self.resolve_type_reference(reference) {
          self.type_resolutions.insert(span, sym);
          self.tables.record_type_resolution(span, sym);
        }
        if let Some(args) = &reference.stx.type_arguments {
          for arg in args.iter() {
            self.walk_type_expr(arg);
          }
        }
      }
      TypeExpr::ArrayType(arr) => self.walk_type_expr(&arr.stx.element_type),
      TypeExpr::UnionType(union) => {
        for t in union.stx.types.iter() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::IntersectionType(inter) => {
        for t in inter.stx.types.iter() {
          self.walk_type_expr(t);
        }
      }
      TypeExpr::ParenthesizedType(par) => self.walk_type_expr(&par.stx.type_expr),
      TypeExpr::FunctionType(func) => self.walk_type_function(func),
      TypeExpr::ConstructorType(func) => self.walk_constructor_type(func),
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter() {
          self.walk_type_expr(&elem.stx.type_expr);
        }
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter() {
          self.push_scope_for_node(member);
          self.pop_scope_for_node(member);
        }
      }
      TypeExpr::TypeQuery(query) => {
        if let Some(sym) = self.resolve_type_entity_name(&query.stx.expr_name) {
          let span = to_range(ty.loc);
          self.type_resolutions.insert(span, sym);
          self.tables.record_type_resolution(span, sym);
        }
      }
      TypeExpr::KeyOfType(k) => self.walk_type_expr(&k.stx.type_expr),
      TypeExpr::IndexedAccessType(idx) => {
        self.walk_type_expr(&idx.stx.object_type);
        self.walk_type_expr(&idx.stx.index_type);
      }
      TypeExpr::ConditionalType(cond) => {
        self.walk_type_expr(&cond.stx.check_type);
        self.walk_type_expr(&cond.stx.extends_type);
        self.walk_type_expr(&cond.stx.true_type);
        self.walk_type_expr(&cond.stx.false_type);
      }
      TypeExpr::MappedType(mapped) => {
        self.walk_type_expr(&mapped.stx.constraint);
        if let Some(name) = &mapped.stx.name_type {
          self.walk_type_expr(name);
        }
        self.walk_type_expr(&mapped.stx.type_expr);
      }
      TypeExpr::TemplateLiteralType(tmpl) => {
        for span in tmpl.stx.spans.iter() {
          self.walk_type_expr(&span.stx.type_expr);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(annot) = &pred.stx.type_annotation {
          self.walk_type_expr(annot);
        }
      }
      TypeExpr::InferType(infer) => {
        if let Some(cons) = &infer.stx.constraint {
          self.walk_type_expr(cons);
        }
      }
      TypeExpr::ImportType(import) => {
        if let Some(qual) = &import.stx.qualifier {
          if let Some(sym) = self.resolve_type_entity_name(qual) {
            let span = to_range(ty.loc);
            self.type_resolutions.insert(span, sym);
            self.tables.record_type_resolution(span, sym);
          }
        }
        if let Some(args) = &import.stx.type_arguments {
          for arg in args.iter() {
            self.walk_type_expr(arg);
          }
        }
      }
      _ => {}
    }
  }

  fn resolve_type_reference(&self, reference: &Node<TypeReference>) -> Option<SymbolId> {
    match &reference.stx.name {
      TypeEntityName::Identifier(name) => {
        self
          .builder
          .resolve(self.current_scope(), name.as_str(), Namespace::TYPE)
      }
      TypeEntityName::Qualified(q) => self.resolve_type_entity_name(&q.left),
      TypeEntityName::Import(_) => None,
    }
  }

  fn resolve_type_entity_name(&self, name: &TypeEntityName) -> Option<SymbolId> {
    match name {
      TypeEntityName::Identifier(name) => {
        self
          .builder
          .resolve(self.current_scope(), name.as_str(), Namespace::TYPE)
      }
      TypeEntityName::Qualified(q) => self.resolve_type_entity_name(&q.left),
      TypeEntityName::Import(_) => None,
    }
  }

  fn walk_type_function(&mut self, func: &Node<TypeFunction>) {
    for param in func.stx.parameters.iter() {
      self.walk_type_expr(&param.stx.type_expr);
    }
    self.walk_type_expr(&func.stx.return_type);
  }

  fn walk_constructor_type(&mut self, func: &Node<TypeConstructor>) {
    for param in func.stx.parameters.iter() {
      self.walk_type_expr(&param.stx.type_expr);
    }
    self.walk_type_expr(&func.stx.return_type);
  }

  fn walk_import_name(&mut self, name: &Node<ImportName>) {
    self.walk_pat_decl(&name.stx.alias);
  }
}

fn ns_index(ns: Namespace) -> usize {
  match ns {
    Namespace::VALUE => 0,
    Namespace::TYPE => 1,
    Namespace::NAMESPACE => 2,
    _ => panic!("expected single namespace bit"),
  }
}

fn to_range(loc: parse_js::loc::Loc) -> TextRange {
  TextRange::new(loc.start_u32(), loc.end_u32())
}

fn span_for_name(loc: parse_js::loc::Loc, name: &str) -> TextRange {
  let range = to_range(loc);
  let len = name.len() as u32;
  if range.len() >= len {
    return range;
  }
  let end = range.start;
  let start = end.saturating_sub(len);
  TextRange::new(start, end)
}
