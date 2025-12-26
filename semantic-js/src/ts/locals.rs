use super::model::Namespace;
use crate::assoc::ts::{DeclaredSymbol, ResolvedSymbol, ScopeInfo, TsAssocTables};
use crate::assoc::SpanKey;
use diagnostics::TextRange;
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
use parse_js::ast::ts_stmt::{ModuleDecl, NamespaceDecl};
use parse_js::ast::type_expr::{
  TypeConstructor, TypeEntityName, TypeExpr, TypeFunction, TypeReference,
};
use parse_js::loc::Loc;
use std::collections::{BTreeMap, HashMap};

/// Deterministic identifier for a lexical scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

impl ScopeId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

/// Deterministic identifier for an interned name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub u32);

impl NameId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

/// Deterministic identifier for a symbol in any namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
  pub names: Vec<String>,
  #[allow(dead_code)]
  name_lookup: HashMap<String, NameId>,
  pub scopes: Vec<ScopeData>,
  pub symbols: Vec<SymbolData>,
  pub tables: TsAssocTables,
}

impl TsLocalSemantics {
  pub fn scope(&self, id: ScopeId) -> &ScopeData {
    &self.scopes[id.index()]
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    &self.symbols[id.index()]
  }

  /// Resolve an expression in a lowered [`hir_js::hir::Body`] back to the local
  /// symbol it referenced, if any.
  pub fn resolve_expr(
    &self,
    body: &hir_js::hir::Body,
    expr: hir_js::ids::ExprId,
  ) -> Option<SymbolId> {
    let span = body.exprs[expr.0 as usize].span;
    self.resolve_expr_span(span)
  }

  /// Resolve an expression span without requiring a lowered body reference.
  pub fn resolve_expr_span(&self, span: TextRange) -> Option<SymbolId> {
    self.tables.resolved_expr(SpanKey::from(span))
  }

  /// Resolve a type name in lowered HIR types.
  pub fn resolve_type_name(
    &self,
    types: &[hir_js::hir::TypeExpr],
    id: hir_js::ids::TypeExprId,
  ) -> Option<SymbolId> {
    let span = types[id.0 as usize].span;
    self.tables.resolved_type(SpanKey::from(span))
  }

  /// Resolve a type reference by its span.
  pub fn resolve_type_span(&self, span: TextRange) -> Option<SymbolId> {
    self.tables.resolved_type(SpanKey::from(span))
  }

  pub fn scope_for_span(&self, span: TextRange) -> Option<ScopeId> {
    self.tables.scope(SpanKey::from(span))
  }

  pub fn declared_symbol_for_span(&self, span: TextRange) -> Option<SymbolId> {
    self.tables.declared_symbol(SpanKey::from(span))
  }
}

trait TsAssocStore {
  fn record_scope(&mut self, loc: Loc, assoc: &mut NodeAssocData, scope: ScopeId);
  fn scope(&self, loc: Loc, assoc: &NodeAssocData) -> Option<ScopeId>;
  fn record_declared_symbol(&mut self, loc: Loc, assoc: &mut NodeAssocData, sym: SymbolId);
  fn declared_symbol(&self, loc: Loc, assoc: &NodeAssocData) -> Option<SymbolId>;
  fn record_value_resolution(&mut self, loc: Loc, assoc: &mut NodeAssocData, sym: Option<SymbolId>);
  fn record_type_resolution(&mut self, loc: Loc, assoc: &mut NodeAssocData, sym: Option<SymbolId>);
}

struct TsAssocRecorder<'a> {
  tables: &'a mut TsAssocTables,
  write_assoc: bool,
}

impl<'a> TsAssocRecorder<'a> {
  fn new(tables: &'a mut TsAssocTables, write_assoc: bool) -> Self {
    Self {
      tables,
      write_assoc,
    }
  }

  fn key(loc: Loc) -> SpanKey {
    SpanKey::from(loc)
  }
}

impl TsAssocStore for TsAssocRecorder<'_> {
  fn record_scope(&mut self, loc: Loc, assoc: &mut NodeAssocData, scope: ScopeId) {
    self.tables.record_scope(Self::key(loc), scope);
    if self.write_assoc {
      assoc.set(ScopeInfo(scope));
    }
  }

  fn scope(&self, loc: Loc, assoc: &NodeAssocData) -> Option<ScopeId> {
    self
      .tables
      .scope(Self::key(loc))
      .or_else(|| assoc.get::<ScopeInfo>().map(|s| s.0))
  }

  fn record_declared_symbol(&mut self, loc: Loc, assoc: &mut NodeAssocData, sym: SymbolId) {
    self.tables.record_declared_symbol(Self::key(loc), sym);
    if self.write_assoc {
      assoc.set(DeclaredSymbol(sym));
    }
  }

  fn declared_symbol(&self, loc: Loc, assoc: &NodeAssocData) -> Option<SymbolId> {
    self
      .tables
      .declared_symbol(Self::key(loc))
      .or_else(|| assoc.get::<DeclaredSymbol>().map(|s| s.0))
  }

  fn record_value_resolution(
    &mut self,
    loc: Loc,
    assoc: &mut NodeAssocData,
    sym: Option<SymbolId>,
  ) {
    if let Some(sym) = sym {
      self.tables.record_expr_resolution(Self::key(loc), sym);
    }
    if self.write_assoc {
      assoc.set(ResolvedSymbol(sym));
    }
  }

  fn record_type_resolution(&mut self, loc: Loc, assoc: &mut NodeAssocData, sym: Option<SymbolId>) {
    if let Some(sym) = sym {
      self.tables.record_type_resolution(Self::key(loc), sym);
    }
    if self.write_assoc {
      assoc.set(ResolvedSymbol(sym));
    }
  }
}

#[derive(Clone, Copy)]
enum DeclTarget {
  Lexical,
  Hoisted,
}

struct SemanticsBuilder {
  names: Vec<String>,
  name_lookup: HashMap<String, NameId>,
  scopes: Vec<ScopeData>,
  symbols: Vec<SymbolData>,
}

impl SemanticsBuilder {
  fn new(kind: ScopeKind) -> (Self, ScopeId) {
    let mut scopes = Vec::new();
    scopes.push(ScopeData::new(None, kind));
    (
      Self {
        names: Vec::new(),
        name_lookup: HashMap::new(),
        scopes,
        symbols: Vec::new(),
      },
      ScopeId(0),
    )
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    if let Some(id) = self.name_lookup.get(name) {
      *id
    } else {
      let id = NameId(self.names.len() as u32);
      self.names.push(name.to_string());
      self.name_lookup.insert(name.to_string(), id);
      id
    }
  }

  fn alloc_scope(&mut self, parent: ScopeId, kind: ScopeKind) -> ScopeId {
    let id = ScopeId(self.scopes.len() as u32);
    self.scopes.push(ScopeData::new(Some(parent), kind));
    self.scopes[parent.index()].children.push(id);
    id
  }

  fn alloc_symbol(
    &mut self,
    scope: ScopeId,
    name: NameId,
    namespaces: Namespace,
    span: Option<TextRange>,
  ) -> SymbolId {
    let id = SymbolId(self.symbols.len() as u32);
    self.symbols.push(SymbolData {
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
      .get(scope.index())
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
    {
      let data = &mut self.symbols[sym.index()];
      data.namespaces |= namespaces;
    }
    for bit in namespaces.iter_bits() {
      slots[ns_index(bit)] = Some(sym);
    }
    if let Some(scope) = self.scopes.get_mut(scope.index()) {
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
      let scope_data = &self.scopes[scope_id.index()];
      if let Some(slots) = scope_data.bindings.get(name_id) {
        if let Some(sym) = slots[ns_index(ns)] {
          if self.symbols[sym.index()].namespaces.contains(ns) {
            return Some(sym);
          }
        }
      }
      current = scope_data.parent;
    }
    None
  }

  fn into_semantics(self, tables: TsAssocTables) -> TsLocalSemantics {
    TsLocalSemantics {
      names: self.names,
      name_lookup: self.name_lookup,
      scopes: self.scopes,
      symbols: self.symbols,
      tables,
    }
  }
}

/// Build deterministic TS local scopes and resolution tables for a parsed file,
/// mutating [`NodeAssocData`] for backwards compatibility.
pub fn bind_ts_locals(top: &mut Node<TopLevel>, is_module: bool) -> TsLocalSemantics {
  bind_ts_locals_internal(top, is_module, true)
}

/// Pure variant of [`bind_ts_locals`] that records side tables without mutating
/// the input AST.
pub fn bind_ts_locals_pure(top: &mut Node<TopLevel>, is_module: bool) -> TsLocalSemantics {
  bind_ts_locals_internal(top, is_module, false)
}

fn bind_ts_locals_internal(
  top: &mut Node<TopLevel>,
  is_module: bool,
  write_assoc: bool,
) -> TsLocalSemantics {
  let kind = if is_module {
    ScopeKind::Module
  } else {
    ScopeKind::Script
  };
  let (builder, root) = SemanticsBuilder::new(kind);
  let mut tables = TsAssocTables::default();
  let mut assoc = TsAssocRecorder::new(&mut tables, write_assoc);
  let mut decl = DeclarePass::new(builder, root, &mut assoc);
  decl.walk_top(top);
  let builder = decl.finish();

  {
    let mut resolve = ResolvePass::new(&builder, root, &mut assoc);
    resolve.walk_top(top);
  }
  builder.into_semantics(tables)
}

struct DeclarePass<'a, A: TsAssocStore> {
  builder: SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  decl_target: Vec<DeclTarget>,
  assoc: &'a mut A,
}

impl<'a, A: TsAssocStore> DeclarePass<'a, A> {
  fn new(builder: SemanticsBuilder, root: ScopeId, assoc: &'a mut A) -> Self {
    Self {
      builder,
      scope_stack: vec![root],
      decl_target: vec![DeclTarget::Lexical],
      assoc,
    }
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope(&mut self, kind: ScopeKind) {
    let parent = self.current_scope();
    let id = self.builder.alloc_scope(parent, kind);
    self.scope_stack.push(id);
  }

  fn pop_scope(&mut self) {
    self.scope_stack.pop();
  }

  fn mark_scope(&mut self, loc: Loc, assoc: &mut NodeAssocData) {
    self.assoc.record_scope(loc, assoc, self.current_scope());
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
      .find(|scope| self.builder.scopes[scope.index()].kind.is_hoist_target())
      .unwrap_or_else(|| self.current_scope())
  }

  fn declare(
    &mut self,
    loc: Loc,
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
    self.assoc.record_declared_symbol(loc, assoc, sym);
  }

  fn walk_top(&mut self, top: &mut Node<TopLevel>) {
    self.mark_scope(top.loc, &mut top.assoc);
    for stmt in top.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_stmt(&mut self, stmt: &mut Node<AstStmt>) {
    self.mark_scope(stmt.loc, &mut stmt.assoc);
    match &mut *stmt.stx {
      AstStmt::Block(block) => {
        self.push_scope(ScopeKind::Block);
        self.walk_block(block);
        self.pop_scope();
      }
      AstStmt::VarDecl(var) => self.walk_var_decl(var),
      AstStmt::FunctionDecl(func) => {
        if let Some(name) = &mut func.stx.name {
          self.declare(
            name.loc,
            &mut name.assoc,
            &name.stx.name,
            Namespace::VALUE,
            None,
          );
        }
        self.walk_func(&mut func.stx.function);
      }
      AstStmt::ClassDecl(class) => {
        if let Some(name) = &mut class.stx.name {
          self.declare(
            name.loc,
            &mut name.assoc,
            &name.stx.name,
            Namespace::VALUE | Namespace::TYPE,
            None,
          );
        }
        self.push_scope(ScopeKind::Class);
        for member in class.stx.members.iter_mut() {
          self.mark_scope(member.loc, &mut member.assoc);
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
          self.push_scope(ScopeKind::Block);
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
          intf.loc,
          &mut intf.assoc,
          &intf.stx.name,
          Namespace::TYPE,
          None,
        );
        if let Some(params) = &mut intf.stx.type_parameters {
          self.push_scope(ScopeKind::TypeParams);
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
          alias.loc,
          &mut alias.assoc,
          &alias.stx.name,
          Namespace::TYPE,
          None,
        );
        if let Some(params) = &mut alias.stx.type_parameters {
          self.push_scope(ScopeKind::TypeParams);
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
      _ => {}
    }
  }

  fn walk_block_stmt(&mut self, block: &mut Node<BlockStmt>) {
    self.push_scope(ScopeKind::Block);
    self.walk_block(block);
    self.pop_scope();
  }

  fn walk_block(&mut self, block: &mut Node<BlockStmt>) {
    self.mark_scope(block.loc, &mut block.assoc);
    for stmt in block.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_catch(&mut self, catch: &mut Node<CatchBlock>) {
    self.mark_scope(catch.loc, &mut catch.assoc);
    self.push_scope(ScopeKind::Block);
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
    self.mark_scope(body.loc, &mut body.assoc);
    self.push_scope(ScopeKind::Block);
    for stmt in body.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope();
  }

  fn walk_for_triple(&mut self, triple: &mut Node<ForTripleStmt>) {
    self.mark_scope(triple.loc, &mut triple.assoc);
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
    self.mark_scope(for_in.loc, &mut for_in.assoc);
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
    self.mark_scope(for_of.loc, &mut for_of.assoc);
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
    self.mark_scope(var.loc, &mut var.assoc);
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
    self.mark_scope(decl.loc, &mut decl.assoc);
    self.walk_pat(&mut decl.stx.pat, true, namespaces);
  }

  fn walk_pat(&mut self, pat: &mut Node<AstPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(pat.loc, &mut pat.assoc);
    match &mut *pat.stx {
      AstPat::Id(id) => {
        if in_decl {
          self.declare(
            id.loc,
            &mut id.assoc,
            &id.stx.name,
            namespaces,
            Some(to_range(pat.loc)),
          );
        }
      }
      AstPat::Arr(arr) => self.walk_arr_pat(arr, in_decl, namespaces),
      AstPat::Obj(obj) => self.walk_obj_pat(obj, in_decl, namespaces),
      AstPat::AssignTarget(expr) => self.walk_expr(expr),
    }
  }

  fn walk_arr_pat(&mut self, pat: &mut Node<ArrPat>, in_decl: bool, namespaces: Namespace) {
    self.mark_scope(pat.loc, &mut pat.assoc);
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
    self.mark_scope(pat.loc, &mut pat.assoc);
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
    self.mark_scope(expr.loc, &mut expr.assoc);
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
        self.push_scope(ScopeKind::Class);
        if let Some(name) = &mut class.stx.name {
          self.declare(
            name.loc,
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
          self.mark_scope(member.loc, &mut member.assoc);
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
    self.mark_scope(func.loc, &mut func.assoc);
    self.push_scope(ScopeKind::Function);
    self.enter_decl_target(DeclTarget::Hoisted);
    for param in func.stx.parameters.iter_mut() {
      self.walk_pat_decl(&mut param.stx.pattern, Namespace::VALUE);
      if let Some(default) = &mut param.stx.default_value {
        self.walk_expr(default);
      }
      if let Some(ty) = &mut param.stx.type_annotation {
        self.walk_type_expr(ty);
      }
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
    self.mark_scope(param.loc, &mut param.assoc);
    self.declare(
      param.loc,
      &mut param.assoc,
      &param.stx.name,
      Namespace::TYPE,
      Some(to_range(param.loc)),
    );
    if let Some(constraint) = &mut param.stx.constraint {
      self.walk_type_expr(constraint);
    }
    if let Some(default) = &mut param.stx.default {
      self.walk_type_expr(default);
    }
  }

  fn walk_type_expr(&mut self, ty: &mut Node<TypeExpr>) {
    self.mark_scope(ty.loc, &mut ty.assoc);
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
          self.mark_scope(member.loc, &mut member.assoc);
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
        self.push_scope(ScopeKind::TypeParams);
        self.declare(
          mapped.loc,
          &mut mapped.assoc,
          &mapped.stx.type_parameter,
          Namespace::TYPE,
          Some(to_range(mapped.loc)),
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
          infer.loc,
          &mut infer.assoc,
          &infer.stx.type_parameter,
          Namespace::TYPE,
          Some(to_range(infer.loc)),
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
    self.mark_scope(func.loc, &mut func.assoc);
    self.push_scope(ScopeKind::TypeParams);
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
    self.mark_scope(func.loc, &mut func.assoc);
    self.push_scope(ScopeKind::TypeParams);
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
    self.mark_scope(reference.loc, &mut reference.assoc);
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
    self.mark_scope(ns.loc, &mut ns.assoc);
    self.declare(
      ns.loc,
      &mut ns.assoc,
      &ns.stx.name,
      Namespace::VALUE | Namespace::NAMESPACE,
      Some(to_range(ns.loc)),
    );
    match &mut ns.stx.body {
      parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
        self.push_scope(ScopeKind::Block);
        for stmt in body.iter_mut() {
          self.walk_stmt(stmt);
        }
        self.pop_scope();
      }
      parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
    }
  }

  fn walk_module(&mut self, module: &mut Node<ModuleDecl>) {
    self.mark_scope(module.loc, &mut module.assoc);
    let name = match &module.stx.name {
      parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.as_str(),
      parse_js::ast::ts_stmt::ModuleName::String(s) => s.as_str(),
    };
    self.declare(
      module.loc,
      &mut module.assoc,
      name,
      Namespace::VALUE | Namespace::NAMESPACE,
      Some(to_range(module.loc)),
    );
    if let Some(body) = &mut module.stx.body {
      self.push_scope(ScopeKind::Module);
      for stmt in body.iter_mut() {
        self.walk_stmt(stmt);
      }
      self.pop_scope();
    }
  }

  fn walk_import(&mut self, import: &mut Node<parse_js::ast::stmt::ImportStmt>) {
    self.mark_scope(import.loc, &mut import.assoc);
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
    self.mark_scope(name.loc, &mut name.assoc);
    self.walk_pat_decl(&mut name.stx.alias, ns);
    if let AstPat::Id(id) = &mut *name.stx.alias.stx.pat.stx {
      self.declare(
        id.loc,
        &mut id.assoc,
        &id.stx.name,
        ns,
        Some(to_range(name.loc)),
      );
    }
  }

  fn finish(self) -> SemanticsBuilder {
    self.builder
  }
}

struct ResolvePass<'a, A: TsAssocStore> {
  builder: &'a SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  assoc: &'a mut A,
}

impl<'a, A: TsAssocStore> ResolvePass<'a, A> {
  fn new(builder: &'a SemanticsBuilder, root: ScopeId, assoc: &'a mut A) -> Self {
    Self {
      builder,
      scope_stack: vec![root],
      assoc,
    }
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope_from_assoc(&mut self, loc: Loc, assoc: &NodeAssocData) {
    if let Some(id) = self.assoc.scope(loc, assoc) {
      if self.scope_stack.last().copied() != Some(id) {
        self.scope_stack.push(id);
      }
    }
  }

  fn pop_scope_from_assoc(&mut self, loc: Loc, assoc: &NodeAssocData) {
    if let Some(id) = self.assoc.scope(loc, assoc) {
      if self.scope_stack.last().copied() == Some(id) {
        self.scope_stack.pop();
      }
    }
  }

  fn walk_top(&mut self, top: &mut Node<TopLevel>) {
    self.push_scope_from_assoc(top.loc, &top.assoc);
    for stmt in top.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_from_assoc(top.loc, &top.assoc);
  }

  fn walk_stmt(&mut self, stmt: &mut Node<AstStmt>) {
    self.push_scope_from_assoc(stmt.loc, &stmt.assoc);
    match &mut *stmt.stx {
      AstStmt::Block(block) => {
        self.walk_block(block);
      }
      AstStmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter_mut() {
          self.walk_pat_decl(&mut decl.pattern);
          if let Some(init) = &mut decl.initializer {
            self.walk_expr(init);
          }
        }
      }
      AstStmt::FunctionDecl(func) => {
        self.walk_func(&mut func.stx.function);
      }
      AstStmt::ClassDecl(class) => {
        for member in class.stx.members.iter_mut() {
          self.push_scope_from_assoc(member.loc, &member.assoc);
          self.pop_scope_from_assoc(member.loc, &member.assoc);
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
        for ext in intf.stx.extends.iter_mut() {
          self.walk_type_expr(ext);
        }
      }
      AstStmt::TypeAliasDecl(alias) => {
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
      _ => {}
    }
    self.pop_scope_from_assoc(stmt.loc, &stmt.assoc);
  }

  fn walk_namespace(&mut self, ns: &mut Node<NamespaceDecl>) {
    self.push_scope_from_assoc(ns.loc, &ns.assoc);
    match &mut ns.stx.body {
      parse_js::ast::ts_stmt::NamespaceBody::Block(body) => {
        for stmt in body.iter_mut() {
          self.walk_stmt(stmt);
        }
      }
      parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => self.walk_namespace(inner),
    }
    self.pop_scope_from_assoc(ns.loc, &ns.assoc);
  }

  fn walk_block_stmt(&mut self, block: &mut Node<BlockStmt>) {
    self.push_scope_from_assoc(block.loc, &block.assoc);
    for stmt in block.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_from_assoc(block.loc, &block.assoc);
  }

  fn walk_block(&mut self, block: &mut Node<BlockStmt>) {
    for stmt in block.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
  }

  fn walk_for_body(&mut self, body: &mut Node<ForBody>) {
    self.push_scope_from_assoc(body.loc, &body.assoc);
    for stmt in body.stx.body.iter_mut() {
      self.walk_stmt(stmt);
    }
    self.pop_scope_from_assoc(body.loc, &body.assoc);
  }

  fn walk_pat_decl(&mut self, decl: &mut Node<parse_js::ast::stmt::decl::PatDecl>) {
    self.walk_pat(&mut decl.stx.pat);
  }

  fn walk_pat(&mut self, pat: &mut Node<AstPat>) {
    match &mut *pat.stx {
      AstPat::Id(id) => {
        if let Some(sym) = self.assoc.declared_symbol(id.loc, &id.assoc) {
          self
            .assoc
            .record_value_resolution(pat.loc, &mut id.assoc, Some(sym));
        } else {
          let sym = self
            .builder
            .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
          self
            .assoc
            .record_value_resolution(pat.loc, &mut id.assoc, sym);
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
        let sym = self
          .builder
          .resolve(self.current_scope(), &id.stx.name, Namespace::VALUE);
        self
          .assoc
          .record_value_resolution(expr.loc, &mut expr.assoc, sym);
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
          let sym = self
            .builder
            .resolve(self.current_scope(), &name.stx.name, Namespace::VALUE);
          self
            .assoc
            .record_value_resolution(name.loc, &mut class.assoc, sym);
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
          self.push_scope_from_assoc(member.loc, &member.assoc);
          self.pop_scope_from_assoc(member.loc, &member.assoc);
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
    self.push_scope_from_assoc(func.loc, &func.assoc);
    for param in func.stx.parameters.iter_mut() {
      self.walk_pat_decl(&mut param.stx.pattern);
      if let Some(default) = &mut param.stx.default_value {
        self.walk_expr(default);
      }
      if let Some(ty) = &mut param.stx.type_annotation {
        self.walk_type_expr(ty);
      }
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
    self.pop_scope_from_assoc(func.loc, &func.assoc);
  }

  fn walk_type_expr(&mut self, ty: &mut Node<TypeExpr>) {
    match &mut *ty.stx {
      TypeExpr::TypeReference(reference) => {
        if let Some(sym) = self.resolve_type_reference(reference) {
          self
            .assoc
            .record_type_resolution(ty.loc, &mut ty.assoc, Some(sym));
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
          self.push_scope_from_assoc(member.loc, &member.assoc);
          self.pop_scope_from_assoc(member.loc, &member.assoc);
        }
      }
      TypeExpr::TypeQuery(query) => {
        if let Some(sym) = self.resolve_type_entity_name(&query.stx.expr_name) {
          self
            .assoc
            .record_type_resolution(ty.loc, &mut ty.assoc, Some(sym));
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
        if let Some(qual) = &import.stx.qualifier {
          if let Some(sym) = self.resolve_type_entity_name(qual) {
            self
              .assoc
              .record_type_resolution(ty.loc, &mut ty.assoc, Some(sym));
          }
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
