use super::JsSemantics;
use super::NameId;
use super::ScopeData;
use super::ScopeId;
use super::ScopeKind;
use super::SymbolData;
use super::SymbolFlags;
use super::SymbolId;
use super::TopLevelMode;
use crate::assoc::js::{scope_id, DeclaredSymbol};
use crate::hash::stable_hash;
use derive_visitor::{Drive, DriveMut, Visitor, VisitorMut};
use diagnostics::{Diagnostic, FileId, Label, Span, TextRange};
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::ClassExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::BlockStmt;
use parse_js::ast::stmt::CatchBlock;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForInStmt;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stmt::ForOfStmt;
use parse_js::ast::stmt::ForTripleStmt;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::ImportStmt;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::SwitchBranch;
use parse_js::ast::stmt::SwitchStmt;
use parse_js::ast::stmt::WithStmt;
use parse_js::ast::stx::TopLevel;
use std::collections::{BTreeMap, BTreeSet};

type BlockStmtNode = Node<BlockStmt>;
type CallExprNode = Node<CallExpr>;
type CatchBlockNode = Node<CatchBlock>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type FuncDeclNode = Node<FuncDecl>;
type FuncExprNode = Node<FuncExpr>;
type FuncNode = Node<Func>;
type ForBodyNode = Node<ForBody>;
type ForInStmtNode = Node<ForInStmt>;
type IdPatNode = Node<IdPat>;
type ImportStmtNode = Node<ImportStmt>;
type ForOfStmtNode = Node<ForOfStmt>;
type ForTripleStmtNode = Node<ForTripleStmt>;
type PatDeclNode = Node<PatDecl>;
type SwitchBranchNode = Node<SwitchBranch>;
type SwitchStmtNode = Node<SwitchStmt>;
type WithStmtNode = Node<WithStmt>;
type VarDeclNode = Node<VarDecl>;

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

fn symbol_id_for(file: FileId, scope: ScopeId, name: NameId) -> SymbolId {
  SymbolId(stable_hash(&(file, scope.raw(), name)))
}

fn range_of<T: Drive + DriveMut>(node: &Node<T>) -> TextRange {
  TextRange::new(node.loc.0 as u32, node.loc.1 as u32)
}

fn ident_range(loc: parse_js::loc::Loc, name: &str) -> TextRange {
  let start = loc.start_u32();
  let end = start.saturating_add(name.len() as u32);
  TextRange::new(start, end)
}

fn collect_pat_decl_names(file: FileId, pat_decl: &PatDecl, out: &mut BTreeSet<NameId>) {
  collect_pat_names(file, pat_decl.pat.stx.as_ref(), out);
}

fn collect_pat_names(file: FileId, pat: &Pat, out: &mut BTreeSet<NameId>) {
  match pat {
    Pat::Id(id) => {
      out.insert(name_id_for(file, &id.stx.name));
    }
    Pat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_pat_names(file, elem.target.stx.as_ref(), out);
      }
      if let Some(rest) = arr.stx.rest.as_ref() {
        collect_pat_names(file, rest.stx.as_ref(), out);
      }
    }
    Pat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_pat_names(file, prop.stx.target.stx.as_ref(), out);
      }
      if let Some(rest) = obj.stx.rest.as_ref() {
        collect_pat_names(file, rest.stx.as_ref(), out);
      }
    }
    Pat::AssignTarget(_) => {}
  }
}

#[derive(Visitor)]
#[visitor(
  BlockStmtNode(enter, exit),
  CatchBlockNode(enter, exit),
  ClassDeclNode(enter, exit),
  ClassExprNode(enter, exit),
  ForBodyNode(enter, exit),
  ForInStmtNode(enter, exit),
  ForInOfLhs(enter, exit),
  ForOfStmtNode(enter, exit),
  ForTripleStmtNode(enter, exit),
  FuncNode(enter, exit),
  SwitchStmtNode(enter, exit),
  VarDeclNode(enter)
)]
struct ClosureLexicalCollector {
  file: FileId,
  depth: usize,
  names: BTreeSet<NameId>,
}

impl ClosureLexicalCollector {
  fn new(file: FileId) -> Self {
    Self {
      file,
      depth: 0,
      names: BTreeSet::new(),
    }
  }

  fn enter_block_stmt_node(&mut self, _node: &BlockStmtNode) {
    self.depth += 1;
  }

  fn exit_block_stmt_node(&mut self, _node: &BlockStmtNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_catch_block_node(&mut self, _node: &CatchBlockNode) {
    self.depth += 1;
  }

  fn exit_catch_block_node(&mut self, _node: &CatchBlockNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_class_decl_node(&mut self, node: &ClassDeclNode) {
    if self.depth == 0 {
      if let Some(name) = node.stx.name.as_ref() {
        self.names.insert(name_id_for(self.file, &name.stx.name));
      }
    }
    self.depth += 1;
  }

  fn exit_class_decl_node(&mut self, _node: &ClassDeclNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_class_expr_node(&mut self, _node: &ClassExprNode) {
    self.depth += 1;
  }

  fn exit_class_expr_node(&mut self, _node: &ClassExprNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_for_body_node(&mut self, _node: &ForBodyNode) {
    self.depth += 1;
  }

  fn exit_for_body_node(&mut self, _node: &ForBodyNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_for_in_stmt_node(&mut self, _node: &ForInStmtNode) {
    self.depth += 1;
  }

  fn exit_for_in_stmt_node(&mut self, _node: &ForInStmtNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_for_in_of_lhs(&mut self, node: &ForInOfLhs) {
    if self.depth > 0 {
      return;
    }
    if let ForInOfLhs::Decl((mode, pat)) = node {
      if matches!(
        mode,
        VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
      ) {
        collect_pat_decl_names(self.file, pat.stx.as_ref(), &mut self.names);
      }
    }
  }

  fn exit_for_in_of_lhs(&mut self, _node: &ForInOfLhs) {}

  fn enter_for_of_stmt_node(&mut self, _node: &ForOfStmtNode) {
    self.depth += 1;
  }

  fn exit_for_of_stmt_node(&mut self, _node: &ForOfStmtNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_for_triple_stmt_node(&mut self, _node: &ForTripleStmtNode) {
    self.depth += 1;
  }

  fn exit_for_triple_stmt_node(&mut self, _node: &ForTripleStmtNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_func_node(&mut self, _node: &FuncNode) {
    self.depth += 1;
  }

  fn exit_func_node(&mut self, _node: &FuncNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_switch_stmt_node(&mut self, _node: &SwitchStmtNode) {
    self.depth += 1;
  }

  fn exit_switch_stmt_node(&mut self, _node: &SwitchStmtNode) {
    self.depth = self.depth.saturating_sub(1);
  }

  fn enter_var_decl_node(&mut self, node: &VarDeclNode) {
    if self.depth > 0 {
      return;
    }
    if !matches!(
      node.stx.mode,
      VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
    ) {
      return;
    }
    for decl in node.stx.declarators.iter() {
      collect_pat_decl_names(self.file, decl.pattern.stx.as_ref(), &mut self.names);
    }
  }
}

fn closure_lexical_names(file: FileId, func: &Func) -> BTreeSet<NameId> {
  let mut visitor = ClosureLexicalCollector::new(file);

  let Some(body) = func.body.as_ref() else {
    return visitor.names;
  };
  let FuncBody::Block(stmts) = body else {
    return visitor.names;
  };
  for stmt in stmts.iter() {
    stmt.drive(&mut visitor);
  }
  visitor.names
}

pub fn declare(top_level: &mut Node<TopLevel>, mode: TopLevelMode, file: FileId) -> JsSemantics {
  let (sem, _) = declare_with_diagnostics(top_level, mode, file);
  sem
}

pub(crate) fn declare_with_diagnostics(
  top_level: &mut Node<TopLevel>,
  mode: TopLevelMode,
  file: FileId,
) -> (JsSemantics, Vec<Diagnostic>) {
  let mut visitor = DeclareVisitor::new(mode, file, range_of(top_level));
  top_level.drive_mut(&mut visitor);
  let (mut sem, diagnostics) = visitor.finish();
  mark_dynamic_scopes(top_level, &mut sem);
  (sem, diagnostics)
}

#[derive(Debug, Clone, Copy, Default)]
struct DeclSpanInfo {
  first_var: Option<TextRange>,
  first_lexical: Option<TextRange>,
}

struct SemanticsBuilder {
  file: FileId,
  names: BTreeMap<NameId, String>,
  name_lookup: BTreeMap<String, NameId>,
  scopes: BTreeMap<ScopeId, ScopeData>,
  symbols: BTreeMap<SymbolId, SymbolData>,
  top_scope: ScopeId,
  decl_spans: BTreeMap<SymbolId, DeclSpanInfo>,
  block_var_decl_spans: BTreeMap<(ScopeId, NameId), TextRange>,
  block_lexical_decl_spans: BTreeMap<(ScopeId, NameId), TextRange>,
  block_func_decl_spans: BTreeMap<(ScopeId, NameId), TextRange>,
  catch_param_decl_spans: BTreeMap<(ScopeId, NameId), TextRange>,
  diagnostics: Vec<Diagnostic>,
}

impl SemanticsBuilder {
  fn new(mode: TopLevelMode, file: FileId, span: TextRange) -> Self {
    let kind = match mode {
      TopLevelMode::Global => ScopeKind::Global,
      TopLevelMode::Module => ScopeKind::Module,
    };
    let mut scopes = BTreeMap::new();
    let top_scope = scope_id_for(file, None, kind, span);
    scopes.insert(
      top_scope,
      ScopeData {
        parent: None,
        kind,
        children: Vec::new(),
        symbols: BTreeMap::new(),
        is_dynamic: false,
        has_direct_eval: false,
        hoisted_bindings: Vec::new(),
        tdz_bindings: Vec::new(),
      },
    );
    Self {
      file,
      names: BTreeMap::new(),
      name_lookup: BTreeMap::new(),
      scopes,
      symbols: BTreeMap::new(),
      top_scope,
      decl_spans: BTreeMap::new(),
      block_var_decl_spans: BTreeMap::new(),
      block_lexical_decl_spans: BTreeMap::new(),
      block_func_decl_spans: BTreeMap::new(),
      catch_param_decl_spans: BTreeMap::new(),
      diagnostics: Vec::new(),
    }
  }

  fn scope_kind(&self, id: ScopeId) -> ScopeKind {
    self.scopes.get(&id).expect("scope exists").kind
  }

  fn new_scope(&mut self, parent: ScopeId, kind: ScopeKind, span: TextRange) -> ScopeId {
    let id = scope_id_for(self.file, Some(parent), kind, span);
    self.scopes.entry(id).or_insert_with(|| ScopeData {
      parent: Some(parent),
      kind,
      children: Vec::new(),
      symbols: BTreeMap::new(),
      is_dynamic: false,
      has_direct_eval: false,
      hoisted_bindings: Vec::new(),
      tdz_bindings: Vec::new(),
    });
    if let Some(scope) = self.scopes.get_mut(&parent) {
      if !scope.children.contains(&id) {
        scope.children.push(id);
      }
    }
    id
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    if let Some(id) = self.name_lookup.get(name).copied() {
      return id;
    }

    let id = name_id_for(self.file, name);
    let owned = name.to_string();
    self.name_lookup.insert(owned.clone(), id);
    self.names.insert(id, owned);
    id
  }

  fn record_block_var_decl(
    &mut self,
    scope: ScopeId,
    name: NameId,
    raw_name: &str,
    span: TextRange,
  ) {
    let key = (scope, name);
    if self.block_var_decl_spans.contains_key(&key) {
      return;
    }
    self.block_var_decl_spans.insert(key, span);

    if let Some(prev_lexical) = self.block_lexical_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0002",
        format!("Conflicting lexical and var declarations for `{raw_name}`"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_lexical),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }

    if let Some(prev_func) = self.block_func_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0002",
        format!("Conflicting block function and var declarations for `{raw_name}`"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_func),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }
  }

  fn record_block_lexical_decl(
    &mut self,
    scope: ScopeId,
    name: NameId,
    raw_name: &str,
    span: TextRange,
  ) {
    let key = (scope, name);
    if self.block_lexical_decl_spans.contains_key(&key) {
      return;
    }
    self.block_lexical_decl_spans.insert(key, span);

    if let Some(prev_var) = self.block_var_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0002",
        format!("Conflicting lexical and var declarations for `{raw_name}`"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_var),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }

    if let Some(prev_func) = self.block_func_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0002",
        format!("Conflicting block function and lexical declarations for `{raw_name}`"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_func),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }
  }

  fn record_block_func_decl(
    &mut self,
    scope: ScopeId,
    name: NameId,
    raw_name: &str,
    span: TextRange,
  ) {
    let key = (scope, name);
    if self.block_func_decl_spans.contains_key(&key) {
      return;
    }
    self.block_func_decl_spans.insert(key, span);

    if let Some(prev_var) = self.block_var_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0002",
        format!("Conflicting block function and var declarations for `{raw_name}`"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_var),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }

    if let Some(prev_lexical) = self.block_lexical_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0002",
        format!("Conflicting block function and lexical declarations for `{raw_name}`"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_lexical),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }

    if let Some(prev_catch_param) = self.catch_param_decl_spans.get(&key).copied() {
      let mut diagnostic = Diagnostic::error(
        "BIND0001",
        format!("Identifier `{raw_name}` has already been declared"),
        Span::new(self.file, span),
      );
      diagnostic.push_label(Label::secondary(
        Span::new(self.file, prev_catch_param),
        "previous declaration here",
      ));
      self.diagnostics.push(diagnostic);
    }
  }

  fn record_catch_param_decl(&mut self, scope: ScopeId, name: NameId, span: TextRange) {
    let key = (scope, name);
    self.catch_param_decl_spans.entry(key).or_insert(span);
  }

  fn mark_tdz_binding(&mut self, scope: ScopeId, symbol: SymbolId) {
    if let Some(bindings) = self.scopes.get_mut(&scope).map(|s| &mut s.tdz_bindings) {
      if !bindings.contains(&symbol) {
        bindings.push(symbol);
      }
    }
  }

  fn mark_hoisted_binding(&mut self, scope: ScopeId, symbol: SymbolId) {
    if let Some(bindings) = self.scopes.get_mut(&scope).map(|s| &mut s.hoisted_bindings) {
      if !bindings.contains(&symbol) {
        bindings.push(symbol);
      }
    }
  }

  fn declare_in_scope_with_span(
    &mut self,
    scope: ScopeId,
    name: &str,
    flags: SymbolFlags,
    lexical: bool,
    span: Option<TextRange>,
  ) -> SymbolId {
    let name_id = self.intern_name(name);
    let existing = self
      .scopes
      .get(&scope)
      .and_then(|s| s.symbols.get(&name_id))
      .copied();

    let id = existing.unwrap_or_else(|| symbol_id_for(self.file, scope, name_id));

    if let Some(span) = span {
      let info = self.decl_spans.entry(id).or_default();
      let is_lexical = lexical;
      if is_lexical {
        if let Some(prev) = info.first_lexical {
          let mut diagnostic = Diagnostic::error(
            "BIND0001",
            format!("Identifier `{name}` has already been declared"),
            Span::new(self.file, span),
          );
          diagnostic.push_label(Label::secondary(
            Span::new(self.file, prev),
            "previous declaration here",
          ));
          self.diagnostics.push(diagnostic);
        } else if let Some(prev) = info.first_var {
          let mut diagnostic = Diagnostic::error(
            "BIND0002",
            format!("Conflicting lexical and var declarations for `{name}`"),
            Span::new(self.file, span),
          );
          diagnostic.push_label(Label::secondary(
            Span::new(self.file, prev),
            "previous declaration here",
          ));
          self.diagnostics.push(diagnostic);
        }
        info.first_lexical.get_or_insert(span);
      } else if info.first_var.is_none() {
        if let Some(prev) = info.first_lexical {
          let mut diagnostic = Diagnostic::error(
            "BIND0002",
            format!("Conflicting lexical and var declarations for `{name}`"),
            Span::new(self.file, span),
          );
          diagnostic.push_label(Label::secondary(
            Span::new(self.file, prev),
            "previous declaration here",
          ));
          self.diagnostics.push(diagnostic);
        }
        info.first_var = Some(span);
      }
    }

    if let Some(existing) = existing {
      self.update_flags(existing, flags);
      return existing;
    }
    if let Some(scope_data) = self.scopes.get_mut(&scope) {
      scope_data.symbols.insert(name_id, id);
    }
    self.symbols.entry(id).or_insert(SymbolData {
      name: name_id,
      decl_scope: scope,
      flags,
    });
    if flags.hoisted {
      self.mark_hoisted_binding(scope, id);
    }
    if flags.tdz {
      self.mark_tdz_binding(scope, id);
    }
    id
  }

  fn update_flags(&mut self, symbol: SymbolId, flags: SymbolFlags) {
    let (decl_scope, merged) = match self.symbols.get_mut(&symbol) {
      Some(data) => {
        let merged = data.flags.union(flags);
        data.flags = merged;
        (data.decl_scope, merged)
      }
      None => return,
    };
    if merged.hoisted {
      self.mark_hoisted_binding(decl_scope, symbol);
    }
    if merged.tdz {
      self.mark_tdz_binding(decl_scope, symbol);
    }
  }

  fn finish(self) -> (JsSemantics, Vec<Diagnostic>) {
    (
      JsSemantics {
        names: self.names,
        name_lookup: self.name_lookup,
        scopes: self.scopes,
        symbols: self.symbols,
        top_scope: self.top_scope,
      },
      self.diagnostics,
    )
  }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DeclTarget {
  IfNotGlobal,
  NearestClosure,
}

#[derive(Clone, Copy)]
struct DeclContext {
  target: DeclTarget,
  flags: SymbolFlags,
  lexical: bool,
  block_lexical: bool,
  block_var: bool,
  catch_param: bool,
}

#[derive(Clone, Copy, Debug)]
struct ForInOfContext {
  loop_scope: Option<ScopeId>,
  body_span: TextRange,
}

#[derive(VisitorMut)]
#[visitor(
  BlockStmtNode,
  CatchBlockNode,
  ClassDeclNode,
  ClassExprNode,
  ForBodyNode,
  ForInStmtNode(enter, exit),
  ForInOfLhs,
  ForOfStmtNode(enter, exit),
  ForTripleStmtNode(enter, exit),
  FuncDeclNode(enter),
  FuncExprNode,
  FuncNode,
  IdPatNode(enter),
  ImportStmtNode,
  PatDeclNode,
  SwitchStmtNode(enter, exit),
  SwitchBranchNode(enter),
  VarDeclNode,
  NodeAssocData(enter)
)]
struct DeclareVisitor {
  builder: SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  decl_target_stack: Vec<DeclContext>,
  in_pattern_decl: Vec<bool>,
  top_level_mode: TopLevelMode,
  closure_lexical_names_stack: Vec<BTreeSet<NameId>>,
  switch_scope_stack: Vec<(ScopeId, bool)>,
  for_in_of_stack: Vec<ForInOfContext>,
  for_in_of_lhs_scope_stack: Vec<Option<ScopeId>>,
  for_body_loop_scope_stack: Vec<Option<ScopeId>>,
  for_triple_scope_stack: Vec<bool>,
}

impl DeclareVisitor {
  fn new(mode: TopLevelMode, file: FileId, span: TextRange) -> Self {
    let builder = SemanticsBuilder::new(mode, file, span);
    let top_scope = builder.top_scope;
    Self {
      builder,
      scope_stack: vec![top_scope],
      decl_target_stack: Vec::new(),
      in_pattern_decl: vec![false],
      top_level_mode: mode,
      closure_lexical_names_stack: Vec::new(),
      switch_scope_stack: Vec::new(),
      for_in_of_stack: Vec::new(),
      for_in_of_lhs_scope_stack: Vec::new(),
      for_body_loop_scope_stack: Vec::new(),
      for_triple_scope_stack: Vec::new(),
    }
  }

  fn finish(self) -> (JsSemantics, Vec<Diagnostic>) {
    self.builder.finish()
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope(&mut self, kind: ScopeKind, span: TextRange) {
    let parent = self.current_scope();
    let id = self.builder.new_scope(parent, kind, span);
    self.scope_stack.push(id);
  }

  fn pop_scope(&mut self) {
    self.scope_stack.pop();
  }

  fn push_decl_target(&mut self, target: DeclTarget) {
    self.decl_target_stack.push(DeclContext {
      target,
      flags: SymbolFlags::default(),
      lexical: false,
      block_lexical: false,
      block_var: false,
      catch_param: false,
    });
  }

  fn push_decl_context(
    &mut self,
    target: DeclTarget,
    flags: SymbolFlags,
    lexical: bool,
    block_lexical: bool,
    block_var: bool,
    catch_param: bool,
  ) {
    self.decl_target_stack.push(DeclContext {
      target,
      flags,
      lexical,
      block_lexical,
      block_var,
      catch_param,
    });
  }

  fn pop_decl_target(&mut self) {
    self.decl_target_stack.pop();
  }

  fn in_pattern_decl(&self) -> bool {
    *self.in_pattern_decl.last().unwrap()
  }

  fn enter_pattern_decl(&mut self) {
    self.in_pattern_decl.push(true);
  }

  fn exit_pattern_decl(&mut self) {
    self.in_pattern_decl.pop();
  }

  fn nearest_closure(&self) -> Option<ScopeId> {
    self
      .scope_stack
      .iter()
      .rev()
      .copied()
      .find(|id| self.builder.scope_kind(*id).is_closure())
  }

  fn declare_with_target(
    &mut self,
    name: &str,
    ctx: DeclContext,
    span: TextRange,
  ) -> Option<(SymbolId, ScopeId)> {
    let name_id = self.builder.intern_name(name);

    if ctx.catch_param && self.builder.scope_kind(self.current_scope()) == ScopeKind::Block {
      self
        .builder
        .record_catch_param_decl(self.current_scope(), name_id, span);
    }

    // Static semantics: `var`-scoped declarations inside a block participate in
    // the block's `VarDeclaredNames`, so they cannot conflict with any lexical
    // declarations (`let`/`const`/`class`/block functions in modules) declared in
    // that same block.
    if ctx.block_var {
      for scope_id in self.scope_stack.iter().rev().copied() {
        let kind = self.builder.scope_kind(scope_id);
        if kind == ScopeKind::Block {
          self
            .builder
            .record_block_var_decl(scope_id, name_id, name, span);
        }
        if kind.is_closure() {
          break;
        }
      }
    }

    if ctx.block_lexical && self.builder.scope_kind(self.current_scope()) == ScopeKind::Block {
      self
        .builder
        .record_block_lexical_decl(self.current_scope(), name_id, name, span);
    }

    let (symbol, scope) = match ctx.target {
      DeclTarget::IfNotGlobal => {
        let scope = self.current_scope();
        if self.builder.scope_kind(scope) == ScopeKind::Global {
          None
        } else {
          Some((
            self.builder.declare_in_scope_with_span(
              scope,
              name,
              ctx.flags,
              ctx.lexical,
              Some(span),
            ),
            scope,
          ))
        }
      }
      DeclTarget::NearestClosure => {
        let scope = self.nearest_closure()?;
        Some((
          self
            .builder
            .declare_in_scope_with_span(scope, name, ctx.flags, ctx.lexical, Some(span)),
          scope,
        ))
      }
    }?;
    Some((symbol, scope))
  }

  fn declare_class_or_func_name(&mut self, node: &mut Node<ClassOrFuncName>, ctx: DeclContext) {
    let span = ident_range(node.loc, &node.stx.name);
    if let Some((symbol, _)) = self.declare_with_target(&node.stx.name, ctx, span) {
      node.assoc.set(DeclaredSymbol(symbol));
    }
  }

  fn enter_node_assoc_data(&mut self, assoc: &mut NodeAssocData) {
    assoc.set(self.current_scope());
  }
}

impl DeclareVisitor {
  fn enter_block_stmt_node(&mut self, node: &mut BlockStmtNode) {
    self.push_scope(ScopeKind::Block, range_of(node));
  }

  fn exit_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.pop_scope();
  }

  fn enter_catch_block_node(&mut self, node: &mut CatchBlockNode) {
    self.push_scope(ScopeKind::Block, range_of(node));
    // Catch parameters are lexical but initialized immediately (no TDZ).
    self.push_decl_context(
      DeclTarget::IfNotGlobal,
      SymbolFlags::default(),
      true,
      false,
      false,
      true,
    );
  }

  fn exit_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.pop_scope();
    self.pop_decl_target();
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(
        name,
        DeclContext {
          target: DeclTarget::IfNotGlobal,
          flags: SymbolFlags::lexical_tdz(),
          lexical: true,
          block_lexical: true,
          block_var: false,
          catch_param: false,
        },
      );
    }
    self.push_scope(ScopeKind::Class, range_of(node));
  }

  fn exit_class_decl_node(&mut self, _node: &mut ClassDeclNode) {
    self.pop_scope();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.push_scope(ScopeKind::Class, range_of(node));
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(
        name,
        DeclContext {
          target: DeclTarget::IfNotGlobal,
          flags: SymbolFlags::lexical_tdz(),
          lexical: true,
          block_lexical: true,
          block_var: false,
          catch_param: false,
        },
      );
    }
  }

  fn exit_class_expr_node(&mut self, _node: &mut ClassExprNode) {
    self.pop_scope();
  }

  fn enter_for_in_stmt_node(&mut self, node: &mut ForInStmtNode) {
    let loop_scope = match &node.stx.lhs {
      ForInOfLhs::Decl((mode, _))
        if matches!(
          mode,
          VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
        ) =>
      {
        Some(
          self
            .builder
            .new_scope(self.current_scope(), ScopeKind::Block, range_of(node)),
        )
      }
      _ => None,
    };
    self.for_in_of_stack.push(ForInOfContext {
      loop_scope,
      body_span: range_of(&node.stx.body),
    });
  }

  fn exit_for_in_stmt_node(&mut self, _node: &mut ForInStmtNode) {
    self.for_in_of_stack.pop();
  }

  fn enter_for_of_stmt_node(&mut self, node: &mut ForOfStmtNode) {
    let loop_scope = match &node.stx.lhs {
      ForInOfLhs::Decl((mode, _))
        if matches!(
          mode,
          VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
        ) =>
      {
        Some(
          self
            .builder
            .new_scope(self.current_scope(), ScopeKind::Block, range_of(node)),
        )
      }
      _ => None,
    };
    self.for_in_of_stack.push(ForInOfContext {
      loop_scope,
      body_span: range_of(&node.stx.body),
    });
  }

  fn exit_for_of_stmt_node(&mut self, _node: &mut ForOfStmtNode) {
    self.for_in_of_stack.pop();
  }

  fn enter_for_triple_stmt_node(&mut self, node: &mut ForTripleStmtNode) {
    let has_lexical_init = match &node.stx.init {
      ForTripleStmtInit::Decl(decl) => matches!(
        decl.stx.mode,
        VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
      ),
      _ => false,
    };
    self.for_triple_scope_stack.push(has_lexical_init);
    if has_lexical_init {
      self.push_scope(ScopeKind::Block, range_of(node));
    }
  }

  fn exit_for_triple_stmt_node(&mut self, _node: &mut ForTripleStmtNode) {
    if self.for_triple_scope_stack.pop().unwrap_or(false) {
      self.pop_scope();
    }
  }

  fn enter_for_body_node(&mut self, node: &mut ForBodyNode) {
    let mut loop_scope_pushed = None;
    if let Some(ctx) = self.for_in_of_stack.last() {
      let span = range_of(node);
      if span == ctx.body_span {
        if let Some(loop_scope) = ctx.loop_scope {
          self.scope_stack.push(loop_scope);
          loop_scope_pushed = Some(loop_scope);
        }
      }
    }
    self.for_body_loop_scope_stack.push(loop_scope_pushed);
    self.push_scope(ScopeKind::Block, range_of(node));
  }

  fn exit_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.pop_scope();
    if let Some(loop_scope) = self.for_body_loop_scope_stack.pop().flatten() {
      let popped = self.scope_stack.pop();
      debug_assert_eq!(popped, Some(loop_scope));
    }
  }

  fn enter_switch_stmt_node(&mut self, node: &mut SwitchStmtNode) {
    let parent = self.current_scope();
    let id = self
      .builder
      .new_scope(parent, ScopeKind::Block, range_of(node));
    self.switch_scope_stack.push((id, false));
  }

  fn enter_switch_branch_node(&mut self, _node: &mut SwitchBranchNode) {
    let Some((scope, active)) = self.switch_scope_stack.last_mut() else {
      return;
    };
    if *active {
      return;
    }
    self.scope_stack.push(*scope);
    *active = true;
  }

  fn exit_switch_stmt_node(&mut self, _node: &mut SwitchStmtNode) {
    let Some((scope, active)) = self.switch_scope_stack.pop() else {
      return;
    };
    if active {
      let popped = self.scope_stack.pop();
      debug_assert_eq!(popped, Some(scope));
    }
  }

  fn enter_for_in_of_lhs(&mut self, node: &mut ForInOfLhs) {
    let loop_scope = self.for_in_of_stack.last().and_then(|ctx| ctx.loop_scope);
    if let Some(scope) = loop_scope {
      self.scope_stack.push(scope);
    }
    self.for_in_of_lhs_scope_stack.push(loop_scope);

    if let ForInOfLhs::Decl((mode, _)) = node {
      let target = match mode {
        VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
          DeclTarget::IfNotGlobal
        }
        VarDeclMode::Var => DeclTarget::NearestClosure,
      };
      let flags = match mode {
        VarDeclMode::Var => SymbolFlags::hoisted(),
        VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
          SymbolFlags::lexical_tdz()
        }
      };
      self.push_decl_context(
        target,
        flags,
        flags.tdz,
        flags.tdz,
        matches!(mode, VarDeclMode::Var),
        false,
      );
    }
  }

  fn exit_for_in_of_lhs(&mut self, node: &mut ForInOfLhs) {
    if matches!(node, ForInOfLhs::Decl(_)) {
      self.pop_decl_target();
    }

    if let Some(scope) = self.for_in_of_lhs_scope_stack.pop().flatten() {
      let popped = self.scope_stack.pop();
      debug_assert_eq!(popped, Some(scope));
    }
  }

  fn enter_func_decl_node(&mut self, node: &mut FuncDeclNode) {
    if let Some(name) = &mut node.stx.name {
      let scope_kind = self.builder.scope_kind(self.current_scope());
      let span = ident_range(name.loc, &name.stx.name);
      let name_id = name_id_for(self.builder.file, &name.stx.name);

      if self.top_level_mode == TopLevelMode::Module {
        let is_module_function_decl = matches!(scope_kind, ScopeKind::Module | ScopeKind::Block);
        let target = if is_module_function_decl && scope_kind == ScopeKind::Block {
          DeclTarget::IfNotGlobal
        } else {
          DeclTarget::NearestClosure
        };
        self.declare_class_or_func_name(
          name,
          DeclContext {
            target,
            flags: SymbolFlags::hoisted(),
            lexical: is_module_function_decl,
            block_lexical: is_module_function_decl && scope_kind == ScopeKind::Block,
            block_var: false,
            catch_param: false,
          },
        );
        return;
      }

      // Non-module script: block-level functions are still `var` scoped but they
      // participate in block-level early errors (e.g. they conflict with
      // `var`/`let`/`const` declarations in the same block).
      if scope_kind == ScopeKind::Block {
        self
          .builder
          .record_block_func_decl(self.current_scope(), name_id, &name.stx.name, span);

        let Some(closure) = self.nearest_closure() else {
          return;
        };

        let suppress_hoist = self
          .closure_lexical_names_stack
          .last()
          .map_or(false, |names| names.contains(&name_id))
          || self
            .builder
            .scopes
            .get(&closure)
            .and_then(|s| s.symbols.get(&name_id))
            .and_then(|sym| self.builder.symbols.get(sym))
            .map(|sym| !sym.flags.hoisted)
            .unwrap_or(false);

        let target = if suppress_hoist {
          DeclTarget::IfNotGlobal
        } else {
          DeclTarget::NearestClosure
        };

        self.declare_class_or_func_name(
          name,
          DeclContext {
            target,
            flags: SymbolFlags::hoisted(),
            lexical: false,
            block_lexical: false,
            block_var: false,
            catch_param: false,
          },
        );
        return;
      }

      self.declare_class_or_func_name(
        name,
        DeclContext {
          target: DeclTarget::NearestClosure,
          flags: SymbolFlags::hoisted(),
          lexical: false,
          block_lexical: false,
          block_var: false,
          catch_param: false,
        },
      );
    }
  }

  fn enter_func_expr_node(&mut self, node: &mut FuncExprNode) {
    self.push_scope(ScopeKind::FunctionExpressionName, range_of(node));
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(
        name,
        DeclContext {
          target: DeclTarget::IfNotGlobal,
          flags: SymbolFlags::hoisted(),
          lexical: false,
          block_lexical: false,
          block_var: false,
          catch_param: false,
        },
      );
    }
  }

  fn exit_func_expr_node(&mut self, _node: &mut FuncExprNode) {
    self.pop_scope();
  }

  fn enter_func_node(&mut self, node: &mut FuncNode) {
    let lexicals = if self.top_level_mode == TopLevelMode::Global {
      closure_lexical_names(self.builder.file, node.stx.as_ref())
    } else {
      BTreeSet::new()
    };
    self.closure_lexical_names_stack.push(lexicals);

    let kind = if node.stx.arrow {
      ScopeKind::ArrowFunction
    } else {
      ScopeKind::NonArrowFunction
    };
    self.push_scope(kind, range_of(node));
    self.push_decl_target(DeclTarget::NearestClosure);
  }

  fn exit_func_node(&mut self, _node: &mut FuncNode) {
    self.pop_scope();
    self.pop_decl_target();
    self.closure_lexical_names_stack.pop();
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.in_pattern_decl() {
      if let Some(ctx) = self.decl_target_stack.last().copied() {
        let span = ident_range(node.loc, &node.stx.name);
        if let Some((symbol, _)) = self.declare_with_target(&node.stx.name, ctx, span) {
          node.assoc.set(DeclaredSymbol(symbol));
        }
      }
    }
  }

  fn enter_import_stmt_node(&mut self, _node: &mut ImportStmtNode) {
    // Import bindings are lexical but initialized before module evaluation (no TDZ).
    self.push_decl_context(
      DeclTarget::IfNotGlobal,
      SymbolFlags::default(),
      true,
      false,
      false,
      false,
    );
  }

  fn exit_import_stmt_node(&mut self, _node: &mut ImportStmtNode) {
    self.pop_decl_target();
  }

  fn enter_pat_decl_node(&mut self, _node: &mut PatDeclNode) {
    self.enter_pattern_decl();
  }

  fn exit_pat_decl_node(&mut self, _node: &mut PatDeclNode) {
    self.exit_pattern_decl();
  }

  fn enter_var_decl_node(&mut self, node: &mut VarDeclNode) {
    let target = match node.stx.mode {
      VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
        DeclTarget::IfNotGlobal
      }
      VarDeclMode::Var => DeclTarget::NearestClosure,
    };
    let flags = match node.stx.mode {
      VarDeclMode::Var => SymbolFlags::hoisted(),
      VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
        SymbolFlags::lexical_tdz()
      }
    };
    self.push_decl_context(
      target,
      flags,
      flags.tdz,
      flags.tdz,
      matches!(node.stx.mode, VarDeclMode::Var),
      false,
    );
  }

  fn exit_var_decl_node(&mut self, _node: &mut VarDeclNode) {
    self.pop_decl_target();
  }
}

#[derive(VisitorMut)]
#[visitor(CallExprNode(exit), WithStmtNode(enter))]
struct DynamicScopeVisitor<'a> {
  sem: &'a mut JsSemantics,
}

impl DynamicScopeVisitor<'_> {
  fn mark_dynamic(&mut self, scope: ScopeId, direct_eval: bool) {
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      let Some(data) = self.sem.scopes.get_mut(&scope_id) else {
        break;
      };
      data.is_dynamic = true;
      if direct_eval {
        data.has_direct_eval = true;
      }
      if data.kind.is_closure() {
        break;
      }
      current = data.parent;
    }
  }

  fn enter_with_stmt_node(&mut self, node: &mut WithStmtNode) {
    if let Some(scope) = scope_id(&node.assoc) {
      self.mark_dynamic(scope, false);
    }
    if let Stmt::Block(block) = node.stx.body.stx.as_ref() {
      if let Some(body_scope) = scope_id(&block.assoc) {
        self.mark_dynamic(body_scope, false);
      }
    }
  }

  fn exit_call_expr_node(&mut self, node: &mut CallExprNode) {
    if node.stx.optional_chaining {
      return;
    }
    if let Expr::Id(callee) = node.stx.callee.stx.as_ref() {
      if callee.stx.name == "eval" {
        if let Some(scope) = scope_id(&node.assoc) {
          if self.sem.resolve_name_in_scope(scope, "eval").is_none() {
            self.mark_dynamic(scope, true);
          }
        }
      }
    }
  }
}

fn mark_dynamic_scopes(top_level: &mut Node<TopLevel>, sem: &mut JsSemantics) {
  let mut visitor = DynamicScopeVisitor { sem };
  top_level.drive_mut(&mut visitor);
}

#[cfg(test)]
mod tests {
  use super::declare;
  use crate::assoc::js::scope_id;
  use crate::js::{ScopeId, ScopeKind, TopLevelMode};
  use derive_visitor::Drive;
  use derive_visitor::Visitor;
  use diagnostics::FileId;
  use parse_js::ast::expr::IdExpr;
  use parse_js::ast::node::Node;
  use parse_js::loc::Loc;
  use parse_js::parse;

  type IdExprNode = Node<IdExpr>;

  #[derive(Default, Visitor)]
  #[visitor(IdExprNode(enter))]
  struct IdCollector {
    seen: Vec<(String, ScopeId, Loc)>,
  }

  impl IdCollector {
    fn enter_id_expr_node(&mut self, node: &IdExprNode) {
      let scope = scope_id(&node.assoc).expect("expected scope id");
      self.seen.push((node.stx.name.clone(), scope, node.loc));
    }
  }

  #[test]
  fn builds_scope_tree() {
    let mut top = parse(
      "function outer(a) { let x; { const y = 1; } function inner(b) { var c; const d = () => { let e; }; } }",
    )
    .unwrap();
    let semantics = declare(&mut top, TopLevelMode::Module, FileId(100));
    let root = semantics.top_scope();
    assert_eq!(semantics.scope(root).kind, ScopeKind::Module);

    let outer = semantics.scope(root).children[0];
    assert_eq!(semantics.scope(outer).kind, ScopeKind::NonArrowFunction);

    let outer_children = &semantics.scope(outer).children;
    assert_eq!(outer_children.len(), 2);
    assert_eq!(semantics.scope(outer_children[0]).kind, ScopeKind::Block);
    assert_eq!(
      semantics.scope(outer_children[1]).kind,
      ScopeKind::NonArrowFunction
    );

    let inner = outer_children[1];
    let inner_children = &semantics.scope(inner).children;
    assert_eq!(inner_children.len(), 1);
    assert_eq!(
      semantics.scope(inner_children[0]).kind,
      ScopeKind::ArrowFunction
    );
  }

  #[test]
  fn for_in_of_declares_symbols() {
    let mut top = parse("for (let x of y) {} for (var z in y) {}").unwrap();
    let semantics = declare(&mut top, TopLevelMode::Module, FileId(101));
    let root = semantics.top_scope();
    let root_scope = semantics.scope(root);
    let x = semantics.name_id("x").unwrap();
    let z = semantics.name_id("z").unwrap();
    assert!(root_scope.symbols.contains_key(&z));
    assert!(!root_scope.symbols.contains_key(&x));

    let x_scopes: Vec<_> = semantics
      .scopes
      .iter()
      .filter(|(_, scope)| scope.symbols.contains_key(&x))
      .map(|(id, _)| *id)
      .collect();
    assert_eq!(x_scopes.len(), 1);
    assert_ne!(x_scopes[0], root);
  }

  #[test]
  fn global_mode_skips_top_level_symbols() {
    let mut top = parse("var a = 1; let b = 2; function f(c) { let d; } class C {}").unwrap();
    let semantics = declare(&mut top, TopLevelMode::Global, FileId(102));
    let root = semantics.top_scope();
    let root_scope = semantics.scope(root);
    assert!(root_scope.symbols.is_empty());

    let func_scope = semantics.scope(root).children[0];
    assert_eq!(
      semantics.scope(func_scope).kind,
      ScopeKind::NonArrowFunction
    );

    let c = semantics.name_id("c").unwrap();
    let d = semantics.name_id("d").unwrap();
    let func_scope = semantics.scope(func_scope);
    assert!(func_scope.symbols.contains_key(&c));
    assert!(func_scope.symbols.contains_key(&d));
  }

  #[test]
  fn attaches_scope_ids_per_node() {
    let mut parsed = parse(
      r#"
      let value = 0;
      function wrap() {
        {
          value;
        }
      }
      value;
    "#,
    )
    .unwrap();

    let semantics = declare(&mut parsed, TopLevelMode::Global, FileId(103));
    let mut collector = IdCollector::default();
    parsed.drive(&mut collector);

    collector.seen.sort_by_key(|(_, _, loc)| loc.0);
    assert_eq!(collector.seen.len(), 2);
    assert_eq!(collector.seen[0].0, "value");
    assert_eq!(collector.seen[1].0, "value");
    assert_ne!(collector.seen[0].1, collector.seen[1].1);
    assert_eq!(semantics.scope(collector.seen[1].1).kind, ScopeKind::Global);
  }
}
