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
use derive_visitor::{Drive, DriveMut, VisitorMut};
use diagnostics::{Diagnostic, FileId, Label, Span, TextRange};
use parse_js::ast::class_or_object::ClassStaticBlock;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::ClassExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::node::ParenthesizedExpr;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::BlockStmt;
use parse_js::ast::stmt::CatchBlock;
use parse_js::ast::stmt::DoWhileStmt;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stmt::ForInStmt;
use parse_js::ast::stmt::ForOfStmt;
use parse_js::ast::stmt::ForTripleStmt;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::IfStmt;
use parse_js::ast::stmt::LabelStmt;
use parse_js::ast::stmt::ImportStmt;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::SwitchBranch;
use parse_js::ast::stmt::SwitchStmt;
use parse_js::ast::stmt::WhileStmt;
use parse_js::ast::stmt::WithStmt;
use parse_js::ast::stx::TopLevel;
use std::collections::BTreeMap;

type BlockStmtNode = Node<BlockStmt>;
type CallExprNode = Node<CallExpr>;
type CatchBlockNode = Node<CatchBlock>;
type ClassStaticBlockNode = Node<ClassStaticBlock>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type FuncDeclNode = Node<FuncDecl>;
type FuncExprNode = Node<FuncExpr>;
type FuncNode = Node<Func>;
type ForBodyNode = Node<ForBody>;
type ForInStmtNode = Node<ForInStmt>;
type IfStmtNode = Node<IfStmt>;
type IdPatNode = Node<IdPat>;
type ImportStmtNode = Node<ImportStmt>;
type ForOfStmtNode = Node<ForOfStmt>;
type ForTripleStmtNode = Node<ForTripleStmt>;
type LabelStmtNode = Node<LabelStmt>;
type PatDeclNode = Node<PatDecl>;
type SwitchBranchNode = Node<SwitchBranch>;
type SwitchStmtNode = Node<SwitchStmt>;
type DoWhileStmtNode = Node<DoWhileStmt>;
type WhileStmtNode = Node<WhileStmt>;
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

fn has_use_strict_directive(stmts: &[Node<Stmt>]) -> bool {
  for stmt in stmts.iter() {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      break;
    };
    if expr_stmt
      .stx
      .expr
      .assoc
      .get::<ParenthesizedExpr>()
      .is_some()
    {
      break;
    }
    let Expr::LitStr(lit) = expr_stmt.stx.expr.stx.as_ref() else {
      break;
    };
    if lit.stx.value == "use strict" {
      return true;
    }
  }
  false
}

fn func_has_use_strict(func: &Func) -> bool {
  match &func.body {
    Some(FuncBody::Block(stmts)) => has_use_strict_directive(stmts),
    _ => false,
  }
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
  let strict = mode == TopLevelMode::Module || has_use_strict_directive(&top_level.stx.body);
  let mut visitor = DeclareVisitor::new(mode, file, range_of(top_level), strict);
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
  annex_b_function_decls: BTreeMap<SymbolId, SymbolId>,
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
      annex_b_function_decls: BTreeMap::new(),
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
        annex_b_function_decls: self.annex_b_function_decls,
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

#[derive(Debug, Clone, Copy)]
struct AnnexBBlockFunction {
  name: NameId,
  block_symbol: SymbolId,
  block_scope: ScopeId,
  closure_scope: Option<ScopeId>,
}

#[derive(Clone, Copy, Debug)]
enum StmtContext {
  /// A `StatementListItem` position (e.g. top-level, block bodies, switch case
  /// bodies, function bodies).
  StatementList,
  /// A single-statement position (e.g. the body of `if`, `while`, `for`, or a
  /// labelled statement).
  SingleStatement {
    allow_regular_function: bool,
  },
}

#[derive(VisitorMut)]
#[visitor(
  BlockStmtNode,
  CatchBlockNode,
  ClassDeclNode,
  ClassExprNode,
  ClassStaticBlockNode(enter, exit),
  DoWhileStmtNode(enter, exit),
  ForBodyNode,
  ForInStmtNode(enter, exit),
  ForInOfLhs,
  ForOfStmtNode(enter, exit),
  ForTripleStmtNode(enter, exit),
  ForTripleStmtInit(enter, exit),
  FuncDeclNode(enter),
  FuncExprNode,
  FuncNode,
  IdPatNode(enter),
  IfStmtNode(enter, exit),
  ImportStmtNode,
  LabelStmtNode(enter, exit),
  PatDeclNode,
  SwitchStmtNode(enter, exit),
  SwitchBranchNode(enter),
  VarDeclNode,
  WhileStmtNode(enter, exit),
  WithStmtNode(enter, exit),
  NodeAssocData(enter)
)]
struct DeclareVisitor {
  builder: SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  decl_target_stack: Vec<DeclContext>,
  in_pattern_decl: Vec<bool>,
  top_level_mode: TopLevelMode,
  strict_stack: Vec<bool>,
  stmt_context_stack: Vec<StmtContext>,
  switch_scope_stack: Vec<(ScopeId, bool)>,
  for_in_of_stack: Vec<ForInOfContext>,
  for_in_of_lhs_scope_stack: Vec<Option<ScopeId>>,
  for_body_loop_scope_stack: Vec<Option<ScopeId>>,
  for_triple_scope_stack: Vec<bool>,
  for_triple_init_stack: Vec<bool>,
  annex_b_block_functions: Vec<AnnexBBlockFunction>,
}

impl DeclareVisitor {
  fn new(mode: TopLevelMode, file: FileId, span: TextRange, strict: bool) -> Self {
    let builder = SemanticsBuilder::new(mode, file, span);
    let top_scope = builder.top_scope;
    Self {
      builder,
      scope_stack: vec![top_scope],
      decl_target_stack: Vec::new(),
      in_pattern_decl: vec![false],
      top_level_mode: mode,
      strict_stack: vec![strict],
      stmt_context_stack: vec![StmtContext::StatementList],
      switch_scope_stack: Vec::new(),
      for_in_of_stack: Vec::new(),
      for_in_of_lhs_scope_stack: Vec::new(),
      for_body_loop_scope_stack: Vec::new(),
      for_triple_scope_stack: Vec::new(),
      for_triple_init_stack: Vec::new(),
      annex_b_block_functions: Vec::new(),
    }
  }

  fn finish(mut self) -> (JsSemantics, Vec<Diagnostic>) {
    self.process_annex_b_block_functions();
    self.builder.finish()
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn process_annex_b_block_functions(&mut self) {
    let functions = std::mem::take(&mut self.annex_b_block_functions);
    for func in functions {
      let closure_scope = func.closure_scope;

      // Annex B hoisting is suppressed if any enclosing lexical environment
      // between the function's block and the nearest variable scope already
      // declares the same name. Catch parameters are excluded from this check
      // (they behave like a separate environment record in legacy semantics).
      let mut current = self
        .builder
        .scopes
        .get(&func.block_scope)
        .and_then(|scope| scope.parent);
      let mut suppressed = false;
      while let Some(scope_id) = current {
        if closure_scope.is_some_and(|closure| closure == scope_id) {
          break;
        }
        if let Some(scope) = self.builder.scopes.get(&scope_id) {
          if scope.symbols.contains_key(&func.name)
            && !self
              .builder
              .catch_param_decl_spans
              .contains_key(&(scope_id, func.name))
          {
            suppressed = true;
            break;
          }
        }
        current = self
          .builder
          .scopes
          .get(&scope_id)
          .and_then(|scope| scope.parent);
      }
      if suppressed {
        continue;
      }

      let Some(closure_scope) = closure_scope else {
        // Global scripts still create a `var` binding for Annex B block
        // functions, but in `TopLevelMode::Global` we intentionally do not
        // surface global bindings as renameable symbols. Create a synthetic
        // symbol ID to link the block binding so downstream renamers can keep
        // the original identifier text.
        let global_scope = self.builder.top_scope;
        let global_symbol = symbol_id_for(self.builder.file, global_scope, func.name);
        self
          .builder
          .symbols
          .entry(global_symbol)
          .or_insert(SymbolData {
            name: func.name,
            decl_scope: global_scope,
            flags: SymbolFlags::hoisted(),
          });
        self
          .builder
          .annex_b_function_decls
          .insert(func.block_symbol, global_symbol);
        continue;
      };

      // If the nearest variable scope already has a non-hoisted binding
      // (parameters or lexical declarations), hoisting is suppressed.
      if let Some(existing) = self
        .builder
        .scopes
        .get(&closure_scope)
        .and_then(|scope| scope.symbols.get(&func.name))
        .copied()
      {
        let is_hoisted = self
          .builder
          .symbols
          .get(&existing)
          .map(|sym| sym.flags.hoisted)
          .unwrap_or(false);
        if !is_hoisted {
          continue;
        }
        self
          .builder
          .annex_b_function_decls
          .insert(func.block_symbol, existing);
        continue;
      }

      let name = self
        .builder
        .names
        .get(&func.name)
        .cloned()
        .expect("annex b function name interned");
      let var_symbol = self.builder.declare_in_scope_with_span(
        closure_scope,
        &name,
        SymbolFlags::hoisted(),
        false,
        None,
      );
      self
        .builder
        .annex_b_function_decls
        .insert(func.block_symbol, var_symbol);
    }
  }

  fn is_strict(&self) -> bool {
    *self.strict_stack.last().unwrap_or(&false)
  }

  fn current_stmt_context(&self) -> StmtContext {
    *self
      .stmt_context_stack
      .last()
      .unwrap_or(&StmtContext::StatementList)
  }

  fn in_statement_list(&self) -> bool {
    matches!(self.current_stmt_context(), StmtContext::StatementList)
  }

  fn in_for_triple_init_decl(&self) -> bool {
    self.for_triple_init_stack.last().copied().unwrap_or(false)
  }

  fn push_stmt_context(&mut self, ctx: StmtContext) {
    self.stmt_context_stack.push(ctx);
  }

  fn pop_stmt_context(&mut self) {
    self.stmt_context_stack.pop();
  }

  fn report_invalid_statement_declaration(&mut self, message: &str, range: TextRange) {
    self.builder.diagnostics.push(Diagnostic::error(
      "BIND0004",
      message.to_string(),
      Span::new(self.builder.file, range),
    ));
  }

  fn report_invalid_lexical_declaration(&mut self, keyword_loc: parse_js::loc::Loc, keyword: &str) {
    self.report_invalid_statement_declaration(
      "Lexical declaration cannot appear in a single-statement context",
      ident_range(keyword_loc, keyword),
    );
  }

  fn report_invalid_class_declaration(&mut self, node: &Node<ClassDecl>) {
    let start = node.loc.start_u32();
    let range = TextRange::new(start, start.saturating_add("class".len() as u32));
    self.report_invalid_statement_declaration(
      "Class declaration cannot appear in a single-statement context",
      range,
    );
  }

  fn report_invalid_function_declaration(&mut self, node: &Node<FuncDecl>) {
    let start = node.loc.start_u32();
    let message = if node.stx.function.stx.async_ {
      "Async functions can only be declared at the top level or inside a block."
    } else if node.stx.function.stx.generator {
      if self.is_strict() {
        "In strict mode code, functions can only be declared at top level or inside a block."
      } else {
        "Generators can only be declared at the top level or inside a block."
      }
    } else if self.is_strict() {
      "In strict mode code, functions can only be declared at top level or inside a block."
    } else {
      "In non-strict mode code, functions can only be declared at top level, inside a block, or as the body of an if statement."
    };
    self.report_invalid_statement_declaration(
      message,
      TextRange::new(start, start.saturating_add("function".len() as u32)),
    );
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
      .find(|id| self.builder.scope_kind(*id).is_var_scope())
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
        if kind.is_var_scope() {
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
  fn enter_do_while_stmt_node(&mut self, _node: &mut DoWhileStmtNode) {
    self.push_stmt_context(StmtContext::SingleStatement {
      allow_regular_function: false,
    });
  }

  fn exit_do_while_stmt_node(&mut self, _node: &mut DoWhileStmtNode) {
    self.pop_stmt_context();
  }

  fn enter_if_stmt_node(&mut self, _node: &mut IfStmtNode) {
    self.push_stmt_context(StmtContext::SingleStatement {
      allow_regular_function: !self.is_strict(),
    });
  }

  fn exit_if_stmt_node(&mut self, _node: &mut IfStmtNode) {
    self.pop_stmt_context();
  }

  fn enter_while_stmt_node(&mut self, _node: &mut WhileStmtNode) {
    self.push_stmt_context(StmtContext::SingleStatement {
      allow_regular_function: false,
    });
  }

  fn exit_while_stmt_node(&mut self, _node: &mut WhileStmtNode) {
    self.pop_stmt_context();
  }

  fn enter_with_stmt_node(&mut self, _node: &mut WithStmtNode) {
    self.push_stmt_context(StmtContext::SingleStatement {
      allow_regular_function: false,
    });
  }

  fn exit_with_stmt_node(&mut self, _node: &mut WithStmtNode) {
    self.pop_stmt_context();
  }

  fn enter_label_stmt_node(&mut self, _node: &mut LabelStmtNode) {
    let allow_regular_function = !self.is_strict() && self.in_statement_list();
    self.push_stmt_context(StmtContext::SingleStatement {
      allow_regular_function,
    });
  }

  fn exit_label_stmt_node(&mut self, _node: &mut LabelStmtNode) {
    self.pop_stmt_context();
  }

  fn enter_for_triple_stmt_init(&mut self, node: &mut ForTripleStmtInit) {
    self
      .for_triple_init_stack
      .push(matches!(node, ForTripleStmtInit::Decl(_)));
  }

  fn exit_for_triple_stmt_init(&mut self, _node: &mut ForTripleStmtInit) {
    self.for_triple_init_stack.pop();
  }

  fn enter_block_stmt_node(&mut self, node: &mut BlockStmtNode) {
    self.push_stmt_context(StmtContext::StatementList);
    self.push_scope(ScopeKind::Block, range_of(node));
  }

  fn exit_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.pop_scope();
    self.pop_stmt_context();
  }

  fn enter_catch_block_node(&mut self, node: &mut CatchBlockNode) {
    self.push_stmt_context(StmtContext::StatementList);
    self.push_scope(ScopeKind::Block, range_of(node));
    // Catch parameters are lexical bindings. They behave like other lexical
    // bindings during destructuring initialization (default initializers can
    // observe TDZ-like ordering), but are fully initialized before the catch
    // body executes.
    self.push_decl_context(
      DeclTarget::IfNotGlobal,
      SymbolFlags::lexical_tdz(),
      true,
      false,
      false,
      true,
    );
  }

  fn exit_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.pop_scope();
    self.pop_decl_target();
    self.pop_stmt_context();
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    if !self.in_statement_list() {
      self.report_invalid_class_declaration(node);
    }
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
    // Class bodies are always strict mode.
    self.strict_stack.push(true);
    self.push_scope(ScopeKind::Class, range_of(node));
  }

  fn exit_class_decl_node(&mut self, _node: &mut ClassDeclNode) {
    self.pop_scope();
    self.strict_stack.pop();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    // Class bodies are always strict mode.
    self.strict_stack.push(true);
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
    self.strict_stack.pop();
  }

  fn enter_class_static_block_node(&mut self, node: &mut ClassStaticBlockNode) {
    self.push_stmt_context(StmtContext::StatementList);
    self.push_scope(ScopeKind::StaticBlock, range_of(node));
  }

  fn exit_class_static_block_node(&mut self, _node: &mut ClassStaticBlockNode) {
    self.pop_scope();
    self.pop_stmt_context();
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

    let span = range_of(node);
    let is_braced = if node.stx.body.is_empty() {
      true
    } else {
      let first = &node.stx.body[0];
      span.start < range_of(first).start
    };
    if is_braced {
      self.push_stmt_context(StmtContext::StatementList);
    } else {
      self.push_stmt_context(StmtContext::SingleStatement {
        allow_regular_function: false,
      });
    }

    self.push_scope(ScopeKind::Block, range_of(node));
  }

  fn exit_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.pop_scope();
    self.pop_stmt_context();
    if let Some(loop_scope) = self.for_body_loop_scope_stack.pop().flatten() {
      let popped = self.scope_stack.pop();
      debug_assert_eq!(popped, Some(loop_scope));
    }
  }

  fn enter_switch_stmt_node(&mut self, node: &mut SwitchStmtNode) {
    self.push_stmt_context(StmtContext::StatementList);
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
    self.pop_stmt_context();
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
    let stmt_ctx = self.current_stmt_context();
    let func = &node.stx.function.stx;
    let is_regular = !func.async_ && !func.generator;
    let func_allowed = match stmt_ctx {
      StmtContext::StatementList => true,
      StmtContext::SingleStatement {
        allow_regular_function,
      } => allow_regular_function && is_regular,
    };
    if !func_allowed {
      self.report_invalid_function_declaration(node);
    }

    if let Some(name) = &mut node.stx.name {
      let scope_kind = self.builder.scope_kind(self.current_scope());
      let span = ident_range(name.loc, &name.stx.name);

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

      if scope_kind == ScopeKind::Block && self.is_strict() {
        // Strict mode: block-level functions are block-scoped declarations.
        self.declare_class_or_func_name(
          name,
          DeclContext {
            target: DeclTarget::IfNotGlobal,
            flags: SymbolFlags::hoisted(),
            lexical: true,
            block_lexical: true,
            block_var: false,
            catch_param: false,
          },
        );
        return;
      }

      // Non-strict script: block-level functions are `var` scoped but still
      // participate in block-level early errors (e.g. they conflict with
      // `var`/`let`/`const` declarations in the same block). Annex B additionally
      // creates a hoisted `var` binding in the nearest variable scope unless the
      // name is shadowed by an enclosing lexical binding.
      if scope_kind == ScopeKind::Block {
        let block_scope = self.current_scope();
        let name_id = self.builder.intern_name(&name.stx.name);

        self
          .builder
          .record_block_func_decl(block_scope, name_id, &name.stx.name, span);

        let block_symbol = self.builder.declare_in_scope_with_span(
          block_scope,
          &name.stx.name,
          SymbolFlags::hoisted(),
          false,
          None,
        );
        name.assoc.set(DeclaredSymbol(block_symbol));

        self.annex_b_block_functions.push(AnnexBBlockFunction {
          name: name_id,
          block_symbol,
          block_scope,
          closure_scope: self.nearest_closure(),
        });
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
    let strict = self.is_strict() || func_has_use_strict(node.stx.as_ref());
    self.strict_stack.push(strict);
    self.push_stmt_context(StmtContext::StatementList);

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
    self.strict_stack.pop();
    self.pop_stmt_context();
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
    let is_lexical = matches!(
      node.stx.mode,
      VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
    );
    if is_lexical && !self.in_for_triple_init_decl() && !self.in_statement_list() {
      let keyword = match node.stx.mode {
        VarDeclMode::Const => "const",
        VarDeclMode::Let => "let",
        VarDeclMode::Using => "using",
        VarDeclMode::AwaitUsing => "await",
        VarDeclMode::Var => "var",
      };
      self.report_invalid_lexical_declaration(node.loc, keyword);
    }

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

fn mark_dynamic(sem: &mut JsSemantics, scope: ScopeId, direct_eval: bool) {
  let mut current = Some(scope);
  while let Some(scope_id) = current {
    let Some(data) = sem.scopes.get_mut(&scope_id) else {
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

#[derive(VisitorMut)]
#[visitor(NodeAssocData(enter))]
struct WithBodyDynamicMarker<'a> {
  sem: &'a mut JsSemantics,
}

impl WithBodyDynamicMarker<'_> {
  fn enter_node_assoc_data(&mut self, assoc: &mut NodeAssocData) {
    if let Some(scope) = scope_id(assoc) {
      mark_dynamic(self.sem, scope, false);
    }
  }
}

#[derive(VisitorMut)]
#[visitor(CallExprNode(exit), WithStmtNode(enter))]
struct DynamicScopeVisitor<'a> {
  sem: &'a mut JsSemantics,
}

impl DynamicScopeVisitor<'_> {
  fn enter_with_stmt_node(&mut self, node: &mut WithStmtNode) {
    if let Some(scope) = scope_id(&node.assoc) {
      mark_dynamic(self.sem, scope, false);
    }
    if let Stmt::Block(block) = node.stx.body.stx.as_ref() {
      if let Some(body_scope) = scope_id(&block.assoc) {
        mark_dynamic(self.sem, body_scope, false);
      }
    }

    // Scopes created within the `with (...) { ... }` body inherit the dynamic
    // scope chain (the object environment record becomes part of their outer
    // environment). Mark them dynamic too so downstream consumers avoid
    // semantics-changing rewrites in nested functions.
    let sem = &mut *self.sem;
    let mut marker = WithBodyDynamicMarker { sem };
    node.stx.body.drive_mut(&mut marker);
  }

  fn exit_call_expr_node(&mut self, node: &mut CallExprNode) {
    if node.stx.optional_chaining {
      return;
    }
    if let Expr::Id(callee) = node.stx.callee.stx.as_ref() {
      if callee.stx.name == "eval" {
        if let Some(scope) = scope_id(&node.assoc) {
          if self.sem.resolve_name_in_scope(scope, "eval").is_none() {
            mark_dynamic(self.sem, scope, true);
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
