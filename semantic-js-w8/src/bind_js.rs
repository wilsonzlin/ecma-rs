use crate::data::resolve_in_scope;
use crate::data::BoundFile;
use crate::data::ScopeData;
use crate::data::ScopeId;
use crate::data::ScopeKind;
use crate::data::SymbolData;
use crate::data::SymbolFlags;
use crate::data::SymbolId;
use crate::data::SymbolKind;
use crate::intern::NameId;
use crate::intern::NameInterner;
use crate::intern::NameTable;
use diagnostics_w8::Diagnostic;
use diagnostics_w8::Label;
use diagnostics_w8::Span;
use hir_js_w8::Binding;
use hir_js_w8::BodyId;
use hir_js_w8::BodyStore;
use hir_js_w8::ExprId;
use hir_js_w8::ExprKind;
use hir_js_w8::FileId;
use hir_js_w8::HirFile;
use hir_js_w8::Stmt;
use hir_js_w8::StmtKind;
use hir_js_w8::TopLevelMode;
use hir_js_w8::VarDecl;
use hir_js_w8::VarDeclKind;
use rustc_hash::FxHashMap;

pub fn bind_js(file: FileId, hir: &HirFile, bodies: &BodyStore) -> (BoundFile, Vec<Diagnostic>) {
  let mut binder = Binder::new(file);
  let root_kind = match hir.top_level {
    TopLevelMode::Global => ScopeKind::Global,
    TopLevelMode::Module => ScopeKind::Module,
  };
  let root_scope = binder.new_scope(None, root_kind);
  binder.bound.root_scope = root_scope;
  binder.bind_body(bodies, hir.root_body, root_scope);
  binder.finish()
}

struct Binder {
  bound: BoundFile,
  interner: NameInterner,
  diagnostics: Vec<Diagnostic>,
  pending_uses: Vec<(ExprId, ScopeId, NameId)>,
}

impl Binder {
  fn new(file: FileId) -> Self {
    Self {
      bound: BoundFile {
        file,
        root_scope: ScopeId(0),
        scopes: Vec::new(),
        symbols: Vec::new(),
        uses: Vec::new(),
        expr_scopes: FxHashMap::default(),
        names: NameTable::default(),
        def_spans: FxHashMap::default(),
      },
      interner: NameInterner::new(),
      diagnostics: Vec::new(),
      pending_uses: Vec::new(),
    }
  }

  fn finish(mut self) -> (BoundFile, Vec<Diagnostic>) {
    for (expr, scope, name) in self.pending_uses.drain(..) {
      if let Some(sym) = resolve_in_scope(&self.bound, scope, name) {
        self.bound.uses.push((expr, sym));
      }
    }
    self.bound.names = self.interner.into_table();
    (self.bound, self.diagnostics)
  }

  fn new_scope(&mut self, parent: Option<ScopeId>, kind: ScopeKind) -> ScopeId {
    let id = ScopeId(self.bound.scopes.len() as u32);
    self.bound.scopes.push(ScopeData::new(parent, kind));
    id
  }

  fn new_symbol(
    &mut self,
    name: NameId,
    scope: ScopeId,
    kind: SymbolKind,
    flags: SymbolFlags,
  ) -> SymbolId {
    let id = SymbolId(self.bound.symbols.len() as u32);
    self.bound.symbols.push(SymbolData {
      name,
      kind,
      flags,
      decls: Vec::new(),
      scope,
    });
    id
  }

  fn bind_body(&mut self, bodies: &BodyStore, body: BodyId, scope: ScopeId) {
    let stmts = &bodies.body(body).statements;
    self.predeclare_block(stmts, scope);
    for stmt in stmts {
      self.bind_stmt(bodies, stmt, scope);
    }
  }

  fn predeclare_block(&mut self, stmts: &[Stmt], scope: ScopeId) {
    for stmt in stmts {
      match &stmt.kind {
        StmtKind::Var(var_decl) => self.bind_var_decl(scope, var_decl),
        StmtKind::Function(func_decl) => self.declare_function(scope, func_decl),
        StmtKind::Class(class_decl) => {
          if let Some(name) = &class_decl.name {
            let binding = Binding::new(class_decl.id, name.clone(), class_decl.range);
            self.declare_binding(scope, &binding, SymbolKind::Class, SymbolFlags::CLASS);
          }
        }
        StmtKind::Import(import_decl) => self.bind_import(import_decl),
        StmtKind::Block(_) | StmtKind::Expr(_) => {}
        StmtKind::Catch(_) => {}
      }
    }
  }

  fn bind_stmt(&mut self, bodies: &BodyStore, stmt: &Stmt, scope: ScopeId) {
    match &stmt.kind {
      StmtKind::Block(stmts) => {
        let block_scope = self.new_scope(Some(scope), ScopeKind::Block);
        self.predeclare_block(stmts, block_scope);
        for stmt in stmts {
          self.bind_stmt(bodies, stmt, block_scope);
        }
      }
      StmtKind::Var(_) => {}
      StmtKind::Function(func_decl) => self.bind_function_decl(bodies, scope, func_decl),
      StmtKind::Class(class_decl) => self.bind_class_decl(bodies, scope, class_decl),
      StmtKind::Expr(expr) => self.bind_expr(bodies, *expr, scope),
      StmtKind::Import(_) => {}
      StmtKind::Catch(catch_block) => {
        let catch_scope = self.new_scope(Some(scope), ScopeKind::Catch);
        if let Some(binding) = &catch_block.param {
          self.declare_binding(
            catch_scope,
            binding,
            SymbolKind::Catch,
            SymbolFlags::CATCH | SymbolFlags::LET,
          );
        }
        self.predeclare_block(&catch_block.body, catch_scope);
        for stmt in &catch_block.body {
          self.bind_stmt(bodies, stmt, catch_scope);
        }
      }
    }
  }

  fn bind_var_decl(&mut self, scope: ScopeId, var_decl: &VarDecl) {
    let (target_scope, kind, flags) = match var_decl.kind {
      VarDeclKind::Var => (self.var_scope(scope), SymbolKind::Var, SymbolFlags::VAR),
      VarDeclKind::Let => (scope, SymbolKind::Let, SymbolFlags::LET),
      VarDeclKind::Const => (scope, SymbolKind::Const, SymbolFlags::CONST),
      VarDeclKind::Using | VarDeclKind::AwaitUsing => (scope, SymbolKind::Let, SymbolFlags::LET),
    };
    for binding in &var_decl.decls {
      self.declare_binding(target_scope, binding, kind, flags);
    }
  }

  fn declare_function(&mut self, scope: ScopeId, decl: &hir_js_w8::FunctionDecl) {
    let binding = Binding::new(decl.id, decl.name.clone(), decl.range);
    let target_scope = self.var_scope(scope);
    self.declare_binding(
      target_scope,
      &binding,
      SymbolKind::Function,
      SymbolFlags::FUNCTION | SymbolFlags::VAR,
    );
  }

  fn bind_function_decl(
    &mut self,
    bodies: &BodyStore,
    scope: ScopeId,
    decl: &hir_js_w8::FunctionDecl,
  ) {
    let func_scope = self.new_scope(
      Some(scope),
      if decl.is_arrow {
        ScopeKind::ArrowFunction
      } else {
        ScopeKind::Function
      },
    );
    for param in &decl.params {
      self.declare_binding(
        func_scope,
        param,
        SymbolKind::Param,
        SymbolFlags::PARAMETER | SymbolFlags::VAR,
      );
    }
    self.bind_body(bodies, decl.body, func_scope);
  }

  fn bind_class_decl(&mut self, bodies: &BodyStore, scope: ScopeId, decl: &hir_js_w8::ClassDecl) {
    let class_scope = self.new_scope(Some(scope), ScopeKind::Class);
    self.bind_body(bodies, decl.body, class_scope);
  }

  fn bind_import(&mut self, import_decl: &hir_js_w8::ImportDecl) {
    let scope = self.bound.root_scope;
    for binding in &import_decl.bindings {
      self.declare_binding(scope, binding, SymbolKind::Import, SymbolFlags::IMPORT);
    }
  }

  fn bind_expr(&mut self, bodies: &BodyStore, expr: ExprId, scope: ScopeId) {
    let expr_data = bodies.expr(expr);
    match &expr_data.kind {
      ExprKind::Name(name) => {
        self.bound.expr_scopes.insert(expr, scope);
        let name_id = self.interner.intern(name.clone());
        if let Some(sym) = resolve_in_scope(&self.bound, scope, name_id) {
          self.bound.uses.push((expr, sym));
        } else {
          self.pending_uses.push((expr, scope, name_id));
        }
      }
      ExprKind::Function(func_expr) => self.bind_function_expr(bodies, scope, func_expr),
      ExprKind::Class(class_expr) => self.bind_class_expr(bodies, scope, class_expr),
      ExprKind::Call { callee, args } => {
        self.bind_expr(bodies, *callee, scope);
        for arg in args {
          self.bind_expr(bodies, *arg, scope);
        }
      }
      ExprKind::Block(stmts) => {
        let block_scope = self.new_scope(Some(scope), ScopeKind::Block);
        for stmt in stmts {
          self.bind_stmt(bodies, stmt, block_scope);
        }
      }
    }
  }

  fn bind_function_expr(
    &mut self,
    bodies: &BodyStore,
    scope: ScopeId,
    expr: &hir_js_w8::FunctionExpr,
  ) {
    let mut parent_scope = scope;
    if let Some(binding) = &expr.name {
      let name_scope = self.new_scope(Some(scope), ScopeKind::Function);
      self.declare_binding(
        name_scope,
        binding,
        SymbolKind::Function,
        SymbolFlags::FUNCTION | SymbolFlags::VAR,
      );
      parent_scope = name_scope;
    }

    let func_scope = self.new_scope(
      Some(parent_scope),
      if expr.is_arrow {
        ScopeKind::ArrowFunction
      } else {
        ScopeKind::Function
      },
    );
    for param in &expr.params {
      self.declare_binding(
        func_scope,
        param,
        SymbolKind::Param,
        SymbolFlags::PARAMETER | SymbolFlags::VAR,
      );
    }
    self.bind_body(bodies, expr.body, func_scope);
  }

  fn bind_class_expr(&mut self, bodies: &BodyStore, scope: ScopeId, expr: &hir_js_w8::ClassExpr) {
    let class_scope = self.new_scope(Some(scope), ScopeKind::Class);
    if let Some(binding) = &expr.name {
      self.declare_binding(class_scope, binding, SymbolKind::Class, SymbolFlags::CLASS);
    }
    self.bind_body(bodies, expr.body, class_scope);
  }

  fn var_scope(&self, mut scope: ScopeId) -> ScopeId {
    loop {
      let data = &self.bound.scopes[scope.0 as usize];
      match data.kind {
        ScopeKind::Function | ScopeKind::ArrowFunction | ScopeKind::Module | ScopeKind::Global => {
          return scope
        }
        _ => {}
      }
      if let Some(parent) = data.parent {
        scope = parent;
      } else {
        return scope;
      }
    }
  }

  fn declare_binding(
    &mut self,
    scope: ScopeId,
    binding: &Binding,
    kind: SymbolKind,
    flags: SymbolFlags,
  ) {
    let name_id = self.interner.intern(binding.name.clone());
    self.bound.def_spans.insert(binding.id, binding.range);
    let existing = self.bound.scopes[scope.0 as usize]
      .symbol_map
      .get(&name_id)
      .copied();
    if let Some(sym_id) = existing {
      self.merge_symbol(sym_id, binding, flags);
      return;
    }

    let sym_id = self.new_symbol(name_id, scope, kind, flags);
    let scope_data = &mut self.bound.scopes[scope.0 as usize];
    scope_data.symbol_map.insert(name_id, sym_id);
    scope_data.symbols.push(sym_id);
    self.bound.symbols[sym_id.0 as usize].decls.push(binding.id);
  }

  fn merge_symbol(&mut self, sym_id: SymbolId, binding: &Binding, flags: SymbolFlags) {
    let data = &mut self.bound.symbols[sym_id.0 as usize];
    let allowed = Self::is_var_like(data.flags) && Self::is_var_like(flags);
    data.flags |= flags;
    data.decls.push(binding.id);
    self.bound.def_spans.insert(binding.id, binding.range);

    if allowed {
      return;
    }

    let Some(name) = self.interner.resolve(data.name) else {
      return;
    };
    let primary = Span::new(self.bound.file, binding.range);
    let mut diag = Diagnostic::new("E0001", format!("redeclaration of '{name}'"), primary);
    if let Some(prev) = data
      .decls
      .first()
      .and_then(|d| self.bound.def_spans.get(d))
      .copied()
    {
      diag = diag.with_label(Label::new(
        Span::new(self.bound.file, prev),
        "previous declaration",
      ));
    }
    self.diagnostics.push(diag);
  }

  fn is_var_like(flags: SymbolFlags) -> bool {
    flags.intersects(SymbolFlags::VAR | SymbolFlags::FUNCTION | SymbolFlags::PARAMETER)
  }
}
