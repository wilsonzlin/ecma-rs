use hir_js::Binding;
use hir_js::Body;
use hir_js::BodyId;
use hir_js::BodyStore;
use hir_js::Expr;
use hir_js::ExprId;
use hir_js::ExprKind;
use hir_js::FileId;
use hir_js::FunctionExpr;
use hir_js::HirFile;
use hir_js::Stmt;
use hir_js::StmtKind;
use hir_js::TextRange;
use hir_js::TopLevelMode;
use hir_js::VarDecl;
use hir_js::VarDeclKind;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use semantic_js::bind_js;
use semantic_js::resolve_in_scope;
use semantic_js::symbol_at_offset;
use semantic_js::BoundFile;
use semantic_js::ScopeId;
use semantic_js::ScopeKind;
use semantic_js::SymbolId;

#[derive(Default)]
struct HirBuilder {
  bodies: BodyStore,
  next_def: u32,
  next_offset: u32,
}

impl HirBuilder {
  fn new() -> Self {
    Self::default()
  }

  fn range(&mut self) -> TextRange {
    let start = self.next_offset;
    self.next_offset += 1;
    TextRange::new(start, start + 1)
  }

  fn alloc_def(&mut self) -> hir_js::DefId {
    let id = hir_js::DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn binding(&mut self, name: &str) -> Binding {
    Binding::new(self.alloc_def(), name.to_string(), self.range())
  }

  fn name_expr(&mut self, name: &str) -> ExprId {
    let range = self.range();
    let expr = Expr {
      range,
      kind: ExprKind::Name(name.to_string()),
    };
    self.bodies.alloc_expr(expr)
  }

  fn expr_stmt(&mut self, name: &str) -> Stmt {
    let expr = self.name_expr(name);
    let range = self.bodies.expr(expr).range;
    Stmt {
      range,
      kind: StmtKind::Expr(expr),
    }
  }

  fn block(&mut self, statements: Vec<Stmt>) -> Stmt {
    let range = self.range();
    Stmt {
      range,
      kind: StmtKind::Block(statements),
    }
  }

  fn var_stmt(&mut self, kind: VarDeclKind, names: &[&str]) -> Stmt {
    let decls = names.iter().map(|n| self.binding(n)).collect();
    let range = self.range();
    Stmt {
      range,
      kind: StmtKind::Var(VarDecl { decls, kind, range }),
    }
  }

  fn function_expr(
    &mut self,
    is_arrow: bool,
    name: Option<&str>,
    params: Vec<Binding>,
    body_statements: Vec<Stmt>,
  ) -> ExprId {
    let body = self.bodies.alloc_body(Body::new(body_statements));
    let range = self.range();
    let expr = Expr {
      range,
      kind: ExprKind::Function(FunctionExpr {
        name: name.map(|n| self.binding(n)),
        params,
        body,
        is_arrow,
        range,
      }),
    };
    self.bodies.alloc_expr(expr)
  }
}

struct ExpectScope<'a> {
  kind: ScopeKind,
  symbols: Vec<(&'a str, &'a str)>,
  children: Vec<ExpectScope<'a>>,
}

fn assert_scope_tree<'a>(
  bound: &BoundFile,
  scope: ScopeId,
  expect: &ExpectScope<'a>,
  out: &mut FxHashMap<&'a str, SymbolId>,
) {
  let data = &bound.scopes[scope.0 as usize];
  assert_eq!(data.kind, expect.kind);
  assert_eq!(data.symbols.len(), expect.symbols.len());
  for (i, (name, key)) in expect.symbols.iter().enumerate() {
    let sym_id = data.symbols[i];
    let sym = &bound.symbols[sym_id.0 as usize];
    assert_eq!(bound.name(sym.name).unwrap(), *name);
    assert!(out.insert(*key, sym_id).is_none());
  }

  let mut children: Vec<ScopeId> = bound
    .scopes
    .iter()
    .enumerate()
    .filter_map(|(i, s)| (s.parent == Some(scope)).then_some(ScopeId(i as u32)))
    .collect();
  children.sort_by_key(|s| s.0);
  assert_eq!(children.len(), expect.children.len());
  for (child, expect_child) in children.into_iter().zip(expect.children.iter()) {
    assert_scope_tree(bound, child, expect_child, out);
  }
}

#[derive(Default)]
struct VarAnalysis {
  declared: FxHashSet<SymbolId>,
  foreign: FxHashSet<SymbolId>,
  unknown: FxHashSet<String>,
  use_before_decl: FxHashMap<SymbolId, TextRange>,
}

fn lifted_scope(bound: &BoundFile, scope: ScopeId) -> ScopeId {
  let data = &bound.scopes[scope.0 as usize];
  match data.kind {
    ScopeKind::Block | ScopeKind::Catch => {
      if let Some(parent) = data.parent {
        let parent_kind = bound.scopes[parent.0 as usize].kind;
        if matches!(parent_kind, ScopeKind::Global | ScopeKind::Module) {
          return parent;
        }
        return lifted_scope(bound, parent);
      }
      scope
    }
    _ => scope,
  }
}

fn analyze(bound: &BoundFile, hir: &HirFile, bodies: &BodyStore) -> VarAnalysis {
  let mut out = VarAnalysis::default();
  let def_to_symbol: FxHashMap<_, _> = bound
    .symbols
    .iter()
    .enumerate()
    .flat_map(|(idx, sym)| sym.decls.iter().map(move |d| (*d, SymbolId(idx as u32))))
    .collect();
  let uses: FxHashMap<ExprId, SymbolId> = bound.uses.iter().copied().collect();

  fn walk_stmt(
    stmt: &Stmt,
    bound: &BoundFile,
    hir: &HirFile,
    bodies: &BodyStore,
    def_to_symbol: &FxHashMap<hir_js::DefId, SymbolId>,
    uses: &FxHashMap<ExprId, SymbolId>,
    out: &mut VarAnalysis,
  ) {
    match &stmt.kind {
      StmtKind::Block(stmts) => {
        for stmt in stmts {
          walk_stmt(stmt, bound, hir, bodies, def_to_symbol, uses, out);
        }
      }
      StmtKind::Var(var_decl) => {
        for binding in &var_decl.decls {
          if let Some(sym) = def_to_symbol.get(&binding.id) {
            out.declared.insert(*sym);
          }
        }
      }
      StmtKind::Function(func_decl) => {
        if let Some(sym) = def_to_symbol.get(&func_decl.id) {
          out.declared.insert(*sym);
        }
        for param in &func_decl.params {
          if let Some(sym) = def_to_symbol.get(&param.id) {
            out.declared.insert(*sym);
          }
        }
        let body = bodies.body(func_decl.body);
        for stmt in &body.statements {
          walk_stmt(stmt, bound, hir, bodies, def_to_symbol, uses, out);
        }
      }
      StmtKind::Class(class_decl) => {
        if let Some(sym) = def_to_symbol.get(&class_decl.id) {
          out.declared.insert(*sym);
        }
        let body = bodies.body(class_decl.body);
        for stmt in &body.statements {
          walk_stmt(stmt, bound, hir, bodies, def_to_symbol, uses, out);
        }
      }
      StmtKind::Expr(expr) => walk_expr(*expr, bound, hir, bodies, def_to_symbol, uses, out),
      StmtKind::Import(import_decl) => {
        for binding in &import_decl.bindings {
          if let Some(sym) = def_to_symbol.get(&binding.id) {
            out.declared.insert(*sym);
          }
        }
      }
      StmtKind::Catch(catch) => {
        if let Some(binding) = &catch.param {
          if let Some(sym) = def_to_symbol.get(&binding.id) {
            out.declared.insert(*sym);
          }
        }
        for stmt in &catch.body {
          walk_stmt(stmt, bound, hir, bodies, def_to_symbol, uses, out);
        }
      }
    }
  }

  fn walk_expr(
    expr: ExprId,
    bound: &BoundFile,
    _hir: &HirFile,
    bodies: &BodyStore,
    def_to_symbol: &FxHashMap<hir_js::DefId, SymbolId>,
    uses: &FxHashMap<ExprId, SymbolId>,
    out: &mut VarAnalysis,
  ) {
    let expr_data = bodies.expr(expr);
    match &expr_data.kind {
      ExprKind::Name(name) => {
        let resolved = uses.get(&expr).copied().or_else(|| {
          let scope = *bound.expr_scopes.get(&expr)?;
          let name_id = bound.names.id(name)?;
          resolve_in_scope(bound, scope, name_id)
        });

        if let Some(sym) = resolved {
          let usage_scope = bound.expr_scopes[&expr];
          let usage_lift = lifted_scope(bound, usage_scope);
          let decl_lift = lifted_scope(bound, bound.symbols[sym.0 as usize].scope);
          if usage_lift != decl_lift {
            out.foreign.insert(sym);
          } else if !out.declared.contains(&sym) {
            out.use_before_decl.insert(sym, expr_data.range);
          }
        } else {
          out.unknown.insert(name.clone());
        }
      }
      ExprKind::Function(func_expr) => {
        if let Some(binding) = &func_expr.name {
          if let Some(sym) = def_to_symbol.get(&binding.id) {
            out.declared.insert(*sym);
          }
        }
        for param in &func_expr.params {
          if let Some(sym) = def_to_symbol.get(&param.id) {
            out.declared.insert(*sym);
          }
        }
        let body = bodies.body(func_expr.body);
        for stmt in &body.statements {
          walk_stmt(stmt, bound, _hir, bodies, def_to_symbol, uses, out);
        }
      }
      ExprKind::Class(class_expr) => {
        if let Some(binding) = &class_expr.name {
          if let Some(sym) = def_to_symbol.get(&binding.id) {
            out.declared.insert(*sym);
          }
        }
        let body = bodies.body(class_expr.body);
        for stmt in &body.statements {
          walk_stmt(stmt, bound, _hir, bodies, def_to_symbol, uses, out);
        }
      }
      ExprKind::Call { callee, args } => {
        walk_expr(*callee, bound, _hir, bodies, def_to_symbol, uses, out);
        for arg in args {
          walk_expr(*arg, bound, _hir, bodies, def_to_symbol, uses, out);
        }
      }
      ExprKind::Block(stmts) => {
        for stmt in stmts {
          walk_stmt(stmt, bound, _hir, bodies, def_to_symbol, uses, out);
        }
      }
    }
  }

  let root_body = bodies.body(hir.root_body);
  for stmt in &root_body.statements {
    walk_stmt(stmt, bound, hir, bodies, &def_to_symbol, &uses, &mut out);
  }

  out
}

fn build_var_analysis_fixture(builder: &mut HirBuilder) -> BodyId {
  let inner_inner_block = {
    let stmt_e = builder.var_stmt(VarDeclKind::Let, &["e"]);
    let expr_z = builder.expr_stmt("z");
    let expr_w = builder.expr_stmt("w");
    let expr_c = builder.expr_stmt("c");
    let expr_b = builder.expr_stmt("b");
    let expr_a = builder.expr_stmt("a");
    builder.block(vec![stmt_e, expr_z, expr_w, expr_c, expr_b, expr_a])
  };

  let block_with_d = {
    let stmt_d = builder.var_stmt(VarDeclKind::Let, &["d"]);
    let expr_b = builder.expr_stmt("b");
    let expr_w = builder.expr_stmt("w");
    builder.block(vec![stmt_d, expr_b, expr_w, inner_inner_block])
  };

  let innermost_body = vec![
    builder.var_stmt(VarDeclKind::Let, &["b"]),
    builder.expr_stmt("z"),
    builder.expr_stmt("y"),
    builder.expr_stmt("x"),
    builder.expr_stmt("a"),
    block_with_d,
  ];
  let innermost_expr = builder.function_expr(true, None, vec![], innermost_body);

  let middle_body = vec![
    builder.var_stmt(VarDeclKind::Let, &["c"]),
    builder.expr_stmt("y"),
    builder.expr_stmt("b"),
    builder.expr_stmt("c"),
    Stmt {
      range: builder.bodies.expr(innermost_expr).range,
      kind: StmtKind::Expr(innermost_expr),
    },
  ];
  let middle_expr = builder.function_expr(true, None, vec![], middle_body);

  let outer_body = vec![
    builder.var_stmt(VarDeclKind::Let, &["a", "b"]),
    builder.expr_stmt("z"),
    Stmt {
      range: builder.bodies.expr(middle_expr).range,
      kind: StmtKind::Expr(middle_expr),
    },
  ];
  let outer_expr = builder.function_expr(true, None, vec![], outer_body);

  let root_body = vec![Stmt {
    range: builder.bodies.expr(outer_expr).range,
    kind: StmtKind::Expr(outer_expr),
  }];

  builder.bodies.alloc_body(Body::new(root_body))
}

fn build_global_fixture(builder: &mut HirBuilder) -> BodyId {
  let inner_block = {
    let expr_a = builder.expr_stmt("a");
    let expr_b = builder.expr_stmt("b");
    let expr_global = builder.expr_stmt("globalVar");
    let stmt_bd = builder.var_stmt(VarDeclKind::Let, &["b", "d"]);
    let expr_d = builder.expr_stmt("d");
    builder.block(vec![expr_a, expr_b, expr_global, stmt_bd, expr_d])
  };

  let middle_block = {
    let expr_a = builder.expr_stmt("a");
    let expr_b = builder.expr_stmt("b");
    let expr_c = builder.expr_stmt("c");
    let expr_global = builder.expr_stmt("globalVar");
    let stmt_bc = builder.var_stmt(VarDeclKind::Let, &["b", "c"]);
    builder.block(vec![
      expr_a,
      expr_b,
      expr_c,
      expr_global,
      stmt_bc,
      inner_block,
    ])
  };

  let outer_block = {
    let expr_a = builder.expr_stmt("a");
    let expr_b = builder.expr_stmt("b");
    let expr_z = builder.expr_stmt("z");
    let stmt_a = builder.var_stmt(VarDeclKind::Let, &["a"]);
    builder.block(vec![expr_a, expr_b, expr_z, stmt_a, middle_block])
  };

  let root_body = vec![
    builder.var_stmt(VarDeclKind::Let, &["globalVar"]),
    builder.expr_stmt("anotherGlobalVar"),
    builder.expr_stmt("z"),
    outer_block,
  ];
  builder.bodies.alloc_body(Body::new(root_body))
}

#[test]
fn scope_tree_and_var_analysis_match_symbol_js() {
  let mut builder = HirBuilder::new();
  let root_body = build_var_analysis_fixture(&mut builder);
  let hir = HirFile::new(
    FileId(0),
    TopLevelMode::Global,
    root_body,
    builder.bodies.expr_ranges(),
  );

  let (bound, diags) = bind_js(FileId(0), &hir, &builder.bodies);
  assert!(diags.is_empty());

  let mut syms = FxHashMap::default();
  assert_scope_tree(
    &bound,
    bound.root_scope,
    &ExpectScope {
      kind: ScopeKind::Global,
      symbols: vec![],
      children: vec![ExpectScope {
        kind: ScopeKind::ArrowFunction,
        symbols: vec![("a", "a"), ("b", "b1")],
        children: vec![ExpectScope {
          kind: ScopeKind::ArrowFunction,
          symbols: vec![("c", "c")],
          children: vec![ExpectScope {
            kind: ScopeKind::ArrowFunction,
            symbols: vec![("b", "b2")],
            children: vec![ExpectScope {
              kind: ScopeKind::Block,
              symbols: vec![("d", "d")],
              children: vec![ExpectScope {
                kind: ScopeKind::Block,
                symbols: vec![("e", "e")],
                children: vec![],
              }],
            }],
          }],
        }],
      }],
    },
    &mut syms,
  );

  let analysis = analyze(&bound, &hir, &builder.bodies);
  let declared: FxHashSet<_> = syms
    .iter()
    .filter(|(k, _)| ["a", "b1", "b2", "c", "d", "e"].contains(k))
    .map(|(_, v)| *v)
    .collect();
  assert_eq!(analysis.declared, declared);

  let foreign: FxHashSet<_> = ["a", "b1", "c"].iter().map(|k| syms[k]).collect();
  assert_eq!(analysis.foreign, foreign);
  assert!(analysis.use_before_decl.is_empty());

  let expected_unknown: FxHashSet<_> = ["w", "y", "x", "z"].iter().map(|s| s.to_string()).collect();
  assert_eq!(analysis.unknown, expected_unknown);
}

#[test]
fn global_scopes_and_use_before_decl() {
  let mut builder = HirBuilder::new();
  let root_body = build_global_fixture(&mut builder);
  let hir = HirFile::new(
    FileId(1),
    TopLevelMode::Global,
    root_body,
    builder.bodies.expr_ranges(),
  );

  let (bound, diags) = bind_js(FileId(1), &hir, &builder.bodies);
  assert!(diags.is_empty());

  let analysis = analyze(&bound, &hir, &builder.bodies);

  let mut syms = FxHashMap::default();
  assert_scope_tree(
    &bound,
    bound.root_scope,
    &ExpectScope {
      kind: ScopeKind::Global,
      symbols: vec![("globalVar", "global")],
      children: vec![ExpectScope {
        kind: ScopeKind::Block,
        symbols: vec![("a", "a")],
        children: vec![ExpectScope {
          kind: ScopeKind::Block,
          symbols: vec![("b", "b1"), ("c", "c")],
          children: vec![ExpectScope {
            kind: ScopeKind::Block,
            symbols: vec![("b", "b2"), ("d", "d")],
            children: vec![],
          }],
        }],
      }],
    },
    &mut syms,
  );

  let label_map: FxHashMap<SymbolId, &str> = syms.iter().map(|(k, v)| (*v, *k)).collect();

  let mut b_resolutions = Vec::new();
  for (expr_id, scope_id) in &bound.expr_scopes {
    let expr = builder.bodies.expr(*expr_id);
    if let ExprKind::Name(name) = &expr.kind {
      if name == "b" {
        let resolved = resolve_in_scope(&bound, *scope_id, bound.names.id(name).unwrap());
        b_resolutions.push((expr.range.start, resolved.map(|s| label_map[&s])));
      }
    }
  }
  b_resolutions.sort_by_key(|(start, _)| *start);
  assert_eq!(b_resolutions.len(), 3);
  let b_resolution_labels: FxHashSet<_> = b_resolutions.iter().map(|(_, l)| *l).collect();
  let expected_b_resolution_labels: FxHashSet<_> =
    [None, Some("b1"), Some("b2")].into_iter().collect();
  assert_eq!(b_resolution_labels, expected_b_resolution_labels);

  let uses_for_b: FxHashSet<&str> = bound
    .uses
    .iter()
    .filter_map(|(expr, sym)| {
      let expr_data = builder.bodies.expr(*expr);
      if let ExprKind::Name(name) = &expr_data.kind {
        if name == "b" {
          return Some(label_map[sym]);
        }
      }
      None
    })
    .collect();
  assert!(uses_for_b.contains("b2"));

  let declared: FxHashSet<_> = ["a", "b1", "b2", "c", "d", "global"]
    .iter()
    .map(|k| syms[k])
    .collect();
  assert_eq!(analysis.declared, declared);
  let actual_labels: FxHashSet<&str> = analysis
    .use_before_decl
    .keys()
    .map(|id| label_map[id])
    .collect();
  let expected_labels: FxHashSet<&str> = ["a", "b1", "b2", "c"].iter().copied().collect();
  assert_eq!(actual_labels, expected_labels);

  let expected_unknown: FxHashSet<_> = ["anotherGlobalVar", "b", "z"]
    .iter()
    .map(|s| s.to_string())
    .collect();
  assert_eq!(analysis.unknown, expected_unknown);
  let foreign_labels: FxHashSet<&str> = analysis.foreign.iter().map(|id| label_map[id]).collect();
  assert!(foreign_labels.is_empty(), "{:?}", foreign_labels);
}

#[test]
fn symbol_at_offset_tracks_uses() {
  let mut builder = HirBuilder::new();
  let name_binding = builder.binding("a");
  let decl_stmt = Stmt {
    range: builder.range(),
    kind: StmtKind::Var(VarDecl {
      decls: vec![name_binding.clone()],
      kind: VarDeclKind::Let,
      range: builder.range(),
    }),
  };
  let name_expr = builder.name_expr("a");
  let use_stmt = Stmt {
    range: builder.bodies.expr(name_expr).range,
    kind: StmtKind::Expr(name_expr),
  };
  let body_id = builder
    .bodies
    .alloc_body(Body::new(vec![decl_stmt, use_stmt]));
  let hir = HirFile::new(
    FileId(2),
    TopLevelMode::Module,
    body_id,
    builder.bodies.expr_ranges(),
  );

  let (bound, _) = bind_js(FileId(2), &hir, &builder.bodies);
  let sym_name = bound.symbols[0].name;
  assert_eq!(
    symbol_at_offset(&bound, &hir, builder.bodies.expr(name_expr).range.start),
    Some(SymbolId(0))
  );
  assert!(symbol_at_offset(&bound, &hir, 999).is_none());
  assert_eq!(
    resolve_in_scope(&bound, bound.root_scope, sym_name),
    Some(SymbolId(0))
  );
}

#[test]
fn illegal_redeclarations_emit_diagnostics() {
  let mut builder = HirBuilder::new();
  let stmt1 = builder.var_stmt(VarDeclKind::Let, &["a"]);
  let stmt2 = builder.var_stmt(VarDeclKind::Var, &["a"]);
  let body_id = builder.bodies.alloc_body(Body::new(vec![stmt1, stmt2]));
  let hir = HirFile::new(
    FileId(3),
    TopLevelMode::Module,
    body_id,
    builder.bodies.expr_ranges(),
  );

  let (_bound, diags) = bind_js(FileId(3), &hir, &builder.bodies);
  assert_eq!(diags.len(), 1);
  assert_eq!(diags[0].code, "E0001");
}

#[test]
fn let_redeclarations_error() {
  let mut builder = HirBuilder::new();
  let stmt1 = builder.var_stmt(VarDeclKind::Let, &["a"]);
  let stmt2 = builder.var_stmt(VarDeclKind::Let, &["a"]);
  let body_id = builder.bodies.alloc_body(Body::new(vec![stmt1, stmt2]));
  let hir = HirFile::new(
    FileId(5),
    TopLevelMode::Module,
    body_id,
    builder.bodies.expr_ranges(),
  );

  let (_bound, diags) = bind_js(FileId(5), &hir, &builder.bodies);
  assert_eq!(diags.len(), 1);
  assert_eq!(diags[0].code, "E0001");
}

#[test]
fn var_redeclarations_are_allowed_and_tracked() {
  let mut builder = HirBuilder::new();
  let stmt1 = builder.var_stmt(VarDeclKind::Var, &["a"]);
  let stmt2 = builder.var_stmt(VarDeclKind::Var, &["a"]);
  let use_expr = builder.name_expr("a");
  let use_stmt = Stmt {
    range: builder.bodies.expr(use_expr).range,
    kind: StmtKind::Expr(use_expr),
  };
  let body_id = builder
    .bodies
    .alloc_body(Body::new(vec![stmt1, stmt2, use_stmt]));
  let hir = HirFile::new(
    FileId(6),
    TopLevelMode::Module,
    body_id,
    builder.bodies.expr_ranges(),
  );

  let (bound, diags) = bind_js(FileId(6), &hir, &builder.bodies);
  assert!(diags.is_empty());
  assert_eq!(bound.symbols.len(), 1);
  let sym = &bound.symbols[0];
  assert_eq!(sym.decls.len(), 2);
  assert_eq!(bound.uses.len(), 1);
}

#[test]
fn binding_is_deterministic() {
  let mut builder = HirBuilder::new();
  let stmt1 = builder.var_stmt(VarDeclKind::Var, &["a"]);
  let stmt2 = builder.expr_stmt("a");
  let body_id = builder.bodies.alloc_body(Body::new(vec![stmt1, stmt2]));
  let hir = HirFile::new(
    FileId(4),
    TopLevelMode::Module,
    body_id,
    builder.bodies.expr_ranges(),
  );

  let (one, diags_one) = bind_js(FileId(4), &hir, &builder.bodies);
  let (two, diags_two) = bind_js(FileId(4), &hir, &builder.bodies);
  assert_eq!(diags_one, diags_two);
  assert_eq!(one, two);
}
