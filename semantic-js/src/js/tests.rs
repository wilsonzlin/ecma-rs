use crate::assoc::js::{declared_symbol, resolved_symbol, resolved_symbol_info, ResolvedSymbol};
use crate::js::{bind_js, declare, JsSemantics, ScopeKind, SymbolId, TopLevelMode};
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use diagnostics::Diagnostic;
use diagnostics::FileId;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::parse;
use std::fmt::Write;

#[derive(Default, VisitorMut)]
#[visitor(IdExprNode(enter), IdPatNode(enter))]
struct Collect {
  id_exprs: Vec<(String, Option<SymbolId>)>,
  id_pats: Vec<(String, Option<SymbolId>, bool)>,
}

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;

impl Collect {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    self
      .id_exprs
      .push((node.stx.name.clone(), resolved_symbol(&node.assoc)));
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let declared = declared_symbol(&node.assoc);
    self.id_pats.push((
      node.stx.name.clone(),
      resolved_symbol(&node.assoc),
      declared.is_some(),
    ));
  }
}

#[derive(Default, VisitorMut)]
#[visitor(IdExprNode(enter), IdPatNode(enter))]
struct CollectWithInfo {
  id_exprs: Vec<(String, Option<ResolvedSymbol>)>,
  id_pats: Vec<(String, Option<ResolvedSymbol>, bool)>,
}

impl CollectWithInfo {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    self
      .id_exprs
      .push((node.stx.name.clone(), resolved_symbol_info(&node.assoc)));
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let declared = declared_symbol(&node.assoc);
    self.id_pats.push((
      node.stx.name.clone(),
      resolved_symbol_info(&node.assoc),
      declared.is_some(),
    ));
  }
}

fn snapshot(sem: &JsSemantics) -> Vec<u8> {
  let mut out = String::new();
  let mut names: Vec<_> = sem
    .names
    .iter()
    .map(|(id, name)| (id.raw(), name.clone()))
    .collect();
  names.sort_by_key(|(id, _)| *id);
  writeln!(&mut out, "names {:?}", names).unwrap();
  writeln!(&mut out, "name_lookup {:?}", sem.name_lookup).unwrap();
  for (id, scope) in sem.scopes.iter() {
    writeln!(
      &mut out,
      "scope {} {:?} parent {:?}",
      id.raw(),
      scope.kind,
      scope.parent.map(|p| p.raw())
    )
    .unwrap();
    let children: Vec<_> = scope.children.iter().map(|child| child.raw()).collect();
    writeln!(&mut out, "  children {children:?}").unwrap();
    writeln!(
      &mut out,
      "  dynamic {} direct_eval {}",
      scope.is_dynamic, scope.has_direct_eval
    )
    .unwrap();
    let hoisted: Vec<_> = scope.hoisted_bindings.iter().map(|sym| sym.raw()).collect();
    writeln!(&mut out, "  hoisted_bindings {hoisted:?}").unwrap();
    let tdz: Vec<_> = scope.tdz_bindings.iter().map(|sym| sym.raw()).collect();
    writeln!(&mut out, "  tdz_bindings {tdz:?}").unwrap();
    let symbols: Vec<_> = scope
      .iter_symbols_sorted()
      .map(|(name, symbol)| (name.raw(), symbol.raw()))
      .collect();
    writeln!(&mut out, "  symbols {symbols:?}").unwrap();
  }
  for (id, symbol) in sem.symbols.iter() {
    writeln!(
      &mut out,
      "symbol {} name {} decl_scope {}",
      id.raw(),
      symbol.name.raw(),
      symbol.decl_scope.raw()
    )
    .unwrap();
  }
  out.into_bytes()
}

#[test]
fn shadowing_prefers_inner_bindings() {
  let mut ast = parse("let a = 1; { let a = 2; a; } a;").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(0));
  assert!(diagnostics.is_empty());

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  let decls: Vec<SymbolId> = collect
    .id_pats
    .iter()
    .filter_map(|(_, resolved, is_decl)| if *is_decl { *resolved } else { None })
    .collect();
  assert_eq!(decls.len(), 2);

  assert_eq!(collect.id_exprs.len(), 2);
  let inner_use = collect.id_exprs[0].1;
  let outer_use = collect.id_exprs[1].1;

  assert_eq!(inner_use, Some(decls[1]));
  assert_eq!(outer_use, Some(decls[0]));
}

#[test]
fn function_expression_name_is_local() {
  let mut ast = parse("const x = function foo() { return foo; }; foo;").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(1));
  assert!(diagnostics.is_empty());

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  let resolved: Vec<Option<SymbolId>> = collect.id_exprs.iter().map(|(_, s)| *s).collect();
  assert_eq!(resolved.len(), 2);
  assert!(resolved[0].is_some());
  assert_eq!(resolved[1], None);
}

#[test]
fn destructuring_assignment_resolves_existing_symbol() {
  let mut ast = parse("let a; ({a} = obj);").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(2));
  assert!(diagnostics.is_empty());

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  let decl_symbol = collect
    .id_pats
    .iter()
    .find(|(_, _, is_decl)| *is_decl)
    .and_then(|(_, resolved, _)| *resolved)
    .expect("declaration symbol");

  let assignment_use = collect
    .id_pats
    .iter()
    .find(|(name, _, is_decl)| name == "a" && !*is_decl)
    .and_then(|(_, resolved, _)| *resolved);

  assert_eq!(assignment_use, Some(decl_symbol));
}

#[test]
fn hoists_var_and_function_declarations() {
  let mut ast = parse(
    "function wrap() { use_before; { var use_before = 1; } fn_call(); function fn_call() {} }",
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(3));
  assert!(diagnostics.is_empty());

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);

  let var_decl = collect
    .id_pats
    .iter()
    .find(|(name, _, is_decl)| name == "use_before" && *is_decl)
    .and_then(|(_, resolved, _)| resolved.as_ref().and_then(|r| r.symbol))
    .expect("var declaration");
  let use_before = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "use_before")
    .and_then(|(_, resolved)| resolved.as_ref())
    .expect("use_before reference");

  assert_eq!(use_before.symbol, Some(var_decl));
  assert!(!use_before.in_tdz);

  let fn_call = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "fn_call")
    .and_then(|(_, resolved)| resolved.as_ref())
    .expect("fn_call reference");
  assert!(fn_call.symbol.is_some());
  assert!(!fn_call.in_tdz);
}

#[test]
fn marks_lexical_uses_in_tdz() {
  let mut ast = parse("let outer = 0; { outer; let outer = 1; outer; }").unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(4));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);

  let block_scope = *sem
    .scope(sem.top_scope())
    .children
    .iter()
    .find(|&&scope| sem.scope(scope).kind == ScopeKind::Block)
    .expect("block scope");
  let name_id = sem.name_id("outer").unwrap();
  let inner_symbol = sem.scope(block_scope).get(name_id).expect("inner symbol");

  let uses: Vec<_> = collect
    .id_exprs
    .iter()
    .filter(|(name, _)| name == "outer")
    .collect();
  assert_eq!(uses.len(), 2);
  let first = uses[0].1.as_ref().unwrap();
  let second = uses[1].1.as_ref().unwrap();

  assert_eq!(first.symbol, Some(inner_symbol));
  assert_eq!(second.symbol, Some(inner_symbol));
  assert!(first.in_tdz);
  assert!(!second.in_tdz);
}

#[test]
fn top_level_tdz_and_hoisting_are_tracked() {
  let mut ast = parse(
    r#"
    var hoisted = 0;
    function hoisted_fn() { return hoisted; }
    console.log(late);
    let late = 1;
  "#,
  )
  .unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(30));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");

  let top_scope = sem.top_scope();
  let hoisted_names: Vec<_> = sem
    .scope(top_scope)
    .hoisted_bindings
    .iter()
    .map(|sym| sem.name(sem.symbol(*sym).name).to_string())
    .collect();
  assert!(hoisted_names.contains(&"hoisted".to_string()));
  assert!(hoisted_names.contains(&"hoisted_fn".to_string()));
  assert!(!hoisted_names.contains(&"late".to_string()));

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);

  let late_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "late")
    .and_then(|(_, info)| info.as_ref())
    .expect("late should resolve");
  assert!(late_use.in_tdz);
}

#[test]
fn class_name_is_visible_inside_static_block() {
  let mut ast = parse("class Foo{static{Foo.x++}}").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(50));
  assert!(diagnostics.is_empty(), "unexpected diagnostics: {diagnostics:?}");
}

#[test]
fn class_name_in_extends_is_in_tdz() {
  let source = "class Foo extends Foo{}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(51));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "Foo");
}

#[test]
fn class_name_in_computed_key_is_in_tdz() {
  let source = "class Foo{['x'](){}[Foo](){}}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(52));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "Foo");
}

#[test]
fn module_top_level_function_redeclaration_is_reported() {
  let source = "function f() {} function f() {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(55));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0001");
  assert_eq!(slice_range(source, &diagnostics[0]), "f");
}

#[test]
fn module_top_level_var_function_conflict_is_reported() {
  let source = "var f = 1; function f() {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(56));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0002");
  assert_eq!(slice_range(source, &diagnostics[0]), "f");
}

#[test]
fn block_var_lexical_conflict_is_reported() {
  let source = "function wrap(){ { let a = 1; var a = 2; } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(57));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0002");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn nested_block_var_lexical_conflict_is_reported() {
  let source = "function wrap(){ { let a = 1; { var a = 2; } } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(58));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0002");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn block_function_is_lexical_in_modules() {
  use crate::assoc::js::resolved_symbol;
  use parse_js::ast::expr::pat::ClassOrFuncName;
  use parse_js::loc::Loc;

  type ClassOrFuncNameNode = Node<ClassOrFuncName>;

  #[derive(Default, VisitorMut)]
  #[visitor(IdExprNode(enter), ClassOrFuncNameNode(enter))]
  struct FooCollector {
    decl: Option<SymbolId>,
    uses: Vec<(Loc, Option<SymbolId>)>,
  }

  impl FooCollector {
    fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
      if node.stx.name == "foo" {
        self.decl = declared_symbol(&node.assoc);
      }
    }

    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == "foo" {
        self.uses.push((node.loc, resolved_symbol(&node.assoc)));
      }
    }
  }

  let source = "function outer(){ if(true){ function foo(){} foo; } foo; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(59));
  assert!(diagnostics.is_empty(), "unexpected diagnostics: {diagnostics:?}");

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(decl));
  assert_eq!(collector.uses[1].1, None);
}

#[test]
fn hoisted_var_uses_are_not_in_tdz() {
  let mut ast = parse("console.log(x); var x = 1;").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(31));
  assert!(diagnostics.is_empty());

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);
  let var_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "x")
    .and_then(|(_, info)| info.as_ref())
    .expect("use of x should resolve");
  assert!(!var_use.in_tdz);
}

#[test]
fn public_resolve_handles_late_declarations() {
  let mut ast = parse("later; const later = 1;").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module, FileId(20));

  let resolved = sem.resolve_name_in_scope(sem.top_scope(), "later");
  let later = sem.name_id("later").expect("name interned");
  assert_eq!(resolved.map(|id| sem.symbol(id).name), Some(later));
}

#[test]
fn public_resolve_traverses_parents() {
  let mut ast = parse("const outer = 1; { outer; }").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module, FileId(21));

  let top_scope = sem.top_scope();
  let block_scope = sem.scope(top_scope).children[0];

  let resolved_in_block = sem.resolve_name_in_scope(block_scope, "outer");
  let resolved_at_top = sem.resolve_name_in_scope(top_scope, "outer");

  assert!(resolved_at_top.is_some());
  assert_eq!(resolved_in_block, resolved_at_top);
}

#[test]
fn public_resolve_unknown_name_returns_none() {
  let mut ast = parse("const known = 1;").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module, FileId(22));

  assert_eq!(sem.resolve_name_in_scope(sem.top_scope(), "missing"), None);
}

#[test]
fn scope_symbols_iteration_is_stable() {
  let mut ast = parse("let b = 1; let a = 2;").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module, FileId(23));

  let first = sem
    .scope_symbols(sem.top_scope())
    .map(|(name, _)| sem.name(name).to_string())
    .collect::<Vec<_>>();
  let second = sem
    .scope_symbols(sem.top_scope())
    .map(|(name, _)| sem.name(name).to_string())
    .collect::<Vec<_>>();

  assert_eq!(first, vec!["b", "a"]);
  assert_eq!(first, second);
}

#[test]
fn semantics_are_deterministic_between_runs() {
  let source = r#"
    function outer(arg) {
      const first = arg;
      {
        let block = first;
        function inner() {
          return arg + block;
        }
        const arrow = () => inner();
      }
      return { first };
    }
  "#;

  let first = {
    let mut ast = parse(source).unwrap();
    let sem = declare(&mut ast, TopLevelMode::Module, FileId(24));
    snapshot(&sem)
  };
  let second = {
    let mut ast = parse(source).unwrap();
    let sem = declare(&mut ast, TopLevelMode::Module, FileId(24));
    snapshot(&sem)
  };

  assert_eq!(first, second);
}

#[test]
fn marks_dynamic_scopes_for_with_and_eval() {
  let mut ast = parse(
    r#"
    with (obj) { shadow; }
    function wrap() { eval("shadow"); }
    function shadowed(eval) { eval("shadow"); }
  "#,
  )
  .unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module, FileId(26));

  let top_scope = sem.top_scope();
  assert!(sem.scope(top_scope).is_dynamic);

  let dynamic_blocks: Vec<_> = sem
    .scope(top_scope)
    .children
    .iter()
    .copied()
    .filter(|scope| sem.scope(*scope).kind == ScopeKind::Block && sem.scope(*scope).is_dynamic)
    .collect();
  assert!(!dynamic_blocks.is_empty());

  let function_scopes: Vec<_> = sem
    .scope(top_scope)
    .children
    .iter()
    .copied()
    .filter(|scope| sem.scope(*scope).kind == ScopeKind::NonArrowFunction)
    .collect();
  assert_eq!(function_scopes.len(), 2);

  let eval_scope = function_scopes
    .iter()
    .find(|&&scope| sem.scope(scope).has_direct_eval)
    .copied()
    .expect("direct eval scope");
  assert!(sem.scope(eval_scope).is_dynamic);

  let shadowed_eval_scope = function_scopes
    .iter()
    .find(|&&scope| scope != eval_scope)
    .copied()
    .unwrap();
  assert!(!sem.scope(shadowed_eval_scope).is_dynamic);
}

fn slice_range<'a>(source: &'a str, diagnostic: &Diagnostic) -> &'a str {
  let range = diagnostic.primary.range;
  &source[range.start as usize..range.end as usize]
}

#[test]
fn reports_lexical_redeclaration_errors() {
  let source = "let a = 1; let a = 2;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(40));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0001");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn reports_lexical_var_conflicts() {
  let source = "var a = 1; let a = 2;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(41));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0002");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn reports_lexical_parameter_conflicts() {
  let source = "function f(a) { let a = 1; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(42));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0002");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn reports_tdz_errors_and_sorts_deterministically() {
  let source = "a; let a = 1; let a = 2;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(43));
  assert_eq!(diagnostics.len(), 2);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(diagnostics[1].code.as_str(), "BIND0001");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
  assert_eq!(slice_range(source, &diagnostics[1]), "a");
  assert!(diagnostics[0].primary.range.start < diagnostics[1].primary.range.start);
}

#[test]
fn class_name_is_available_inside_class_body() {
  let mut ast = parse("class C { static x = C; }").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(44));
  assert!(
    diagnostics.is_empty(),
    "expected class body to be able to reference class name, got {diagnostics:?}"
  );
}

#[test]
fn class_name_is_in_tdz_in_extends_clause() {
  let source = "class C extends C {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(45));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "C");
}

#[test]
fn class_expression_name_is_available_inside_class_body() {
  let mut ast = parse("const x = class C { static y = C; };").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(46));
  assert!(
    diagnostics.is_empty(),
    "expected class expression body to be able to reference class name, got {diagnostics:?}"
  );
}

#[test]
fn class_expression_name_is_in_tdz_in_extends_clause() {
  let source = "const x = class C extends C {};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(47));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "C");
}

#[test]
fn parameter_default_initializer_does_not_resolve_to_body_lexicals() {
  let source = "function f(a = b) { let b = 1; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(48));
  assert!(
    diagnostics.is_empty(),
    "expected default parameter initializer to ignore body lexicals, got {diagnostics:?}"
  );

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);
  let b_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "b")
    .and_then(|(_, info)| info.as_ref())
    .expect("b use");
  assert_eq!(b_use.symbol, None);
  assert!(!b_use.in_tdz);
}

#[test]
fn parameter_default_initializer_prefers_outer_binding() {
  let source = "let b = 2; function f(a = b) { let b = 1; }";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(49));
  assert!(
    diagnostics.is_empty(),
    "expected default parameter initializer to resolve to outer binding, got {diagnostics:?}"
  );

  let outer_b = sem
    .resolve_name_in_scope(sem.top_scope(), "b")
    .expect("outer binding");

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);
  let b_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "b")
    .and_then(|(_, info)| info.as_ref())
    .expect("b use");
  assert_eq!(b_use.symbol, Some(outer_b));
  assert!(!b_use.in_tdz);
}

#[test]
fn destructuring_default_initializer_can_reference_prior_binding() {
  let source = "let {a, b = a} = obj;";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(50));
  assert!(
    diagnostics.is_empty(),
    "expected destructuring defaults to allow referencing earlier bindings, got {diagnostics:?}"
  );

  let a_symbol = sem
    .resolve_name_in_scope(sem.top_scope(), "a")
    .expect("binding a");

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);

  let a_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "a")
    .and_then(|(_, info)| info.as_ref())
    .expect("a use in default initializer");
  assert_eq!(a_use.symbol, Some(a_symbol));
  assert!(!a_use.in_tdz);
}

#[test]
fn destructuring_default_initializer_prior_binding_array_pattern() {
  let source = "let [a, b = a] = arr;";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(51));
  assert!(
    diagnostics.is_empty(),
    "expected array destructuring defaults to allow referencing earlier bindings, got {diagnostics:?}"
  );

  let a_symbol = sem
    .resolve_name_in_scope(sem.top_scope(), "a")
    .expect("binding a");

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);

  let a_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "a")
    .and_then(|(_, info)| info.as_ref())
    .expect("a use in default initializer");
  assert_eq!(a_use.symbol, Some(a_symbol));
  assert!(!a_use.in_tdz);
}

#[test]
fn destructuring_default_initializer_later_binding_is_in_tdz() {
  let source = "let {a = b, b} = obj;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(52));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "b");
}

#[test]
fn closure_uses_of_outer_bindings_are_not_reported_as_tdz() {
  let source = "const f = () => f; f();";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(53));
  assert!(
    diagnostics.is_empty(),
    "expected recursive closure reference to be allowed, got {diagnostics:?}"
  );
}

#[test]
fn class_method_body_does_not_trigger_outer_tdz_diagnostics() {
  let source = "class C { m() { return x; } } let x = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(54));
  assert!(
    diagnostics.is_empty(),
    "expected method bodies to be deferred and not report outer TDZ, got {diagnostics:?}"
  );
}
