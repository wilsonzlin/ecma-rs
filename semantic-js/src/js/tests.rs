use crate::assoc::js::{declared_symbol, resolved_symbol, resolved_symbol_info, ResolvedSymbol};
use crate::js::{
  bind_js, bind_js_for_runtime, declare, JsSemantics, ScopeKind, SymbolId, TopLevelMode,
};
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use diagnostics::Diagnostic;
use diagnostics::FileId;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::{parse, parse_with_options, Dialect, ParseOptions, SourceType};
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
  let annex_pairs: Vec<_> = sem
    .annex_b_function_decls
    .iter()
    .map(|(block, var_sym)| (block.raw(), var_sym.raw()))
    .collect();
  writeln!(&mut out, "annex_b_function_decls {annex_pairs:?}").unwrap();
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
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn static_block_lexicals_do_not_leak_to_sibling_members() {
  let mut ast = parse("class C { static { let a = 1; } static m(){ a; } }").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(78));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  assert_eq!(collect.id_exprs, vec![("a".to_string(), None)]);
}

#[test]
fn static_block_vars_do_not_leak_to_sibling_members() {
  let mut ast = parse("class C { static { var a = 1; } static m(){ a; } }").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(79));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  assert_eq!(collect.id_exprs, vec![("a".to_string(), None)]);
}

#[test]
fn static_blocks_have_independent_scopes() {
  let mut ast = parse("class C { static { let a = 1; } static { let a = 2; } }").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(80));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  let decls: Vec<_> = collect
    .id_pats
    .iter()
    .filter(|(name, _, is_decl)| name == "a" && *is_decl)
    .filter_map(|(_, sym, _)| *sym)
    .collect();
  assert_eq!(decls.len(), 2);
  assert_ne!(decls[0], decls[1]);
}

#[test]
fn static_block_tdz_is_reported() {
  let source = "class C { static { a; let a = 1; } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(81));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
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
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(decl));
  assert_eq!(collector.uses[1].1, None);
}

#[test]
fn strict_script_block_function_is_block_scoped() {
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

  let source = "function outer(){ \"use strict\"; if(true){ function foo(){} foo; } foo; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(82));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(decl));
  assert_eq!(collector.uses[1].1, None);
}

#[test]
fn parenthesized_use_strict_is_not_a_directive() {
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

  let source = r#"function outer(){ ("use strict"); if(true){ function foo(){} } foo; }"#;
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(90));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 1);
  let outside = collector.uses[0]
    .1
    .expect("expected hoisted foo binding to resolve");
  assert_ne!(outside, decl);
  assert_eq!(
    sem.annex_b_function_decls.get(&decl).copied(),
    Some(outside)
  );
}

#[test]
fn catch_parameter_allows_var_redecl() {
  let source = "function f(){ try{}catch(e){ var e; } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(60));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn catch_parameter_conflicts_with_lexical_decl() {
  let source = "function f(){ try{}catch(e){ let e; } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(61));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0001");
  assert_eq!(slice_range(source, &diagnostics[0]), "e");
}

#[test]
fn catch_destructuring_default_initializer_can_reference_prior_binding() {
  let source = "function f(){ try{throw {}}catch({a, b=a}){ b; } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(94));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn catch_destructuring_default_initializer_later_binding_is_in_tdz() {
  let source = "function f(){ try{throw {}}catch({a=b, b}){} }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(95));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "b");
}

#[test]
fn catch_parameter_does_not_suppress_script_block_function_hoisting() {
  use crate::assoc::js::resolved_symbol;
  use parse_js::ast::expr::pat::ClassOrFuncName;
  use parse_js::loc::Loc;

  type ClassOrFuncNameNode = Node<ClassOrFuncName>;

  #[derive(Default, VisitorMut)]
  #[visitor(IdExprNode(enter), IdPatNode(enter), ClassOrFuncNameNode(enter))]
  struct XCollector {
    func_decl: Option<SymbolId>,
    catch_decl: Option<SymbolId>,
    uses: Vec<(Loc, Option<SymbolId>)>,
  }

  impl XCollector {
    fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
      if node.stx.name == "x" {
        self.func_decl = declared_symbol(&node.assoc);
      }
    }

    fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
      if node.stx.name == "x" {
        if let Some(sym) = declared_symbol(&node.assoc) {
          self.catch_decl = Some(sym);
        }
      }
    }

    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == "x" {
        self.uses.push((node.loc, resolved_symbol(&node.assoc)));
      }
    }
  }

  let source = r#"
    function outer(){
      try { throw 1; } catch (x) {
        x;
        { function x(){} x; }
        x;
      }
      x;
    }
  "#;
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(93));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = XCollector::default();
  ast.drive_mut(&mut collector);
  let func_decl = collector
    .func_decl
    .expect("expected function x declaration");
  let catch_decl = collector.catch_decl.expect("expected catch parameter x");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 4);
  assert_eq!(collector.uses[0].1, Some(catch_decl));
  assert_eq!(collector.uses[1].1, Some(func_decl));
  assert_eq!(collector.uses[2].1, Some(catch_decl));

  let outside = collector.uses[3]
    .1
    .expect("expected hoisted var binding for x");
  assert_ne!(outside, func_decl);
  assert_ne!(outside, catch_decl);
  assert_eq!(
    sem.annex_b_function_decls.get(&func_decl).copied(),
    Some(outside)
  );
}

#[test]
fn script_block_function_is_block_scoped_when_shadowed_by_let() {
  use crate::assoc::js::resolved_symbol;
  use parse_js::ast::expr::pat::ClassOrFuncName;
  use parse_js::loc::Loc;

  type ClassOrFuncNameNode = Node<ClassOrFuncName>;

  #[derive(Default, VisitorMut)]
  #[visitor(IdExprNode(enter), IdPatNode(enter), ClassOrFuncNameNode(enter))]
  struct FooCollector {
    func_decl: Option<SymbolId>,
    let_decl: Option<SymbolId>,
    uses: Vec<(Loc, Option<SymbolId>)>,
  }

  impl FooCollector {
    fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
      if node.stx.name == "foo" {
        self.func_decl = declared_symbol(&node.assoc);
      }
    }

    fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
      if node.stx.name == "foo" {
        if let Some(sym) = declared_symbol(&node.assoc) {
          self.let_decl = Some(sym);
        }
      }
    }

    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == "foo" {
        self.uses.push((node.loc, resolved_symbol(&node.assoc)));
      }
    }
  }

  let source = "function outer(){ if(true){ function foo(){} foo; } let foo = 1; foo; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(62));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let func_decl = collector
    .func_decl
    .expect("expected function foo declaration");
  let let_decl = collector.let_decl.expect("expected let foo declaration");
  assert_ne!(func_decl, let_decl);

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(func_decl));
  assert_eq!(collector.uses[1].1, Some(let_decl));
}

#[test]
fn script_block_function_hoists_when_not_shadowed() {
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
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(63));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(decl));

  let outside = collector.uses[1].1.expect("expected hoisted foo binding");
  assert_ne!(outside, decl);
  assert_eq!(
    sem.annex_b_function_decls.get(&decl).copied(),
    Some(outside)
  );
}

#[test]
fn script_block_function_does_not_hoist_over_parameter() {
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

  let source = "function outer(foo){ if(true){ function foo(){} foo; } foo; }";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(64));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(decl));
  let outside = collector.uses[1]
    .1
    .expect("expected parameter foo binding to resolve");
  assert_ne!(outside, decl);
  assert!(!sem.symbol(outside).flags.hoisted);
}

#[test]
fn script_block_function_var_conflict_is_reported() {
  let source = "function outer(){ if(true){ function foo(){} var foo; } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(65));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0002");
  assert_eq!(slice_range(source, &diagnostics[0]), "foo");
}

#[test]
fn script_block_function_var_binding_exists_even_if_block_never_executes() {
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

  let source = "function outer(){ if(false){ function foo(){} } foo; }";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(91));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = FooCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected foo declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 1);
  let outside = collector.uses[0]
    .1
    .expect("expected hoisted foo binding to resolve");
  assert_ne!(outside, decl);
  assert_eq!(
    sem.annex_b_function_decls.get(&decl).copied(),
    Some(outside)
  );
}

#[test]
fn for_of_let_suppresses_script_block_function_hoisting() {
  use crate::assoc::js::resolved_symbol;
  use parse_js::ast::expr::pat::ClassOrFuncName;
  use parse_js::loc::Loc;

  type ClassOrFuncNameNode = Node<ClassOrFuncName>;

  #[derive(Default, VisitorMut)]
  #[visitor(IdExprNode(enter), ClassOrFuncNameNode(enter))]
  struct XCollector {
    decl: Option<SymbolId>,
    uses: Vec<(Loc, Option<SymbolId>)>,
  }

  impl XCollector {
    fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
      if node.stx.name == "x" {
        self.decl = declared_symbol(&node.assoc);
      }
    }

    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == "x" {
        self.uses.push((node.loc, resolved_symbol(&node.assoc)));
      }
    }
  }

  let source = "function outer(){ for (let x of y) { function x(){} x; } x; }";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(92));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collector = XCollector::default();
  ast.drive_mut(&mut collector);
  let decl = collector.decl.expect("expected x declaration symbol");

  collector.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(collector.uses.len(), 2);
  assert_eq!(collector.uses[0].1, Some(decl));
  assert_eq!(collector.uses[1].1, None);
  assert!(!sem.annex_b_function_decls.contains_key(&decl));
}

#[test]
fn switch_case_lexicals_are_not_visible_outside_switch() {
  let mut ast = parse("switch(0){case 0: let a = 1; break;} a;").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(70));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  assert_eq!(collect.id_exprs, vec![("a".to_string(), None)]);
  let use_after_switch = collect.id_exprs[0].1;

  let inner_decl = collect
    .id_pats
    .iter()
    .find(|(name, _, is_decl)| name == "a" && *is_decl)
    .and_then(|(_, sym, _)| *sym)
    .expect("expected inner declaration symbol");
  assert_ne!(use_after_switch, Some(inner_decl));
}

#[test]
fn switch_case_lexicals_do_not_conflict_with_outer_let() {
  let source = "switch(0){case 0: let a = 1; break;} let a = 2;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(71));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn switch_discriminant_prefers_outer_binding() {
  let source = "let a = 0; switch(a){case 0: let a = 1; break;}";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(72));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let outer = sem
    .resolve_name_in_scope(sem.top_scope(), "a")
    .expect("expected outer binding");

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  let discriminant = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "a")
    .and_then(|(_, sym)| *sym)
    .expect("expected discriminant to resolve");
  assert_eq!(discriminant, outer);
}

#[test]
fn switch_discriminant_does_not_resolve_to_case_lexicals() {
  let source = "switch(a){case 0: let a = 1; break;}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(73));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  let discriminant = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "a")
    .and_then(|(_, sym)| *sym);
  assert_eq!(discriminant, None);
}

#[test]
fn switch_case_expr_use_before_declaration_is_in_tdz() {
  let source = "switch(0){case a: let a = 1; break;}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(96));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn switch_case_body_use_before_declaration_is_in_tdz() {
  let source = "switch(0){case 0: a; let a = 1; break;}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(97));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

/// ECMA-262 §14.12.1 SwitchStatement early errors: LexicallyDeclaredNames of
/// CaseBlock must be unique and must not intersect VarDeclaredNames. All case
/// / default clauses share one lexical environment.
fn assert_switch_caseblock_early_error(source: &str, file: u32, code: &str) {
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap_or_else(|e| panic!("parse failed for `{source}`: {e:?}"));
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(file));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == code),
    "expected {code} for `{source}`, got {diagnostics:?}"
  );
}

#[test]
fn switch_caseblock_rejects_duplicate_let() {
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: let f; default: let f }",
    200,
    "BIND0001",
  );
}

#[test]
fn switch_caseblock_rejects_let_var_conflict() {
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: var f; default: let f }",
    201,
    "BIND0002",
  );
}

#[test]
fn switch_caseblock_rejects_duplicate_class() {
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: class f {} default: class f {} }",
    202,
    "BIND0001",
  );
}

#[test]
fn switch_caseblock_rejects_duplicate_async_function_in_sloppy() {
  // AsyncFunctionDeclaration is always lexical (Annex B.3.2 does not apply).
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: async function f() {} default: async function f() {} }",
    203,
    "BIND0001",
  );
}

#[test]
fn switch_caseblock_rejects_duplicate_generator_in_sloppy() {
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: function* f() {} default: function* f() {} }",
    204,
    "BIND0001",
  );
}

#[test]
fn switch_caseblock_rejects_async_function_vs_let() {
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: async function f() {} default: let f }",
    205,
    "BIND0001",
  );
}

#[test]
fn switch_caseblock_rejects_ordinary_function_vs_let_in_sloppy() {
  assert_switch_caseblock_early_error(
    "switch (0) { case 1: function f() {} default: let f }",
    206,
    "BIND0002",
  );
}

#[test]
fn switch_caseblock_rejects_duplicate_ordinary_function_in_strict() {
  assert_switch_caseblock_early_error(
    "'use strict'; switch (0) { case 1: function f() {} default: function f() {} }",
    207,
    "BIND0001",
  );
}

#[test]
fn switch_caseblock_allows_duplicate_ordinary_function_in_sloppy() {
  // Annex B.3.2: two ordinary FunctionDeclarations in a CaseBlock are not an
  // early error in non-strict code (test262 marks the strict-only variants).
  let source = "switch (0) { case 1: function f() {} default: function f() {} }";
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(208));
  assert!(
    diagnostics
      .iter()
      .all(|d| d.code.as_str() != "BIND0001" && d.code.as_str() != "BIND0002"),
    "unexpected early errors for Annex B switch functions: {diagnostics:?}"
  );
}

#[test]
fn for_of_lexicals_are_not_visible_outside_loop() {
  let mut ast = parse("for (let a of [1]) {} a;").unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(74));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  assert_eq!(collect.id_exprs, vec![("a".to_string(), None)]);
}

#[test]
fn for_of_rhs_prefers_outer_binding() {
  use crate::assoc::js::resolved_symbol;
  use parse_js::loc::Loc;

  #[derive(Default, VisitorMut)]
  #[visitor(IdExprNode(enter))]
  struct ACollector {
    uses: Vec<(Loc, Option<SymbolId>)>,
  }

  impl ACollector {
    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == "a" {
        self.uses.push((node.loc, resolved_symbol(&node.assoc)));
      }
    }
  }

  let source = "let a = 0; for (let a of [a]) { a; } a;";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(75));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let outer = sem
    .resolve_name_in_scope(sem.top_scope(), "a")
    .expect("expected outer binding");

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  let decls: Vec<_> = collect
    .id_pats
    .iter()
    .filter(|(name, _, is_decl)| name == "a" && *is_decl)
    .filter_map(|(_, resolved, _)| *resolved)
    .collect();
  assert_eq!(decls.len(), 2);
  let loop_binding = decls
    .iter()
    .copied()
    .find(|sym| *sym != outer)
    .expect("expected loop binding");

  let mut uses = ACollector::default();
  ast.drive_mut(&mut uses);
  uses.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(uses.uses.len(), 3);
  assert_eq!(uses.uses[0].1, Some(outer)); // rhs `[a]`
  assert_eq!(uses.uses[1].1, Some(loop_binding)); // body `a;`
  assert_eq!(uses.uses[2].1, Some(outer)); // after loop `a;`
}

#[test]
fn for_of_body_can_shadow_loop_binding() {
  let source = "for (let a of [1]) { let a = 2; a; }";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(76));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  let decls: Vec<_> = collect
    .id_pats
    .iter()
    .filter(|(name, _, is_decl)| name == "a" && *is_decl)
    .filter_map(|(_, resolved, _)| *resolved)
    .collect();
  assert_eq!(decls.len(), 2);

  let scope0 = sem.symbol(decls[0]).decl_scope;
  let scope1 = sem.symbol(decls[1]).decl_scope;
  let inner = if sem.scope(scope0).parent == Some(scope1) {
    decls[0]
  } else if sem.scope(scope1).parent == Some(scope0) {
    decls[1]
  } else {
    panic!("expected loop binding scope to be parent of body binding scope");
  };

  let a_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "a")
    .and_then(|(_, sym)| *sym)
    .expect("expected `a` use to resolve");
  assert_eq!(a_use, inner);
}

#[test]
fn for_triple_let_shadows_outer_without_conflict() {
  use crate::assoc::js::resolved_symbol;
  use parse_js::loc::Loc;

  #[derive(Default, VisitorMut)]
  #[visitor(IdExprNode(enter))]
  struct ICollector {
    uses: Vec<(Loc, Option<SymbolId>)>,
  }

  impl ICollector {
    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == "i" {
        self.uses.push((node.loc, resolved_symbol(&node.assoc)));
      }
    }
  }

  let source = "let i = 0; for (let i = 0; i < 1; i++) { } i;";
  let mut ast = parse(source).unwrap();
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(77));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let outer = sem
    .resolve_name_in_scope(sem.top_scope(), "i")
    .expect("expected outer binding");

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);
  let decls: Vec<_> = collect
    .id_pats
    .iter()
    .filter(|(name, _, is_decl)| name == "i" && *is_decl)
    .filter_map(|(_, resolved, _)| *resolved)
    .collect();
  assert_eq!(decls.len(), 2);
  let loop_binding = decls
    .iter()
    .copied()
    .find(|sym| *sym != outer)
    .expect("expected loop binding");

  let mut uses = ICollector::default();
  ast.drive_mut(&mut uses);
  uses.uses.sort_by_key(|(loc, _)| loc.0);
  assert_eq!(uses.uses.len(), 3);
  assert_eq!(uses.uses[0].1, Some(loop_binding)); // condition `i < 1`
  assert_eq!(uses.uses[1].1, Some(loop_binding)); // update `i++`
  assert_eq!(uses.uses[2].1, Some(outer)); // after loop `i;`
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

#[test]
fn with_marks_nested_function_scopes_dynamic() {
  let mut ast = parse(r#"with (obj) { (() => shadow)(); (function () { shadow; })(); }"#).unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module, FileId(27));

  let arrow_scopes: Vec<_> = sem
    .scopes
    .iter()
    .filter(|(_, scope)| scope.kind == ScopeKind::ArrowFunction)
    .collect();
  assert_eq!(arrow_scopes.len(), 1);
  assert!(arrow_scopes[0].1.is_dynamic);

  let non_arrow_scopes: Vec<_> = sem
    .scopes
    .iter()
    .filter(|(_, scope)| scope.kind == ScopeKind::NonArrowFunction)
    .collect();
  assert_eq!(non_arrow_scopes.len(), 1);
  assert!(non_arrow_scopes[0].1.is_dynamic);
}

fn slice_range<'a>(source: &'a str, diagnostic: &Diagnostic) -> &'a str {
  let range = diagnostic.primary.range;
  &source[range.start as usize..range.end as usize]
}

fn parse_js_script(source: &str) -> Node<parse_js::ast::stx::TopLevel> {
  parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Js,
      source_type: SourceType::Script,
    },
  )
  .unwrap()
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
fn runtime_binding_suppresses_tdz_diagnostics() {
  let source = "function f(){ x; let x = 1; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Module, FileId(130));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0003"),
    "unexpected TDZ diagnostics: {diagnostics:?}"
  );

  // TDZ state is still computed and attached for runtime checks.
  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);
  let x_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "x")
    .and_then(|(_, info)| info.as_ref())
    .expect("expected `x` identifier reference");
  assert!(x_use.in_tdz);
}

#[test]
fn runtime_binding_still_reports_true_early_errors() {
  let source = "let x; let x;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Module, FileId(131));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0001");
  assert_eq!(slice_range(source, &diagnostics[0]), "x");
}

#[test]
fn runtime_binding_attaches_resolved_symbols() {
  let mut ast = parse("let x = 1; x;").unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Module, FileId(132));
  assert!(diagnostics.is_empty());

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  let decl_symbol = collect
    .id_pats
    .iter()
    .find(|(name, _, is_decl)| name == "x" && *is_decl)
    .and_then(|(_, sym, _)| *sym)
    .expect("expected `x` declaration symbol");
  let use_symbol = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "x")
    .and_then(|(_, sym)| *sym)
    .expect("expected `x` to resolve");

  assert_eq!(use_symbol, decl_symbol);
}

#[test]
fn runtime_binding_resolves_top_level_script_bindings() {
  let mut ast = parse_js_script("var x = 1; x;");
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, FileId(133));
  assert!(diagnostics.is_empty());

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  let decl_symbol = collect
    .id_pats
    .iter()
    .find(|(name, _, is_decl)| name == "x" && *is_decl)
    .and_then(|(_, sym, _)| *sym)
    .expect("expected `x` declaration symbol");
  let use_symbol = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "x")
    .and_then(|(_, sym)| *sym)
    .expect("expected `x` to resolve");

  assert_eq!(use_symbol, decl_symbol);
}

#[test]
fn lexical_declaration_in_if_body_is_reported() {
  let source = "if(true) let x = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(90));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0004");
  assert_eq!(slice_range(source, &diagnostics[0]), "let");
}

#[test]
fn lexical_declaration_in_label_body_is_reported() {
  let source = "label: let x = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(91));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0004");
  assert_eq!(slice_range(source, &diagnostics[0]), "let");
}

#[test]
fn strict_mode_function_declaration_in_if_body_is_reported() {
  let source = "'use strict'; if(true) function f(){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(92));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0004");
  assert_eq!(slice_range(source, &diagnostics[0]), "function");
}

#[test]
fn non_strict_function_declaration_in_while_body_is_reported() {
  let source = "while(false) function f(){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(93));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0004");
  assert_eq!(slice_range(source, &diagnostics[0]), "function");
}

#[test]
fn non_strict_labelled_function_declaration_is_only_allowed_in_statement_lists() {
  let source = "if(true) label: function f(){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(94));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0004");
  assert_eq!(slice_range(source, &diagnostics[0]), "function");
}

#[test]
fn strict_mode_restricted_identifier_in_parameter_is_reported() {
  let source = "'use strict'; function f(eval){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(95));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0005");
  assert_eq!(slice_range(source, &diagnostics[0]), "eval");
}

#[test]
fn class_names_always_restrict_eval_and_arguments() {
  let source = "class eval {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(96));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0005");
  assert_eq!(slice_range(source, &diagnostics[0]), "eval");
}

#[test]
fn module_import_restricted_identifier_is_reported() {
  let source = "import eval from 'x';";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(97));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0005");
  assert_eq!(slice_range(source, &diagnostics[0]), "eval");
}

#[test]
fn strict_assignment_to_eval_is_reported() {
  let source = "'use strict'; eval = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(101));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0005");
  assert_eq!(slice_range(source, &diagnostics[0]), "eval");
}

#[test]
fn strict_destructuring_assignment_to_eval_is_reported() {
  let source = "'use strict'; ({eval} = obj);";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(102));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0005");
  assert_eq!(slice_range(source, &diagnostics[0]), "eval");
}

#[test]
fn strict_for_in_assignment_to_eval_is_reported() {
  let source = "'use strict'; for (eval in obj) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(103));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0005");
  assert_eq!(slice_range(source, &diagnostics[0]), "eval");
}

#[test]
fn const_without_initializer_is_reported() {
  let source = "const a;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(400));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0015"),
    "expected BIND0015, got {diagnostics:?}"
  );
}

#[test]
fn const_in_for_triple_head_without_initializer_is_reported() {
  let source = "for (const a;;) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(401));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0015"),
    "expected BIND0015, got {diagnostics:?}"
  );
}

#[test]
fn const_with_initializer_is_accepted() {
  let source = "const a = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(402));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0015"),
    "unexpected BIND0015, got {diagnostics:?}"
  );
}

#[test]
fn const_without_initializer_allowed_in_for_of_head() {
  // A `for-of`/`for-in` head binds per iteration and needs no initializer.
  let source = "for (const a of [1]) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(403));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0015"),
    "unexpected BIND0015, got {diagnostics:?}"
  );
}

#[test]
fn let_as_lexical_binding_name_is_reported() {
  let source = "let let;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(404));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0016"),
    "expected BIND0016, got {diagnostics:?}"
  );
}

#[test]
fn let_as_const_binding_name_is_reported() {
  let source = "const let = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(405));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0016"),
    "expected BIND0016, got {diagnostics:?}"
  );
}

#[test]
fn let_binding_name_in_for_of_head_is_reported() {
  let source = "for (let let of a);";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(406));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0016"),
    "expected BIND0016, got {diagnostics:?}"
  );
}

#[test]
fn var_named_let_is_accepted_in_sloppy_mode() {
  // `let` is only a reserved BindingIdentifier for lexical declarations; a
  // sloppy-mode `var let` is legal.
  let source = "var let;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(407));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0016"),
    "unexpected BIND0016, got {diagnostics:?}"
  );
}

#[test]
fn duplicate_proto_data_property_is_reported() {
  let source = "({ __proto__: 1, __proto__: 2 })";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(408));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0017"),
    "expected BIND0017, got {diagnostics:?}"
  );
}

#[test]
fn duplicate_proto_mixed_string_and_identifier_is_reported() {
  let source = "({ \"__proto__\": null, __proto__: null })";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(409));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0017"),
    "expected BIND0017, got {diagnostics:?}"
  );
}

#[test]
fn single_proto_data_property_is_accepted() {
  let source = "({ __proto__: null, x: 1 })";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(410));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0017"),
    "unexpected BIND0017, got {diagnostics:?}"
  );
}

#[test]
fn proto_shorthand_and_method_do_not_count() {
  // Shorthand `__proto__` and a computed `["__proto__"]` are not colon-form
  // data properties, so they do not trigger the duplicate-`__proto__` error.
  let source = "var __proto__ = 1; ({ __proto__, [\"__proto__\"]: 2 })";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(411));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0017"),
    "unexpected BIND0017, got {diagnostics:?}"
  );
}

// --- Module ExportedNames / ExportedBindings (ECMA-262 §16.2.1.1) ---
//
// V8/`node --check` evidence (2026-07-23): `export const a = 1; export {a}` is a
// Syntax Error — declaration exports and export lists both contribute to
// ExportedNames, so the second `a` is a duplicate even though there is only one
// local binding. Same for `export {a}; export function a(){}` / `export var a`
// twice. Legal: `export {a as b, a as c}` (same local, distinct exported names);
// `export {x} from "m"` / `export * from "m"` (no local ExportedBindings).

#[test]
fn duplicate_export_list_name_is_reported() {
  let source = "let a; export {a, a};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(420));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018, got {diagnostics:?}"
  );
  let diag = diagnostics
    .iter()
    .find(|d| d.code.as_str() == "BIND0018")
    .unwrap();
  assert_eq!(slice_range(source, diag), "a");
  assert!(
    diag.labels.iter().any(|l| l.message.contains("previous")),
    "expected secondary label on first export, got {diag:?}"
  );
}

#[test]
fn duplicate_export_via_as_alias_is_reported() {
  let source = "let a, b; export {a, b as a};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(421));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018, got {diagnostics:?}"
  );
}

#[test]
fn duplicate_default_export_is_reported() {
  let source = "export default 1; export default 2;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(422));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018, got {diagnostics:?}"
  );
}

#[test]
fn declaration_and_export_list_duplicate_exported_name() {
  // Spec + V8: ExportedNames contains `a` twice → Syntax Error (not merely a
  // second reference to the same binding).
  let source = "export const a = 1; export {a};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(423));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018, got {diagnostics:?}"
  );
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0019"),
    "local `a` is declared; must not emit BIND0019, got {diagnostics:?}"
  );
}

#[test]
fn export_list_then_declaration_duplicate_exported_name() {
  let source = "export {a}; export function a() {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(424));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018, got {diagnostics:?}"
  );
}

#[test]
fn export_var_twice_is_duplicate_exported_name() {
  let source = "export var a; export var a;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(425));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018, got {diagnostics:?}"
  );
}

#[test]
fn same_local_distinct_exported_names_is_legal() {
  let source = "const a = 1; export {a as b, a as c};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(426));
  assert!(
    diagnostics
      .iter()
      .all(|d| d.code.as_str() != "BIND0018" && d.code.as_str() != "BIND0019"),
    "unexpected module-export diagnostic, got {diagnostics:?}"
  );
}

#[test]
fn reexport_does_not_require_local_binding() {
  let source = r#"export {x} from "m"; export * from "n"; export * as ns from "o";"#;
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(427));
  assert!(
    diagnostics
      .iter()
      .all(|d| d.code.as_str() != "BIND0018" && d.code.as_str() != "BIND0019"),
    "unexpected module-export diagnostic, got {diagnostics:?}"
  );
}

#[test]
fn undeclared_export_binding_is_reported() {
  let source = "export {a};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(428));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0019"),
    "expected BIND0019, got {diagnostics:?}"
  );
  let diag = diagnostics
    .iter()
    .find(|d| d.code.as_str() == "BIND0019")
    .unwrap();
  assert_eq!(slice_range(source, diag), "a");
}

#[test]
fn undeclared_export_local_with_declared_alias_target() {
  // `b` is local ExportedBindings; exported name `a` colliding with a local
  // `var a` does not satisfy the local-binding requirement for `b`.
  let source = "var a; export {b as a};";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(429));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0019"),
    "expected BIND0019, got {diagnostics:?}"
  );
}

#[test]
fn module_export_early_errors_survive_runtime_bind() {
  // True early errors — unlike BIND0003, `bind_js_for_runtime` must keep them.
  let source = "export {a}; export default 1; export default 2;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Module, FileId(430));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0019"),
    "expected BIND0019 from runtime bind, got {diagnostics:?}"
  );
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0018"),
    "expected BIND0018 from runtime bind, got {diagnostics:?}"
  );
}

#[test]
fn duplicate_import_binding_is_already_covered_by_bind0001() {
  let source = r#"import {a, a} from "m";"#;
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(431));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0001"),
    "expected BIND0001 for duplicate import binding, got {diagnostics:?}"
  );
}

#[test]
fn strict_with_statement_is_reported() {
  let source = "'use strict'; with({}){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(104));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0007");
  assert_eq!(slice_range(source, &diagnostics[0]), "with");
}

#[test]
fn strict_delete_identifier_is_reported() {
  let source = "'use strict'; delete a;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(105));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0008");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn strict_reserved_word_in_var_decl_is_reported() {
  let source = "var implements = 1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(117));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0013");
  assert_eq!(slice_range(source, &diagnostics[0]), "implements");
}

#[test]
fn strict_reserved_word_in_identifier_reference_is_reported() {
  let source = "implements;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(118));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0013");
  assert_eq!(slice_range(source, &diagnostics[0]), "implements");
}

#[test]
fn strict_reserved_word_in_label_is_reported() {
  let source = "implements: for(;;) break;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(119));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0013");
  assert_eq!(slice_range(source, &diagnostics[0]), "implements");
}

#[test]
fn sloppy_mode_allows_strict_reserved_words() {
  let source = "var implements = 1; implements;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(120));
  assert!(diagnostics.is_empty());
}

#[test]
fn new_target_at_top_level_is_reported() {
  let source = "new.target;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(121));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0014");
  assert_eq!(slice_range(source, &diagnostics[0]), "new.target");
}

#[test]
fn new_target_in_top_level_arrow_is_reported() {
  let source = "(() => new.target)();";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(122));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0014");
  assert_eq!(slice_range(source, &diagnostics[0]), "new.target");
}

#[test]
fn new_target_in_function_is_allowed() {
  let source = "function f(){ return new.target; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(123));
  assert!(diagnostics.is_empty());
}

#[test]
fn new_target_in_class_field_initializer_is_allowed() {
  let source = "class C { x = new.target; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(124));
  assert!(diagnostics.is_empty());
}

#[test]
fn new_target_in_class_computed_key_is_reported() {
  let source = "class C { [new.target](){ } }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(125));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0014");
  assert_eq!(slice_range(source, &diagnostics[0]), "new.target");
}

#[test]
fn strict_octal_literal_is_reported() {
  let source = "'use strict'; 010;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(106));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0009");
  assert_eq!(slice_range(source, &diagnostics[0]), "010");
}

#[test]
fn strict_decimal_literal_with_leading_zero_is_reported() {
  let source = "'use strict'; 08;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(107));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0010");
  assert_eq!(slice_range(source, &diagnostics[0]), "08");
}

#[test]
fn strict_decimal_literal_with_leading_zero_exponent_is_reported() {
  let source = "'use strict'; 08e1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(114));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0010");
  assert_eq!(slice_range(source, &diagnostics[0]), "08e1");
}

#[test]
fn strict_decimal_literal_with_leading_zero_fraction_is_reported() {
  let source = "'use strict'; 08.1;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(115));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0010");
  assert_eq!(slice_range(source, &diagnostics[0]), "08.1");
}

#[test]
fn strict_octal_literal_property_key_is_reported() {
  let source = "'use strict'; ({010: 1});";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(108));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0009");
  assert_eq!(slice_range(source, &diagnostics[0]), "010");
}

#[test]
fn strict_decimal_literal_property_key_with_exponent_is_reported() {
  let source = "'use strict'; ({08e1: 1});";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(116));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0010");
  assert_eq!(slice_range(source, &diagnostics[0]), "08e1");
}

#[test]
fn strict_octal_escape_in_string_literal_is_reported() {
  let source = "'use strict'; \"\\1\";";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(109));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0011");
  assert_eq!(slice_range(source, &diagnostics[0]), "\\1");
}

#[test]
fn strict_octal_escape_in_property_key_is_reported() {
  let source = "'use strict'; ({\"\\1\": 1});";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(110));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0011");
  assert_eq!(slice_range(source, &diagnostics[0]), "\\1");
}

#[test]
fn template_literal_octal_escape_is_reported() {
  let source = "`\\1`;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(111));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0012");
  assert_eq!(slice_range(source, &diagnostics[0]), "\\1");
}

#[test]
fn template_literal_escape_8_is_reported() {
  let source = "`\\8`;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(112));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0012");
  assert_eq!(slice_range(source, &diagnostics[0]), "\\8");
}

#[test]
fn tagged_templates_allow_octal_escapes() {
  let source = "String.raw`\\1`;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(113));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn duplicate_parameters_in_strict_functions_are_reported() {
  let source = "'use strict'; function f(a,a){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(98));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0006");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
}

#[test]
fn duplicate_parameters_in_sloppy_simple_functions_are_allowed() {
  let source = "function f(a,a){}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(99));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn object_literal_method_duplicate_parameters_are_reported_in_sloppy_scripts() {
  let source = "!{ a(b, b){} };";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(200));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0006"),
    "expected BIND0006, got {diagnostics:?}"
  );
}

#[test]
fn object_literal_generator_method_duplicate_parameters_are_reported_in_sloppy_scripts() {
  let source = "!{ *a(b, b){} };";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(201));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0006"),
    "expected BIND0006, got {diagnostics:?}"
  );
}

#[test]
fn sloppy_object_literal_method_allows_yield_parameter() {
  // Object methods are not automatically strict (unlike class bodies).
  // ECMA-262 §13.1.1 / §15.4 — `yield` as a BindingIdentifier is only banned
  // in strict code (or generator formal parameters, which the parser rejects).
  let source = "({ a(yield){} });";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(202));
  assert!(
    diagnostics
      .iter()
      .all(|d| d.code.as_str() != "BIND0013" && d.code.as_str() != "BIND0005"),
    "unexpected strict-mode param diagnostics: {diagnostics:?}"
  );
}

#[test]
fn sloppy_object_literal_method_allows_eval_parameter() {
  let source = "({ a(eval){} });";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(203));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0005"),
    "unexpected BIND0005, got {diagnostics:?}"
  );
}

#[test]
fn escaped_use_strict_is_not_a_directive() {
  // ECMA-262 §11.2.1 — `'use\x20strict'` is not a Use Strict Directive.
  let source = "'use\\x20strict'; with(x){}";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(210));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0007"),
    "escaped directive must not enable strict/with rejection: {diagnostics:?}"
  );
}

#[test]
fn real_use_strict_still_rejects_with() {
  let source = "'use strict'; with(x){}";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(211));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0007"),
    "expected BIND0007, got {diagnostics:?}"
  );
}

#[test]
fn sloppy_setter_allows_yield_and_eval_parameters() {
  for (source, file) in [("({set a(yield){}})", 212u32), ("({set a(eval){}})", 213)] {
    let mut ast = parse_js_script(source);
    let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(file));
    assert!(
      diagnostics
        .iter()
        .all(|d| { d.code.as_str() != "BIND0013" && d.code.as_str() != "BIND0005" }),
      "sloppy setter params must be accepted ({source}): {diagnostics:?}"
    );
  }
}

#[test]
fn yield_as_identifier_in_non_generator_accessor_inside_generator() {
  // Accessors (and non-generator methods) reset yield context: `yield` is an
  // IdentifierReference in the accessor body, legal in sloppy code (§15.5.1).
  for (source, file) in [
    ("function *a(){({get b(){yield}})}", 214u32),
    ("function *a(){({set b(c){yield}})}", 215),
    ("function *a(){({b(){yield}})}", 216),
    ("function *a(){({set b(yield){}})}", 217),
  ] {
    let mut ast = parse_js_script(source);
    let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(file));
    assert!(
      diagnostics.iter().all(|d| d.code.as_str() != "BIND0013"),
      "yield must not be treated as strict-reserved in nested non-generator ({source}): {diagnostics:?}"
    );
  }
}

#[test]
fn strict_setter_still_rejects_yield_parameter() {
  let source = "'use strict'; ({set a(yield){}});";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(218));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0013"),
    "expected BIND0013, got {diagnostics:?}"
  );
}

#[test]
fn annex_b_if_body_function_may_reuse_catch_param_name() {
  // Web reality / V8: `catch (a) { function a(){} }` is an early error, but
  // `catch (a) { if (1) function a(){} }` is allowed (Annex B statement position).
  let source = "try {} catch (a) { if(1) function a(){} }";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(219));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0001"),
    "unexpected BIND0001, got {diagnostics:?}"
  );

  let reject = "try {} catch (a) { function a(){} }";
  let mut ast = parse_js_script(reject);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Script, FileId(220));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0001"),
    "expected BIND0001 for StatementList function in catch, got {diagnostics:?}"
  );
}

#[test]
fn sloppy_script_allows_duplicate_parameters_in_functions() {
  let source = "function f(a, a){};";
  let mut ast = parse_js_script(source);
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(204));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0006"),
    "unexpected BIND0006, got {diagnostics:?}"
  );
}

#[test]
fn duplicate_parameters_in_arrow_functions_are_reported() {
  let source = "const f = (a,a) => a;";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(100));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0006");
  assert_eq!(slice_range(source, &diagnostics[0]), "a");
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
fn parameter_default_initializer_does_not_resolve_to_body_var_decls() {
  let source = "function f(a = x) { var x = 1; }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(88));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);
  let x_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "x")
    .and_then(|(_, info)| info.as_ref())
    .expect("x use");
  assert_eq!(x_use.symbol, None);
  assert!(!x_use.in_tdz);
}

#[test]
fn parameter_default_initializer_does_not_resolve_to_body_function_decls() {
  let source = "function f(a = g) { function g(){} }";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(89));
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let mut collect = CollectWithInfo::default();
  ast.drive_mut(&mut collect);
  let g_use = collect
    .id_exprs
    .iter()
    .find(|(name, _)| name == "g")
    .and_then(|(_, info)| info.as_ref())
    .expect("g use");
  assert_eq!(g_use.symbol, None);
  assert!(!g_use.in_tdz);
}

#[test]
fn parameter_default_initializer_later_parameter_is_in_tdz() {
  let source = "function f(a = b, b = 1) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(83));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "b");
}

#[test]
fn parameter_default_initializer_can_reference_prior_parameter() {
  let source = "function f(a = 1, b = a) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(84));
  assert!(
    diagnostics.is_empty(),
    "expected parameter initializers to allow referencing earlier bindings, got {diagnostics:?}"
  );
}

#[test]
fn parameter_destructuring_defaults_can_reference_prior_binding() {
  let source = "function f({a, b = a}) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(85));
  assert!(
    diagnostics.is_empty(),
    "expected destructuring parameter defaults to allow referencing earlier bindings, got {diagnostics:?}"
  );
}

#[test]
fn parameter_destructuring_defaults_later_binding_is_in_tdz() {
  let source = "function f({a = b, b}) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(86));
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), "BIND0003");
  assert_eq!(slice_range(source, &diagnostics[0]), "b");
}

#[test]
fn parameter_default_initializer_closure_uses_do_not_trigger_tdz_diagnostics() {
  let source = "function f(a = () => b, b = 1) {}";
  let mut ast = parse(source).unwrap();
  let (_sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(87));
  assert!(
    diagnostics.is_empty(),
    "expected nested closures in parameter initializers to not report TDZ, got {diagnostics:?}"
  );
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

#[test]
fn undeclared_private_in_expression_is_reported() {
  // AllPrivateIdentifiersValid — `#name in {}` at script top level.
  let source = "#name in {};";
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, FileId(500));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0020"),
    "expected BIND0020, got {diagnostics:?}"
  );
}

#[test]
fn undeclared_private_in_inside_class_is_reported() {
  let source = "class C { #a; constructor() { #b in {}; } }";
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, FileId(501));
  let diag = diagnostics
    .iter()
    .find(|d| d.code.as_str() == "BIND0020")
    .unwrap_or_else(|| panic!("expected BIND0020, got {diagnostics:?}"));
  assert_eq!(slice_range(source, diag), "#b");
}

#[test]
fn undeclared_private_member_access_is_reported() {
  let source = "{ this.#x }";
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, FileId(502));
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "BIND0020"),
    "expected BIND0020, got {diagnostics:?}"
  );
}

#[test]
fn declared_private_in_and_member_are_accepted() {
  let source = "class C { #f; m(o) { o.#f; return #f in o; } }";
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, FileId(503));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0020"),
    "unexpected BIND0020, got {diagnostics:?}"
  );
}

#[test]
fn outer_class_private_name_visible_in_nested_class() {
  // AllPrivateIdentifiersValid concatenates outer names into nested ClassBody.
  let source = "class Outer { #x; m() { class Inner { n(o) { return #x in o; } } } }";
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .unwrap();
  let (_sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, FileId(504));
  assert!(
    diagnostics.iter().all(|d| d.code.as_str() != "BIND0020"),
    "unexpected BIND0020, got {diagnostics:?}"
  );
}
