use crate::assoc::js::{declared_symbol, resolved_symbol, resolved_symbol_info, ResolvedSymbol};
use crate::js::{bind_js, declare, JsSemantics, ScopeKind, SymbolId, TopLevelMode};
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
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
  writeln!(&mut out, "names {:?}", sem.names).unwrap();
  writeln!(&mut out, "name_lookup {:?}", sem.name_lookup).unwrap();
  for (idx, scope) in sem.scopes.iter().enumerate() {
    writeln!(
      &mut out,
      "scope {idx} {:?} parent {:?}",
      scope.kind,
      scope.parent.map(|p| p.index())
    )
    .unwrap();
    let children: Vec<_> = scope.children.iter().map(|child| child.index()).collect();
    writeln!(&mut out, "  children {children:?}").unwrap();
    writeln!(
      &mut out,
      "  dynamic {} direct_eval {}",
      scope.is_dynamic, scope.has_direct_eval
    )
    .unwrap();
    let tdz: Vec<_> = scope.tdz_bindings.iter().map(|sym| sym.index()).collect();
    writeln!(&mut out, "  tdz_bindings {tdz:?}").unwrap();
    let symbols: Vec<_> = scope
      .iter_symbols_sorted()
      .map(|(name, symbol)| (name.index(), symbol.index()))
      .collect();
    writeln!(&mut out, "  symbols {symbols:?}").unwrap();
  }
  for (idx, symbol) in sem.symbols.iter().enumerate() {
    writeln!(
      &mut out,
      "symbol {idx} name {} decl_scope {}",
      symbol.name.index(),
      symbol.decl_scope.index()
    )
    .unwrap();
  }
  out.into_bytes()
}

#[test]
fn shadowing_prefers_inner_bindings() {
  let mut ast = parse("let a = 1; { let a = 2; a; } a;").unwrap();
  let (_sem, _res) = bind_js(&mut ast, TopLevelMode::Module);

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
  let (_sem, _res) = bind_js(&mut ast, TopLevelMode::Module);

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
  let (_sem, _res) = bind_js(&mut ast, TopLevelMode::Module);

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
  let (_sem, _res) = bind_js(&mut ast, TopLevelMode::Module);

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
  let (sem, _res) = bind_js(&mut ast, TopLevelMode::Module);

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
fn public_resolve_handles_late_declarations() {
  let mut ast = parse("later; const later = 1;").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module);

  let resolved = sem.resolve_name_in_scope(sem.top_scope(), "later");
  let later = sem.name_id("later").expect("name interned");
  assert_eq!(resolved.map(|id| sem.symbol(id).name), Some(later));
}

#[test]
fn public_resolve_traverses_parents() {
  let mut ast = parse("const outer = 1; { outer; }").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module);

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
  let sem = declare(&mut ast, TopLevelMode::Module);

  assert_eq!(sem.resolve_name_in_scope(sem.top_scope(), "missing"), None);
}

#[test]
fn scope_symbols_iteration_is_stable() {
  let mut ast = parse("let b = 1; let a = 2;").unwrap();
  let sem = declare(&mut ast, TopLevelMode::Module);

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
    let sem = declare(&mut ast, TopLevelMode::Module);
    snapshot(&sem)
  };
  let second = {
    let mut ast = parse(source).unwrap();
    let sem = declare(&mut ast, TopLevelMode::Module);
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
  let sem = declare(&mut ast, TopLevelMode::Module);

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
