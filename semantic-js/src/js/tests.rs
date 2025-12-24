use crate::declared_symbol;
use crate::js::bind_js;
use crate::js::SymbolId;
use crate::resolved_symbol;
use crate::TopLevelMode;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::parse;

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
