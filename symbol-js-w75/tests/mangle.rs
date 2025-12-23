use derive_visitor::Drive;
use derive_visitor::Visitor;
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ObjMember;
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::pat::ObjPatProp;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::parse;
use symbol_js::mangle::mangle_identifiers;
use symbol_js::mangle::MangleOptions;
use symbol_js::TopLevelMode;

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;

#[derive(Default, Visitor)]
#[visitor(IdExprNode(enter), IdPatNode(enter))]
struct NameCollector {
  expr: Vec<String>,
  pat: Vec<String>,
}

impl NameCollector {
  fn enter_id_expr_node(&mut self, node: &IdExprNode) {
    self.expr.push(node.stx.name.clone());
  }

  fn enter_id_pat_node(&mut self, node: &IdPatNode) {
    self.pat.push(node.stx.name.clone());
  }
}

fn collect_names(top: &Node<TopLevel>) -> NameCollector {
  let mut collector = NameCollector::default();
  top.drive(&mut collector);
  collector
}

#[test]
fn basic_local_renaming() {
  let mut top = parse("() => { let my_first_variable = 1; my_first_variable; }").unwrap();
  let result = mangle_identifiers(&mut top, TopLevelMode::Global, &MangleOptions::default());
  let names = collect_names(&top);

  assert!(result.renamed.values().any(|v| v == "a"));
  assert!(names.pat.iter().all(|n| n != "my_first_variable"));
  assert!(names.expr.iter().all(|n| n != "my_first_variable"));
  assert!(names.pat.contains(&"a".to_string()));
  assert!(names.expr.contains(&"a".to_string()));
}

#[test]
fn avoid_unknown_globals() {
  let mut top = parse("() => { a; let x; }").unwrap();
  let result = mangle_identifiers(&mut top, TopLevelMode::Global, &MangleOptions::default());
  let names = collect_names(&top);

  assert!(result.renamed.values().any(|v| v == "b"));
  assert!(names.pat.iter().all(|n| n != "a"));
  assert!(names.pat.contains(&"b".to_string()));
}

#[test]
fn avoid_capture_across_scopes() {
  let mut top = parse("(() => { let x; (() => { x; let y; })(); })();").unwrap();
  mangle_identifiers(&mut top, TopLevelMode::Global, &MangleOptions::default());
  let names = collect_names(&top);

  assert!(names.pat.contains(&"a".to_string()));
  assert!(names.pat.contains(&"b".to_string()));
}

#[test]
fn reuse_names_when_no_foreign_use() {
  let mut top = parse("(() => { let x; (() => { let y; })(); })();").unwrap();
  mangle_identifiers(&mut top, TopLevelMode::Global, &MangleOptions::default());
  let names = collect_names(&top);

  let count_a = names.pat.iter().filter(|n| n.as_str() == "a").count();
  assert_eq!(count_a, 2);
}

type ObjMemberNode = Node<ObjMember>;

#[derive(Default, Visitor)]
#[visitor(ObjMemberNode(enter))]
struct ObjMemberFinder {
  key: Option<String>,
  value_ident: Option<String>,
}

impl ObjMemberFinder {
  fn enter_obj_member_node(&mut self, node: &ObjMemberNode) {
    if self.key.is_some() {
      return;
    }
    if let ObjMemberType::Valued { key, val } = &node.stx.typ {
      if let ClassOrObjKey::Direct(direct) = key {
        self.key = Some(direct.stx.key.clone());
      }
      if let ClassOrObjVal::Prop(Some(expr)) = val {
        if let parse_js::ast::expr::Expr::Id(id) = expr.stx.as_ref() {
          self.value_ident = Some(id.stx.name.clone());
        }
      }
    }
  }
}

#[test]
fn expand_object_shorthand_literal() {
  let mut top = parse("(() => { let long; return { long }; })();").unwrap();
  mangle_identifiers(&mut top, TopLevelMode::Global, &MangleOptions::default());

  let mut finder = ObjMemberFinder::default();
  top.drive(&mut finder);
  assert_eq!(finder.key.as_deref(), Some("long"));
  assert_eq!(finder.value_ident.as_deref(), Some("a"));
}

type ObjPatPropNode = Node<ObjPatProp>;

#[derive(Default, Visitor)]
#[visitor(ObjPatPropNode(enter))]
struct ObjPatPropFinder {
  shorthand: Option<bool>,
  name: Option<String>,
}

impl ObjPatPropFinder {
  fn enter_obj_pat_prop_node(&mut self, node: &ObjPatPropNode) {
    if self.shorthand.is_some() {
      return;
    }
    self.shorthand = Some(node.stx.shorthand);
    if let Pat::Id(id) = node.stx.target.stx.as_ref() {
      self.name = Some(id.stx.name.clone());
    }
  }
}

#[test]
fn expand_object_pattern_shorthand() {
  let mut top = parse("(() => { let obj; let { long } = obj; })();").unwrap();
  mangle_identifiers(&mut top, TopLevelMode::Global, &MangleOptions::default());

  let mut finder = ObjPatPropFinder::default();
  top.drive(&mut finder);
  assert_eq!(finder.shorthand, Some(false));
  assert_ne!(finder.name.as_deref(), Some("long"));
  assert!(finder.name.is_some());
}

#[test]
fn update_export_list_binding() {
  let mut top = parse("let foo = 1; export { foo }; ").unwrap();
  mangle_identifiers(&mut top, TopLevelMode::Module, &MangleOptions::default());

  let names = collect_names(&top);
  assert!(names.pat.contains(&"a".to_string()));

  let mut found = false;
  for stmt in top.stx.body.iter() {
    if let Stmt::ExportList(export) = stmt.stx.as_ref() {
      found = true;
      match &export.stx.names {
        parse_js::ast::import_export::ExportNames::Specific(entries) => {
          assert_eq!(entries.len(), 1);
          let entry = &entries[0];
          assert_eq!(entry.stx.exportable, "a");
          assert_eq!(entry.stx.alias.stx.name, "foo");
        }
        _ => panic!("expected export list"),
      }
    }
  }
  assert!(found, "export list not found");
}

#[test]
fn export_declaration_pinned() {
  let mut top = parse("export const foo = 1;").unwrap();
  let result = mangle_identifiers(&mut top, TopLevelMode::Module, &MangleOptions::default());

  assert!(result.renamed.is_empty());

  let names = collect_names(&top);
  assert!(names.pat.contains(&"foo".to_string()));
  assert!(names.expr.is_empty());
}
