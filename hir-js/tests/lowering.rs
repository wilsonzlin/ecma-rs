use diagnostics::FileId;
use hir_js::lower_file;
use hir_js::lower_file_with_diagnostics;
use hir_js::lower_from_source;
use hir_js::lower_from_source_with_kind;
use hir_js::BodyId;
use hir_js::BodyKind;
use hir_js::DefKind;
use hir_js::ExportDefaultValue;
use hir_js::ExportKind;
use hir_js::ExprId;
use hir_js::ExprKind;
use hir_js::FileKind;
use hir_js::ImportKind;
use hir_js::ObjectKey;
use hir_js::ObjectProperty;
use hir_js::StmtKind;
use hir_js::TypeExprKind;
use hir_js::TypeName;
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::loc::Loc;
use parse_js::parse;
use proptest::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashSet};

fn computed_methods(result: &hir_js::LowerResult) -> Vec<&hir_js::DefData> {
  let names = &result.names;
  result
    .defs
    .iter()
    .filter(|def| def.path.kind == DefKind::Method)
    .filter(|def| {
      names
        .resolve(def.path.name)
        .map(|name| name.starts_with("<computed:"))
        .unwrap_or(false)
    })
    .collect()
}

#[test]
fn def_ids_are_sorted_and_stable() {
  let source = "function f() {}\nconst b = 2;\nconst a = 1;";
  let ast = parse(source).expect("parse");
  let (result, diagnostics) = lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let names: Vec<_> = result
    .defs
    .iter()
    .map(|def| result.names.resolve(def.path.name).unwrap().to_string())
    .collect();
  let kinds: Vec<_> = result.defs.iter().map(|def| def.path.kind).collect();

  assert_eq!(names, vec!["f", "a", "b"]);
  assert_eq!(kinds, vec![DefKind::Function, DefKind::Var, DefKind::Var]);

  let ast_again = parse(source).expect("parse");
  let (result_again, diagnostics_again) =
    lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast_again);
  assert!(diagnostics_again.is_empty());
  let names_again: Vec<_> = result_again
    .defs
    .iter()
    .map(|def| {
      result_again
        .names
        .resolve(def.path.name)
        .unwrap()
        .to_string()
    })
    .collect();
  assert_eq!(names, names_again);
}

#[test]
fn def_ids_survive_unrelated_insertions() {
  let base = "function keep() {}\nconst value = 1;";
  let with_extra = "function keep() {}\nconst extra = 0;\nconst value = 1;";

  let base_ast = parse(base).expect("parse base");
  let base_result = lower_file(FileId(0), FileKind::Ts, &base_ast);

  let extra_ast = parse(with_extra).expect("parse variant");
  let extra_result = lower_file(FileId(0), FileKind::Ts, &extra_ast);

  for (path, id) in base_result.hir.def_paths.iter() {
    let other = extra_result
      .hir
      .def_paths
      .get(path)
      .expect("path should exist in variant");
    assert_eq!(id, other, "def id changed for path {:?}", path);
  }
}

#[test]
fn lowers_enum_members_as_defs() {
  let source = r#"enum Color { Red, Green = 2, Blue = "b" }"#;
  let result = lower_from_source_with_kind(FileKind::Ts, source).expect("lower");

  let color = result
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Enum && result.names.resolve(def.name) == Some("Color"))
    .expect("enum definition");

  let members: Vec<_> = result
    .defs
    .iter()
    .filter(|def| def.path.kind == DefKind::EnumMember && def.parent == Some(color.id))
    .collect();
  assert_eq!(members.len(), 3);
  let mut member_names: Vec<_> = members
    .iter()
    .map(|def| result.names.resolve(def.name).unwrap())
    .collect();
  member_names.sort();
  let mut expected = vec!["Red", "Green", "Blue"];
  expected.sort();
  assert_eq!(member_names, expected);

  for member in members {
    let mapped = result
      .hir
      .span_map
      .def_at_offset(member.span.start)
      .expect("member in span map");
    assert_eq!(mapped, member.id);
    assert_eq!(member.parent, Some(color.id));
  }
}

#[test]
fn enum_member_ids_are_stable() {
  let base = lower_from_source_with_kind(FileKind::Ts, "enum Color { Red, Green, Blue }")
    .expect("base lowering");
  let variant = lower_from_source_with_kind(
    FileKind::Ts,
    "enum Shape { Red }\nenum Color { Red, Green, Blue }",
  )
  .expect("variant lowering");

  let color = base
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Enum && base.names.resolve(def.name) == Some("Color"))
    .expect("color enum");

  let member_paths: Vec<_> = base
    .defs
    .iter()
    .filter(|def| def.path.kind == DefKind::EnumMember && def.parent == Some(color.id))
    .map(|def| def.path)
    .collect();

  for path in member_paths {
    let base_id = base
      .hir
      .def_paths
      .get(&path)
      .copied()
      .expect("path in base def map");
    let variant_id = variant
      .hir
      .def_paths
      .get(&path)
      .copied()
      .expect("path in variant def map");
    assert_eq!(
      base_id,
      variant_id,
      "enum member id changed for {}",
      base.names.resolve(path.name).unwrap()
    );
  }
}

#[test]
fn nested_defs_use_scoped_paths() {
  let source = "namespace A { export const x = 1; }\nconst x = 2;";
  let ast = parse(source).expect("parse base");
  let (base, diagnostics) = lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let namespace = base
    .defs
    .iter()
    .find(|d| d.path.kind == DefKind::Namespace && base.names.resolve(d.name) == Some("A"))
    .expect("namespace A");
  let nested_x = base
    .defs
    .iter()
    .find(|d| {
      d.path.kind == DefKind::Var
        && base.names.resolve(d.name) == Some("x")
        && d.parent == Some(namespace.id)
    })
    .expect("nested x");
  let top_level_x = base
    .defs
    .iter()
    .find(|d| {
      d.path.kind == DefKind::Var && base.names.resolve(d.name) == Some("x") && d.parent.is_none()
    })
    .expect("top-level x");

  assert_ne!(nested_x.path, top_level_x.path);
  assert_eq!(nested_x.parent, Some(namespace.id));
  assert_eq!(top_level_x.parent, None);

  let variant_source = "const y = 0;\nnamespace A { export const x = 1; }\nconst x = 2;";
  let variant_ast = parse(variant_source).expect("parse variant");
  let variant = lower_file(FileId(0), FileKind::Ts, &variant_ast);

  let variant_namespace = variant
    .defs
    .iter()
    .find(|d| d.path.kind == DefKind::Namespace && variant.names.resolve(d.name) == Some("A"))
    .expect("variant namespace");
  let variant_nested_x = variant
    .defs
    .iter()
    .find(|d| {
      d.path.kind == DefKind::Var
        && variant.names.resolve(d.name) == Some("x")
        && d.parent == Some(variant_namespace.id)
    })
    .expect("variant nested x");
  let variant_top_x = variant
    .defs
    .iter()
    .find(|d| {
      d.path.kind == DefKind::Var
        && variant.names.resolve(d.name) == Some("x")
        && d.parent.is_none()
    })
    .expect("variant top-level x");

  assert_eq!(namespace.path, variant_namespace.path);
  assert_eq!(nested_x.path, variant_nested_x.path);
  assert_eq!(top_level_x.path, variant_top_x.path);
}

#[test]
fn nested_disambiguators_are_scoped() {
  let base_ast = parse("const x = 0;").expect("parse base");
  let base = lower_file(FileId(0), FileKind::Ts, &base_ast);

  let variant_source =
    "namespace A { export const x = 1; }\nnamespace A { export const x = 1; }\nconst x = 0;";
  let variant_ast = parse(variant_source).expect("parse variant");
  let variant = lower_file(FileId(0), FileKind::Ts, &variant_ast);

  let base_top_x = base
    .defs
    .iter()
    .find(|d| d.path.kind == DefKind::Var && base.names.resolve(d.name) == Some("x"))
    .expect("base top-level x");
  let variant_top_x = variant
    .defs
    .iter()
    .find(|d| {
      d.path.kind == DefKind::Var
        && variant.names.resolve(d.name) == Some("x")
        && d.parent.is_none()
    })
    .expect("variant top-level x");

  assert_eq!(base_top_x.path, variant_top_x.path);
  let base_top_id = base
    .hir
    .def_paths
    .get(&base_top_x.path)
    .copied()
    .expect("base id for top-level x");
  let variant_top_id = variant
    .hir
    .def_paths
    .get(&variant_top_x.path)
    .copied()
    .expect("variant id for top-level x");
  assert_eq!(base_top_id, variant_top_id);
  assert_eq!(base_top_x.path.disambiguator, 0);

  let namespaces: Vec<_> = variant
    .defs
    .iter()
    .filter(|d| d.path.kind == DefKind::Namespace && variant.names.resolve(d.name) == Some("A"))
    .collect();
  assert_eq!(namespaces.len(), 2);

  let nested_xs: Vec<_> = namespaces
    .iter()
    .map(|ns| {
      variant
        .defs
        .iter()
        .find(|d| {
          d.path.kind == DefKind::Var
            && variant.names.resolve(d.name) == Some("x")
            && d.parent == Some(ns.id)
        })
        .expect("namespace member x")
    })
    .collect();
  assert_eq!(nested_xs.len(), 2);
  let parent_ids: HashSet<_> = nested_xs.iter().map(|d| d.parent.unwrap()).collect();
  assert_eq!(parent_ids.len(), 2);
  assert!(nested_xs.iter().all(|d| d.path.disambiguator == 0));
  let nested_paths: HashSet<_> = nested_xs.iter().map(|d| d.path).collect();
  assert_eq!(nested_paths.len(), 2);
}

#[test]
fn nested_defs_are_parented_to_enclosing_function() {
  let source = r#"
    function outer(){ const a=1; function inner(){} const b=() => 1; }
    function other(){ const c=() => 2; }
  "#;
  let result = lower_from_source_with_kind(FileKind::Ts, source).expect("lower");

  let find_def = |kind: DefKind, name: &str| -> &hir_js::DefData {
    result
      .defs
      .iter()
      .find(|def| def.path.kind == kind && result.names.resolve(def.name) == Some(name))
      .unwrap_or_else(|| panic!("expected {name} {kind:?} definition"))
  };

  let outer = find_def(DefKind::Function, "outer");
  let other = find_def(DefKind::Function, "other");

  let a = find_def(DefKind::Var, "a");
  assert_eq!(a.parent, Some(outer.id), "a should be nested under outer");

  let inner = find_def(DefKind::Function, "inner");
  assert_eq!(
    inner.parent,
    Some(outer.id),
    "inner should be nested under outer"
  );

  let arrows: Vec<_> = result
    .defs
    .iter()
    .filter(|def| def.path.kind == DefKind::Function && result.names.resolve(def.name) == Some("<arrow>"))
    .collect();
  assert_eq!(arrows.len(), 2, "expected exactly two arrow function defs");

  let outer_arrow = arrows
    .iter()
    .find(|def| def.parent == Some(outer.id))
    .expect("expected arrow function def nested under outer");
  let other_arrow = arrows
    .iter()
    .find(|def| def.parent == Some(other.id))
    .expect("expected arrow function def nested under other");

  assert_eq!(
    outer_arrow.parent,
    Some(outer.id),
    "arrow in outer should be parented to outer"
  );
  assert_eq!(
    other_arrow.parent,
    Some(other.id),
    "arrow in other should be parented to other"
  );
}

#[test]
fn nested_def_ids_do_not_shift_across_unrelated_edits_in_other_functions() {
  let base_source = r#"
    function first(){ const a = () => 1; }
    function second(){ const b = () => 1; }
  "#;
  let variant_source = r#"
    function first(){ const a = () => 1; const extra = () => 2; }
    function second(){ const b = () => 1; }
  "#;

  let base = lower_from_source_with_kind(FileKind::Ts, base_source).expect("lower base");
  let variant = lower_from_source_with_kind(FileKind::Ts, variant_source).expect("lower variant");

  let base_second = base
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Function && base.names.resolve(def.name) == Some("second"))
    .expect("second function in base");
  let variant_second = variant
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function && variant.names.resolve(def.name) == Some("second")
    })
    .expect("second function in variant");
  assert_eq!(
    base_second.id, variant_second.id,
    "second function DefId should remain stable"
  );

  let base_arrow = base
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function
        && base.names.resolve(def.name) == Some("<arrow>")
        && def.parent == Some(base_second.id)
    })
    .expect("arrow in base second()");
  let variant_arrow = variant
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function
        && variant.names.resolve(def.name) == Some("<arrow>")
        && def.parent == Some(variant_second.id)
    })
    .expect("arrow in variant second()");

  assert_eq!(
    base_arrow.id, variant_arrow.id,
    "arrow DefId in second() should remain stable"
  );
  assert_eq!(
    base_arrow.body, variant_arrow.body,
    "arrow BodyId in second() should remain stable"
  );
  assert_eq!(
    base_arrow.path, variant_arrow.path,
    "arrow DefPath in second() should remain stable"
  );
}

#[test]
fn nested_def_ids_in_class_method_bodies_do_not_shift_across_unrelated_edits() {
  let base_source = r#"
    class C { m(){ const f = () => 1; } }
    class D { m(){ const g = () => 2; } }
  "#;
  let variant_source = r#"
    class C { m(){ const f = () => 1; const extra = () => 3; } }
    class D { m(){ const g = () => 2; } }
  "#;

  let base = lower_from_source_with_kind(FileKind::Ts, base_source).expect("lower base");
  let variant = lower_from_source_with_kind(FileKind::Ts, variant_source).expect("lower variant");

  let base_d = base
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Class && base.names.resolve(def.name) == Some("D"))
    .expect("class D in base");
  let variant_d = variant
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Class && variant.names.resolve(def.name) == Some("D"))
    .expect("class D in variant");
  assert_eq!(
    base_d.id, variant_d.id,
    "class D DefId should remain stable"
  );

  let base_method = base
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Method
        && base.names.resolve(def.name) == Some("m")
        && def.parent == Some(base_d.id)
    })
    .expect("D.m method def in base");
  let variant_method = variant
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Method
        && variant.names.resolve(def.name) == Some("m")
        && def.parent == Some(variant_d.id)
    })
    .expect("D.m method def in variant");
  assert_eq!(
    base_method.id, variant_method.id,
    "D.m DefId should remain stable"
  );

  let base_arrow = base
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function
        && base.names.resolve(def.name) == Some("<arrow>")
        && def.parent == Some(base_method.id)
    })
    .expect("arrow in base D.m()");
  let variant_arrow = variant
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function
        && variant.names.resolve(def.name) == Some("<arrow>")
        && def.parent == Some(variant_method.id)
    })
    .expect("arrow in variant D.m()");

  assert_eq!(
    base_arrow.id, variant_arrow.id,
    "arrow DefId in D.m() should remain stable"
  );
  assert_eq!(
    base_arrow.body, variant_arrow.body,
    "arrow BodyId in D.m() should remain stable"
  );
  assert_eq!(
    base_arrow.path, variant_arrow.path,
    "arrow DefPath in D.m() should remain stable"
  );
}

#[test]
fn lowering_is_deterministic_for_nested_defs() {
  let source = r#"
    namespace A {
      export const x = 1;
      export function f() {}
    }
    enum Color { Red, Green }
    const value = () => Color.Red;
  "#;

  let ast = parse(source).expect("parse");
  let (first, diagnostics) = lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let ast_again = parse(source).expect("parse again");
  let (second, diagnostics_again) =
    lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast_again);
  assert!(diagnostics_again.is_empty());

  assert_eq!(first.hir.def_paths, second.hir.def_paths);
  assert_eq!(first.defs.len(), second.defs.len());

  for (left, right) in first.defs.iter().zip(second.defs.iter()) {
    assert_eq!(left.id, right.id, "def id changed for {:?}", left.path);
    assert_eq!(left.path, right.path);
    assert_eq!(left.parent, right.parent);
    assert_eq!(left.body, right.body);
  }
}

#[test]
fn body_ids_are_stable_across_runs() {
  let source = "function keep() {}\nconst value = () => keep();";
  let ast = parse(source).expect("parse");
  let (first, diagnostics) = lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let ast_again = parse(source).expect("parse again");
  let (second, diagnostics_again) =
    lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast_again);
  assert!(diagnostics_again.is_empty());

  let first_map: BTreeMap<_, _> = first
    .defs
    .iter()
    .filter_map(|def| def.body.map(|body| (def.path, body)))
    .collect();
  let second_map: BTreeMap<_, _> = second
    .defs
    .iter()
    .filter_map(|def| def.body.map(|body| (def.path, body)))
    .collect();

  assert_eq!(first_map, second_map, "body mapping changed across runs");

  let first_set: BTreeSet<_> = first.hir.bodies.iter().copied().collect();
  let second_set: BTreeSet<_> = second.hir.bodies.iter().copied().collect();
  assert_eq!(first_set, second_set, "body ids changed across runs");
}

#[test]
fn expr_ids_are_stable_across_runs() {
  let source = "const value = (1 + 2) * 3;";
  let ast = parse(source).expect("parse");
  let first = lower_file(FileId(0), FileKind::Ts, &ast);

  let ast_again = parse(source).expect("parse again");
  let second = lower_file(FileId(0), FileKind::Ts, &ast_again);

  let body = first.root_body();
  assert_eq!(body, second.root_body(), "root body changed between runs");

  let first_body = first.body(body).expect("first body");
  let second_body = second.body(body).expect("second body");
  assert_eq!(
    first_body.exprs.len(),
    second_body.exprs.len(),
    "expression count changed across runs"
  );

  for (idx, expr) in first_body.exprs.iter().enumerate() {
    let id = ExprId(idx as u32);
    let other = &second_body.exprs[idx];
    assert_eq!(expr.span, other.span, "expr span changed for {:?}", id);
    let mapped = first
      .hir
      .span_map
      .expr_span_at_offset(expr.span.start)
      .expect("first span map entry");
    let mapped_again = second
      .hir
      .span_map
      .expr_span_at_offset(expr.span.start)
      .expect("second span map entry");
    assert_eq!(mapped, mapped_again, "span map entry changed for {:?}", id);
  }
}

#[test]
fn body_ids_survive_unrelated_insertions() {
  let base = "function keep() {}\nconst value = 1;";
  let with_extra = "function keep() {}\nconst inserted = 0;\nconst value = 1;";

  let base_ast = parse(base).expect("parse base");
  let base_result = lower_file(FileId(0), FileKind::Ts, &base_ast);

  let extra_ast = parse(with_extra).expect("parse variant");
  let extra_result = lower_file(FileId(0), FileKind::Ts, &extra_ast);

  for def in base_result.defs.iter().filter(|d| d.body.is_some()) {
    let base_body = def.body.expect("base body id present");
    let extra_def_id = extra_result
      .hir
      .def_paths
      .get(&def.path)
      .copied()
      .expect("path should exist after insertion");
    let extra_body = extra_result
      .def(extra_def_id)
      .and_then(|def| def.body)
      .expect("body should exist in variant");
    assert_eq!(
      base_body, extra_body,
      "body id changed for def path {:?}",
      def.path
    );
  }
}

#[test]
fn lowers_class_decl_as_decl_stmt() {
  let ast = parse("class C {}").expect("parse");
  let (result, diagnostics) = lower_file_with_diagnostics(FileId(7), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let body = result.body(result.root_body()).expect("root body");
  let def_id = body
    .stmts
    .iter()
    .find_map(|stmt| match stmt.kind {
      StmtKind::Decl(def) => Some(def),
      _ => None,
    })
    .expect("class declaration lowered as decl stmt");
  let def = result.def(def_id).expect("class def");
  assert_eq!(def.path.kind, DefKind::Class);
  let class_body = def.body.expect("class body id");
  let class_body_data = result.body(class_body).expect("class body");
  assert_eq!(class_body_data.kind, BodyKind::Class);
}

#[test]
fn lowers_class_expr() {
  let ast = parse("const x = class Named {}").expect("parse");
  let (result, diagnostics) = lower_file_with_diagnostics(FileId(8), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let body = result.body(result.root_body()).expect("root body");
  let (def_id, body_id, name) = body
    .exprs
    .iter()
    .find_map(|expr| match &expr.kind {
      ExprKind::ClassExpr { def, body, name } => Some((*def, *body, *name)),
      _ => None,
    })
    .expect("class expression present");

  let def = result.def(def_id).expect("class def");
  assert_eq!(def.path.kind, DefKind::Class);
  assert_eq!(def.body, Some(body_id));
  assert_ne!(body_id, BodyId(u32::MAX));
  assert!(result.body(body_id).is_some());
  assert_eq!(name.and_then(|n| result.names.resolve(n)), Some("Named"));
}

#[test]
fn export_default_class_has_ids() {
  let ast = parse("export default class {}").expect("parse");
  let (result, diagnostics) = lower_file_with_diagnostics(FileId(9), FileKind::Ts, &ast);
  assert!(diagnostics.is_empty());

  let export_value = result
    .hir
    .exports
    .iter()
    .find_map(|export| match &export.kind {
      ExportKind::Default(default) => Some(&default.value),
      _ => None,
    })
    .expect("default export present");

  let (def, body, name) = match export_value {
    ExportDefaultValue::Class { def, body, name } => (*def, *body, name),
    other => panic!("expected class default export, got {:?}", other),
  };

  let def_data = result.def(def).expect("class def");
  assert_eq!(def_data.path.kind, DefKind::Class);
  assert_eq!(def_data.body, Some(body));
  assert_ne!(body, BodyId(u32::MAX));
  let class_body = result.body(body).expect("class body");
  assert_eq!(class_body.kind, BodyKind::Class);
  assert!(name.is_none());
}

#[test]
fn class_member_defs_have_stable_ids() {
  let source = "class C { x = 1; static y = 2; method(a){ const inner = () => 1; } get z(){ return 1 } set z(v){} static { const s = 1 } constructor(){} }";
  let result = lower_from_source(source).expect("lower");

  let class_def = result
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Class && result.names.resolve(def.name) == Some("C"))
    .expect("class definition");
  let class_id = class_def.id;

  let find_def = |kind: DefKind, name: &str| -> &hir_js::DefData {
    result
      .defs
      .iter()
      .find(|def| def.path.kind == kind && result.names.resolve(def.name) == Some(name))
      .expect("definition present")
  };

  let field_x = find_def(DefKind::Field, "x");
  assert_eq!(field_x.parent, Some(class_id));
  let field_body = result
    .body(field_x.body.expect("field body"))
    .expect("body present");
  assert!(
    !field_body.root_stmts.is_empty(),
    "field initializer should produce statements"
  );

  let static_y = find_def(DefKind::Field, "y");
  assert_eq!(static_y.parent, Some(class_id));
  assert!(static_y.is_static, "static field should be marked static");
  let static_body = result
    .body(static_y.body.expect("static field body"))
    .expect("body present");
  assert!(
    !static_body.root_stmts.is_empty(),
    "static field initializer should produce statements"
  );

  let method = find_def(DefKind::Method, "method");
  assert_eq!(method.parent, Some(class_id));
  let method_body = result
    .body(method.body.expect("method body"))
    .expect("body present");
  assert!(
    !method_body.root_stmts.is_empty(),
    "method body should contain statements"
  );
  assert!(
    method_body
      .exprs
      .iter()
      .any(|expr| matches!(expr.kind, ExprKind::FunctionExpr { is_arrow: true, .. })),
    "arrow function in method should be lowered"
  );

  let z_members: Vec<_> = result
    .defs
    .iter()
    .filter(|def| def.path.kind == DefKind::Method && result.names.resolve(def.name) == Some("z"))
    .collect();
  assert_eq!(z_members.len(), 2, "expected getter and setter for z");
  for member in z_members {
    assert_eq!(member.parent, Some(class_id));
    assert!(member.body.is_some(), "accessor should have a body");
  }

  let static_block = find_def(DefKind::Method, "<static_block>");
  assert_eq!(static_block.parent, Some(class_id));
  assert!(static_block.is_static);
  let static_block_body = result
    .body(static_block.body.expect("static block body"))
    .expect("body present");
  assert!(
    !static_block_body.root_stmts.is_empty(),
    "static block should contain statements"
  );

  let constructor = find_def(DefKind::Constructor, "constructor");
  assert_eq!(constructor.parent, Some(class_id));
  assert!(constructor.body.is_some());
}

#[test]
fn class_member_ids_survive_unrelated_insertions() {
  let base = "class C { method() {} }\nclass D { method() {} }";
  let with_extra = "class C { method() {} }\nclass Extra { method() {} }\nclass D { method() {} }";

  let base = lower_from_source(base).expect("lower base");
  let variant = lower_from_source(with_extra).expect("lower variant");

  let base_member_paths: Vec<_> = base
    .hir
    .def_paths
    .iter()
    .filter(|(path, _)| path.parent.is_some())
    .map(|(path, id)| (*path, *id))
    .collect();

  for (path, def_id) in base_member_paths {
    let other = variant
      .hir
      .def_paths
      .get(&path)
      .copied()
      .expect("path should exist in variant");
    assert_eq!(def_id, other, "def id changed for path {:?}", path);

    if let Some(body) = base.def(def_id).and_then(|d| d.body) {
      let variant_body = variant
        .def(other)
        .and_then(|d| d.body)
        .expect("body in variant");
      assert_eq!(body, variant_body, "body id changed for path {:?}", path);
    }
  }
}

#[test]
fn span_map_indexes_class_members() {
  let source = "class C { x = 1; static { const s = 1; } method() { return 1; } }";
  let result = lower_from_source(source).expect("lower");
  let span_map = &result.hir.span_map;

  let find_def = |kind: DefKind, name: &str| -> &hir_js::DefData {
    result
      .defs
      .iter()
      .find(|def| def.path.kind == kind && result.names.resolve(def.name) == Some(name))
      .expect("definition present")
  };

  let field = find_def(DefKind::Field, "x");
  let field_span = span_map.def_span(field.id).expect("field span");
  assert_eq!(
    span_map.def_at_offset(field_span.start),
    Some(field.id),
    "field def should map to its span start"
  );

  let method = find_def(DefKind::Method, "method");
  let method_span = span_map.def_span(method.id).expect("method span");
  assert_eq!(
    span_map.def_at_offset(method_span.start),
    Some(method.id),
    "method def should map to its span start"
  );

  let static_block = find_def(DefKind::Method, "<static_block>");
  let static_span = span_map
    .def_span(static_block.id)
    .expect("static block span");
  assert_eq!(
    span_map.def_at_offset(static_span.start),
    Some(static_block.id),
    "static block def should map to its span start"
  );
}

#[test]
fn name_ids_stay_stable_when_unrelated_names_are_introduced() {
  let base = "function f() {}\nconst tail = 1;";
  let with_extra = "const earlier = 0;\nfunction f() {}\nconst tail = 1;";

  let base_ast = parse(base).expect("parse base");
  let base_result = lower_file(FileId(6), FileKind::Ts, &base_ast);

  let extra_ast = parse(with_extra).expect("parse variant");
  let extra_result = lower_file(FileId(6), FileKind::Ts, &extra_ast);

  let base_f = base_result
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function && base_result.names.resolve(def.name) == Some("f")
    })
    .expect("function f in base");
  let extra_f = extra_result
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Function && extra_result.names.resolve(def.name) == Some("f")
    })
    .expect("function f in variant");

  assert_eq!(base_f.name, extra_f.name, "NameId for f should be stable");
  assert_eq!(base_f.path, extra_f.path, "DefPath for f should be stable");
}

#[test]
fn module_decl_string_and_ident_have_distinct_def_ids() {
  let source = r#"
module Foo {}
declare module "Foo" {}
"#;
  let lowered = lower_from_source_with_kind(FileKind::Ts, source).expect("lower");

  // `module Foo {}` lowers as a namespace, while string-literal modules produce `DefKind::Module`.
  let module_like_defs: Vec<_> = lowered
    .defs
    .iter()
    .filter(|def| matches!(def.path.kind, DefKind::Module | DefKind::Namespace))
    .collect();
  assert_eq!(
    module_like_defs.len(),
    2,
    "expected module and namespace declarations"
  );

  let ambient_module = module_like_defs
    .iter()
    .find(|def| def.path.kind == DefKind::Module)
    .expect("ambient module present");
  assert_eq!(
    lowered.names.resolve(ambient_module.path.name),
    Some("\"Foo\""),
    "string-literal module names should remain quoted"
  );

  let name_texts: BTreeSet<_> = module_like_defs
    .iter()
    .map(|def| lowered.names.resolve(def.path.name).unwrap().to_string())
    .collect();
  assert_eq!(name_texts.len(), 2, "module names should not collide");
  assert!(
    name_texts.contains("Foo") && name_texts.contains("\"Foo\""),
    "module names should distinguish identifier and ambient string forms: {:?}",
    name_texts
  );

  let name_ids: BTreeSet<_> = module_like_defs.iter().map(|def| def.path.name).collect();
  assert_eq!(
    name_ids.len(),
    module_like_defs.len(),
    "module-like DefPaths should carry distinct names"
  );

  let def_ids: BTreeSet<_> = module_like_defs.iter().map(|def| def.id).collect();
  assert_eq!(
    def_ids.len(),
    module_like_defs.len(),
    "module-like DefIds should differ"
  );
}

#[test]
fn module_decl_string_name_is_stable() {
  let source = r#"declare module "Foo" {}"#;
  let first = lower_from_source_with_kind(FileKind::Ts, source).expect("lower first");
  let second = lower_from_source_with_kind(FileKind::Ts, source).expect("lower second");

  let first_module = first
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Module)
    .expect("ambient module present");
  let second_module = second
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Module)
    .expect("ambient module present");

  assert_eq!(
    first.names.resolve(first_module.path.name),
    Some("\"Foo\""),
    "string-literal module names are quoted to avoid namespace collisions"
  );
  assert_eq!(
    first_module.path.name, second_module.path.name,
    "NameId for string module should be stable across runs"
  );
  assert_eq!(
    first_module.id, second_module.id,
    "DefId for string module should be stable across runs"
  );
  assert_eq!(
    first_module.path, second_module.path,
    "DefPath for string module should be stable across runs"
  );
}

#[test]
fn expr_at_offset_prefers_inner_expression() {
  let source = "const a = 1 + 2;";
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(1), FileKind::Ts, &ast);

  let body_id = result.root_body();
  let body = result.body(body_id).expect("body");
  let map = &result.hir.span_map;

  let (binary_id, left_span) = body
    .exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      ExprKind::Binary { left, .. } => Some((ExprId(idx as u32), body.exprs[left.0 as usize].span)),
      _ => None,
    })
    .expect("binary expression present");

  let offset = left_span.start;
  let expected = result
    .hir
    .bodies
    .iter()
    .copied()
    .filter_map(|bid| {
      let body = result.body(bid)?;
      let mut best: Option<((u32, u32, u32, u32, u32), ExprId)> = None;
      for (idx, expr) in body.exprs.iter().enumerate() {
        if expr.span.is_empty() || offset < expr.span.start || offset > expr.span.end {
          continue;
        }
        let rank = (
          expr.span.len(),
          expr.span.start,
          bid.0,
          idx as u32,
          expr.span.end,
        );
        if best
          .as_ref()
          .map(|(current, _)| rank < *current)
          .unwrap_or(true)
        {
          best = Some((rank, ExprId(idx as u32)));
        }
      }
      if best.is_none() {
        for (idx, expr) in body.exprs.iter().enumerate() {
          if !expr.span.is_empty() || offset != expr.span.start {
            continue;
          }
          let rank = (
            expr.span.len(),
            expr.span.start,
            bid.0,
            idx as u32,
            expr.span.end,
          );
          if best
            .as_ref()
            .map(|(current, _)| rank < *current)
            .unwrap_or(true)
          {
            best = Some((rank, ExprId(idx as u32)));
          }
        }
      }
      best.map(|(_, expr_id)| (bid, expr_id))
    })
    .min_by_key(|(bid, expr_id)| {
      let body = result.body(*bid).expect("body");
      let span = body.exprs[expr_id.0 as usize].span;
      (span.len(), span.start, bid.0, expr_id.0, span.end)
    })
    .expect("expected candidate");

  let mapped = map.expr_at_offset(offset).expect("expr at offset");
  assert_eq!(mapped, expected);

  let binary_span = body.exprs[binary_id.0 as usize].span;
  let (mapped_body, mapped_binary) = map
    .expr_at_offset(binary_span.start)
    .expect("mapped binary expr");
  let mapped_body_data = result.body(mapped_body).expect("body");
  assert!(mapped_body_data.exprs[mapped_binary.0 as usize].span.len() <= binary_span.len());
}

#[test]
fn lowers_common_ts_constructs() {
  let source = r#"
interface Foo { bar: string }
type Alias = Foo;
enum Color { Red }
export namespace NS { const x = 1; }
"#;
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(2), FileKind::Ts, &ast);
  let kinds: Vec<_> = result.defs.iter().map(|d| d.path.kind).collect();

  assert!(kinds.contains(&DefKind::Interface));
  assert!(kinds.contains(&DefKind::TypeAlias));
  assert!(kinds.contains(&DefKind::Enum));
  assert!(kinds.contains(&DefKind::Namespace));
}

#[test]
fn marks_declare_global_ambient() {
  let source = r#"
declare global {
  interface Foo {
    bar: string;
  }
}
"#;
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(3), FileKind::Dts, &ast);

  assert_eq!(result.hir.file_kind, FileKind::Dts);
  let foo = result
    .defs
    .iter()
    .find(|d| result.names.resolve(d.path.name) == Some("Foo"))
    .expect("Foo interface present");
  assert!(foo.is_ambient, "global declarations should be ambient");
  assert!(foo.in_global, "declare global declarations are tracked");
}

#[test]
fn saturates_overflowing_spans() {
  let mut ast = parse("const x = 1;").expect("parse");
  let huge_start = u32::MAX as usize + 10;
  let huge_end = huge_start + 5;

  let stmt = ast.stx.body.first_mut().expect("stmt");
  stmt.loc = Loc(huge_start, huge_end);
  match &mut *stmt.stx {
    AstStmt::VarDecl(var_decl) => {
      var_decl.loc = Loc(huge_start, huge_end);
      if let Some(declarator) = var_decl.stx.declarators.first_mut() {
        declarator.pattern.loc = Loc(huge_start, huge_end);
        declarator.pattern.stx.pat.loc = Loc(huge_start, huge_end);
        if let Some(init) = declarator.initializer.as_mut() {
          init.loc = Loc(huge_start, huge_end);
        }
      }
    }
    other => panic!("expected var decl, got {:?}", other),
  }

  let (result, diagnostics) = lower_file_with_diagnostics(FileId(4), FileKind::Ts, &ast);
  assert!(
    diagnostics.iter().any(|d| d.code == "LOWER0001"),
    "expected overflow diagnostic",
  );

  let def = result.defs.first().expect("def");
  assert_eq!(def.span.start, u32::MAX);
  assert_eq!(def.span.end, u32::MAX);

  let body_id = result.root_body();
  let body = result.body(body_id).expect("body");
  let stmt_span = body.stmts.first().expect("stmt").span;
  assert_eq!(stmt_span.start, u32::MAX);
  assert_eq!(stmt_span.end, u32::MAX);

  let expr_span = body.exprs.first().expect("expr").span;
  assert_eq!(expr_span.start, u32::MAX);
  assert_eq!(expr_span.end, u32::MAX);
}

#[test]
fn lowers_computed_object_keys() {
  let ast = parse("const obj = { [foo]: 1, regular: 2, [bar()]: baz };").expect("parse");
  let (result, diagnostics) = lower_file_with_diagnostics(FileId(5), FileKind::Ts, &ast);

  assert!(diagnostics.is_empty());

  let _def = result
    .defs
    .iter()
    .find(|d| result.names.resolve(d.path.name) == Some("obj"))
    .expect("obj definition");
  let body = result.body(result.root_body()).expect("root body");
  let object_expr = body
    .exprs
    .iter()
    .find(|expr| matches!(expr.kind, ExprKind::Object(_)))
    .expect("object literal");

  if let ExprKind::Object(obj) = &object_expr.kind {
    let computed_keys: Vec<_> = obj
      .properties
      .iter()
      .filter_map(|prop| match prop {
        ObjectProperty::KeyValue {
          key: ObjectKey::Computed(expr),
          ..
        } => Some(*expr),
        _ => None,
      })
      .collect();
    assert_eq!(
      computed_keys.len(),
      2,
      "expected both computed keys to be lowered"
    );
  } else {
    panic!("expected object literal");
  }
}

#[test]
fn collects_nested_defs_in_object_literal_methods() {
  let source = "const obj = { m(){ const inner = () => class {}; return inner; } };";
  let ast = parse(source).expect("parse");
  let (result, diagnostics) = lower_file_with_diagnostics(FileId(10), FileKind::Ts, &ast);

  assert!(diagnostics.is_empty());

  let method_def = result
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::Method && result.names.resolve(def.path.name) == Some("m")
    })
    .expect("object literal method");

  let method_body_id = method_def.body.expect("method body id");
  let method_body = result.body(method_body_id).expect("method body");

  let (arrow_expr_id, arrow_body_id) = method_body
    .exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match &expr.kind {
      ExprKind::FunctionExpr {
        is_arrow: true,
        body,
        ..
      } => Some((ExprId(idx as u32), *body)),
      _ => None,
    })
    .expect("arrow function expression for inner binding");

  assert!(matches!(
    method_body.exprs[arrow_expr_id.0 as usize].kind,
    ExprKind::FunctionExpr { .. }
  ));

  let arrow_body = result.body(arrow_body_id).expect("arrow function body");
  let class_expr = arrow_body
    .exprs
    .iter()
    .find(|expr| matches!(expr.kind, ExprKind::ClassExpr { .. }))
    .expect("class expression inside arrow function");
  assert!(matches!(class_expr.kind, ExprKind::ClassExpr { .. }));
}

#[test]
fn computed_member_names_are_distinct_and_stable() {
  let base_source = "const obj = { [foo]() {}, [bar()]() {}, [foo]() {} };";
  let base = lower_from_source_with_kind(FileKind::Ts, base_source).expect("lower base");

  let base_methods = computed_methods(&base);
  let distinct_spans: BTreeSet<_> = base_methods.iter().map(|def| def.span).collect();
  assert_eq!(
    distinct_spans.len(),
    3,
    "expected three computed member spans"
  );

  let mut name_counts = BTreeMap::new();
  for def in &base_methods {
    *name_counts.entry(def.name).or_insert(0) += 1;
  }
  assert_eq!(
    name_counts.len(),
    2,
    "expected distinct names for foo and bar computed members"
  );
  assert!(
    name_counts.values().any(|count| *count == 2),
    "expected identical computed keys to share a synthetic name"
  );

  let with_extra_source = "const obj = { regular() {}, [foo]() {}, [bar()]() {}, [foo]() {} };";
  let with_extra =
    lower_from_source_with_kind(FileKind::Ts, with_extra_source).expect("lower variant");
  let with_extra_methods = computed_methods(&with_extra);
  let with_extra_spans: BTreeSet<_> = with_extra_methods.iter().map(|def| def.span).collect();
  assert_eq!(
    with_extra_spans.len(),
    3,
    "unrelated member should not change computed member count"
  );

  let base_paths: BTreeSet<_> = base_methods.iter().map(|def| def.path).collect();
  let extra_paths: BTreeSet<_> = with_extra_methods.iter().map(|def| def.path).collect();
  assert_eq!(
    base_paths, extra_paths,
    "computed member def paths should remain stable"
  );

  for def in &base_methods {
    let variant_id = with_extra
      .def_id_for_path(&def.path)
      .expect("computed path present after insertion");
    assert_eq!(
      variant_id,
      def.id,
      "computed member def id should remain stable for {:?}",
      base.names.resolve(def.path.name)
    );
  }
}

#[test]
fn lowers_imports_and_exports() {
  let source = r#"
    import defaultName, { foo as bar, type Baz } from "mod";
    import * as ns from "lib";
    import type { Qux } from "types";
    export { bar, type Baz } from "mod";
    export * as nsAll from "lib";
    export interface Api {}
    export type Alias = string;
    export enum Mode { On }
    export default function qux() {}
    export = defaultName;
  "#;
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(6), FileKind::Ts, &ast);

  let imports = &result.hir.imports;
  assert_eq!(imports.len(), 3);
  let names = &result.names;

  let first = match &imports[0].kind {
    ImportKind::Es(es) => es,
    _ => panic!("expected es import"),
  };
  assert_eq!(first.specifier.value, "mod");
  assert_eq!(
    names.resolve(first.default.as_ref().unwrap().local),
    Some("defaultName")
  );
  assert!(first
    .named
    .iter()
    .any(|n| names.resolve(n.local) == Some("bar")));
  assert!(first
    .named
    .iter()
    .any(|n| n.is_type_only && names.resolve(n.local) == Some("Baz")));

  let second = match &imports[1].kind {
    ImportKind::Es(es) => es,
    _ => panic!("expected namespace import"),
  };
  assert_eq!(
    names.resolve(second.namespace.as_ref().unwrap().local),
    Some("ns")
  );

  let third = match &imports[2].kind {
    ImportKind::Es(es) => es,
    _ => panic!("expected type-only import"),
  };
  assert!(third.is_type_only);
  assert!(third.named.iter().all(|n| n.is_type_only));

  let exports = &result.hir.exports;
  assert_eq!(exports.len(), 7);

  let reexport = exports
    .iter()
    .find_map(|e| match &e.kind {
      ExportKind::Named(named)
        if named.source.as_ref().map(|s| s.value.as_str()) == Some("mod") =>
      {
        Some(named)
      }
      _ => None,
    })
    .expect("re-export with source present");
  assert!(reexport
    .specifiers
    .iter()
    .any(|s| names.resolve(s.exported) == Some("bar")));
  assert!(reexport
    .specifiers
    .iter()
    .any(|s| s.is_type_only && names.resolve(s.exported) == Some("Baz")));

  let export_all = exports
    .iter()
    .find_map(|e| match &e.kind {
      ExportKind::ExportAll(all) => Some(all),
      _ => None,
    })
    .expect("export * as nsAll");
  assert_eq!(
    names.resolve(export_all.alias.as_ref().unwrap().exported),
    Some("nsAll")
  );

  let named_exports: Vec<_> = exports
    .iter()
    .filter_map(|e| match &e.kind {
      ExportKind::Named(named) if named.source.is_none() => Some(named),
      _ => None,
    })
    .collect();
  assert!(named_exports.iter().any(|named| named.is_type_only
    && named
      .specifiers
      .iter()
      .any(|s| names.resolve(s.exported) == Some("Api"))));
  assert!(named_exports.iter().any(|named| named.is_type_only
    && named
      .specifiers
      .iter()
      .any(|s| names.resolve(s.exported) == Some("Alias"))));
  assert!(named_exports.iter().any(|named| !named.is_type_only
    && named
      .specifiers
      .iter()
      .any(|s| names.resolve(s.exported) == Some("Mode"))));

  let default_export = exports
    .iter()
    .find_map(|e| match &e.kind {
      ExportKind::Default(default) => Some(default),
      _ => None,
    })
    .expect("default export present");
  assert!(matches!(
    default_export.value,
    ExportDefaultValue::Function { .. }
  ));

  assert!(
    exports
      .iter()
      .any(|e| matches!(e.kind, ExportKind::Assignment(_))),
    "export assignment should be captured"
  );
}

#[test]
fn nested_exports_do_not_create_file_exports() {
  let source = r#"export namespace NS { export const x = 1; export function f() {} }"#;
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(10), FileKind::Ts, &ast);

  assert_eq!(
    result.hir.exports.len(),
    1,
    "only the namespace itself should be a file-level export"
  );

  let exported_names: Vec<_> = result
    .hir
    .exports
    .iter()
    .flat_map(|export| match &export.kind {
      ExportKind::Named(named) => named
        .specifiers
        .iter()
        .map(|spec| result.names.resolve(spec.exported))
        .collect::<Vec<_>>(),
      _ => Vec::new(),
    })
    .collect();
  assert_eq!(
    exported_names,
    vec![Some("NS")],
    "nested exports should not be treated as file-level exports"
  );

  for name in ["x", "f"] {
    let def = result
      .defs
      .iter()
      .find(|def| result.names.resolve(def.path.name) == Some(name))
      .unwrap_or_else(|| panic!("expected {} definition", name));
    assert!(
      def.is_exported,
      "{name} should remain exported from its namespace"
    );
  }
}

#[test]
fn namespace_members_have_parent_and_export_flag() {
  let source = r#"export namespace NS { export const x = 1; export function f(){} namespace Inner { export interface I {} } }"#;
  let result = lower_from_source_with_kind(FileKind::Ts, source).expect("lower");

  let find_def = |kind: DefKind, name: &str| -> &hir_js::DefData {
    result
      .defs
      .iter()
      .find(|def| def.path.kind == kind && result.names.resolve(def.name) == Some(name))
      .unwrap_or_else(|| panic!("expected {name} {kind:?} definition"))
  };

  let ns = find_def(DefKind::Namespace, "NS");
  let x = find_def(DefKind::Var, "x");
  assert_eq!(x.parent, Some(ns.id), "x should belong to NS");
  assert!(x.is_exported, "x should be marked exported from NS");

  let f = find_def(DefKind::Function, "f");
  assert_eq!(f.parent, Some(ns.id), "f should belong to NS");
  assert!(f.is_exported, "f should be marked exported from NS");

  let inner = find_def(DefKind::Namespace, "Inner");
  assert_eq!(inner.parent, Some(ns.id), "Inner should belong to NS");
  assert!(
    inner.is_exported,
    "Inner should be treated as exported from NS for namespace membership"
  );

  let interface = find_def(DefKind::Interface, "I");
  assert_eq!(
    interface.parent,
    Some(inner.id),
    "I should belong to the Inner namespace"
  );
  assert!(
    interface.is_exported,
    "I should be marked exported from Inner namespace"
  );
}

#[test]
fn namespace_member_ids_stable_under_unrelated_edits() {
  let base = lower_from_source_with_kind(
    FileKind::Ts,
    r#"export namespace NS { export const x = 1; export function f(){} namespace Inner { export interface I {} } }"#,
  )
  .expect("lower base");

  let with_noise = lower_from_source_with_kind(
    FileKind::Ts,
    r#"
const noise = 0;
export namespace NS { export const x = 1; export function f(){} namespace Inner { export interface I {} } }
function extra() {}
"#,
  )
  .expect("lower variant");

  let targets = [
    (DefKind::Namespace, "NS"),
    (DefKind::Var, "x"),
    (DefKind::Function, "f"),
    (DefKind::Namespace, "Inner"),
    (DefKind::Interface, "I"),
  ];

  for (kind, name) in targets {
    let def = base
      .defs
      .iter()
      .find(|def| def.path.kind == kind && base.names.resolve(def.name) == Some(name))
      .unwrap_or_else(|| panic!("expected {name} {kind:?} definition"));
    let base_path = def.path;
    let variant_id = with_noise
      .hir
      .def_paths
      .get(&base_path)
      .copied()
      .unwrap_or_else(|| panic!("missing def path for {}", name));
    assert_eq!(
      variant_id, def.id,
      "DefId changed for {} after unrelated edits",
      name
    );
  }
}

#[test]
fn lowers_control_flow_statements() {
  let source = r#"
    function demo(items) {
      if (items.length) { return 1; } else { return 2; }
      for (let i = 0; i < items.length; i++) { continue; }
      do { break; } while (false);
      switch (items) { case 1: break; default: throw items; }
      try { items(); } catch (e) { throw e; } finally { items(); }
    }
  "#;
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(7), FileKind::Ts, &ast);

  let func = result
    .defs
    .iter()
    .find(|d| result.names.resolve(d.path.name) == Some("demo"))
    .expect("demo function");
  let body = result.body(func.body.unwrap()).expect("function body");
  let kinds: Vec<_> = body.stmts.iter().map(|s| &s.kind).collect();

  assert!(kinds.iter().any(|k| matches!(k, StmtKind::If { .. })));
  assert!(kinds.iter().any(|k| matches!(k, StmtKind::For { .. })));
  assert!(kinds.iter().any(|k| matches!(k, StmtKind::DoWhile { .. })));
  assert!(kinds.iter().any(|k| matches!(k, StmtKind::Switch { .. })));
  assert!(kinds.iter().any(|k| matches!(k, StmtKind::Try { .. })));
}

#[test]
fn parses_jsx_and_tsx_file_kinds() {
  let tsx = lower_from_source_with_kind(FileKind::Tsx, "const el = <div>{value}</div>;")
    .expect("tsx should parse");
  assert_eq!(tsx.hir.file_kind, FileKind::Tsx);
  let tsx_body = tsx.body(tsx.root_body()).expect("el body");
  assert!(tsx_body
    .exprs
    .iter()
    .any(|e| matches!(e.kind, ExprKind::Jsx(_))));

  let jsx =
    lower_from_source_with_kind(FileKind::Jsx, "const node = <span/>;").expect("jsx should parse");
  assert_eq!(jsx.hir.file_kind, FileKind::Jsx);
  let jsx_body = jsx.body(jsx.root_body()).expect("node body");
  assert!(jsx_body
    .exprs
    .iter()
    .any(|e| matches!(e.kind, ExprKind::Jsx(_))));
}

#[test]
fn lowers_new_expressions() {
  let ast = parse("const instance = new Foo(1);").expect("parse");
  let result = lower_file(FileId(8), FileKind::Ts, &ast);
  let _def = result
    .defs
    .iter()
    .find(|d| result.names.resolve(d.path.name) == Some("instance"))
    .expect("instance def");
  let body = result.body(result.root_body()).expect("root body");
  let call = body
    .exprs
    .iter()
    .find_map(|expr| match &expr.kind {
      ExprKind::Call(call) => Some(call),
      _ => None,
    })
    .expect("call expression");
  assert!(call.is_new);
  assert_eq!(call.args.len(), 1);
}

#[test]
fn lowers_type_assertion_type_annotation() {
  let result = lower_from_source_with_kind(
    FileKind::Ts,
    "const x = value as Foo; const y = value as const;",
  )
  .expect("lower");
  let body = result.body(result.root_body()).expect("root body");

  let mut assertions: Vec<_> = body
    .exprs
    .iter()
    .filter_map(|expr| match &expr.kind {
      ExprKind::TypeAssertion {
        const_assertion,
        type_annotation,
        ..
      } => Some((expr.span.start, *const_assertion, *type_annotation)),
      _ => None,
    })
    .collect();
  assertions.sort_by_key(|(start, _, _)| *start);
  assert_eq!(assertions.len(), 2);

  let (_, first_const, first_type) = assertions[0];
  assert!(!first_const);
  let first_type = first_type.expect("type annotation for `as Foo`");

  let arenas = result
    .type_arenas(body.owner)
    .expect("type arenas present for root body");
  let first_ty = &arenas.type_exprs[first_type.0 as usize];
  match &first_ty.kind {
    TypeExprKind::TypeRef(reference) => match &reference.name {
      TypeName::Ident(id) => assert_eq!(result.names.resolve(*id), Some("Foo")),
      other => panic!("expected Foo type ref, got {other:?}"),
    },
    other => panic!("expected type ref, got {other:?}"),
  }

  let mapped_span = result.hir.span_map.type_expr_span(body.owner, first_type);
  assert_eq!(mapped_span, Some(first_ty.span));

  let (_, second_const, second_type) = assertions[1];
  assert!(second_const);
  assert!(second_type.is_none());
}

#[test]
fn lowers_satisfies_type_annotation() {
  let result =
    lower_from_source_with_kind(FileKind::Ts, "const x = ({a:1} satisfies Foo);").expect("lower");
  let body = result.body(result.root_body()).expect("root body");

  let (type_expr, type_annotation) = body
    .exprs
    .iter()
    .find_map(|expr| match &expr.kind {
      ExprKind::Satisfies {
        expr,
        type_annotation,
      } => Some((*expr, *type_annotation)),
      _ => None,
    })
    .expect("satisfies expression");
  let _ = type_expr;

  let arenas = result
    .type_arenas(body.owner)
    .expect("type arenas present for root body");
  let ty = &arenas.type_exprs[type_annotation.0 as usize];
  match &ty.kind {
    TypeExprKind::TypeRef(reference) => match &reference.name {
      TypeName::Ident(id) => assert_eq!(result.names.resolve(*id), Some("Foo")),
      other => panic!("expected Foo type ref, got {other:?}"),
    },
    other => panic!("expected type ref, got {other:?}"),
  }
}

#[test]
fn type_expr_ids_are_scoped_to_enclosing_body_owner() {
  let result = lower_from_source_with_kind(
    FileKind::Ts,
    "function f() { value as Foo; ({a:1} satisfies Foo); value as const; }",
  )
  .expect("lower");

  let func_def = result
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Function && result.names.resolve(def.name) == Some("f"))
    .expect("function def");
  let body_id = func_def.body.expect("function body id");
  let body = result.body(body_id).expect("function body");
  assert_eq!(body.owner, func_def.id);

  let arenas = result
    .type_arenas(func_def.id)
    .expect("type arenas present for function body owner");

  let mut assertions: Vec<_> = body
    .exprs
    .iter()
    .filter_map(|expr| match &expr.kind {
      ExprKind::TypeAssertion {
        const_assertion,
        type_annotation,
        ..
      } => Some((expr.span.start, *const_assertion, *type_annotation)),
      _ => None,
    })
    .collect();
  assertions.sort_by_key(|(start, _, _)| *start);
  assert_eq!(assertions.len(), 2);

  let (_, first_const, first_type) = assertions[0];
  assert!(!first_const);
  let first_type = first_type.expect("type annotation for `as Foo`");
  let first_ty = &arenas.type_exprs[first_type.0 as usize];
  match &first_ty.kind {
    TypeExprKind::TypeRef(reference) => match &reference.name {
      TypeName::Ident(id) => assert_eq!(result.names.resolve(*id), Some("Foo")),
      other => panic!("expected Foo type ref, got {other:?}"),
    },
    other => panic!("expected type ref, got {other:?}"),
  }
  assert_eq!(
    result.hir.span_map.type_expr_at_offset(first_ty.span.start),
    Some((func_def.id, first_type))
  );

  let (_, second_const, second_type) = assertions[1];
  assert!(second_const);
  assert!(second_type.is_none());

  let satisfies = body
    .exprs
    .iter()
    .find_map(|expr| match &expr.kind {
      ExprKind::Satisfies {
        type_annotation, ..
      } => Some(*type_annotation),
      _ => None,
    })
    .expect("satisfies expression");

  let sat_ty = &arenas.type_exprs[satisfies.0 as usize];
  match &sat_ty.kind {
    TypeExprKind::TypeRef(reference) => match &reference.name {
      TypeName::Ident(id) => assert_eq!(result.names.resolve(*id), Some("Foo")),
      other => panic!("expected Foo type ref, got {other:?}"),
    },
    other => panic!("expected type ref, got {other:?}"),
  }
  assert_eq!(
    result.hir.span_map.type_expr_at_offset(sat_ty.span.start),
    Some((func_def.id, satisfies))
  );
}

#[test]
fn type_expr_ids_do_not_shift_across_unrelated_body_insertions() {
  let base = lower_from_source_with_kind(
    FileKind::Ts,
    "function f() { value as Foo; }\nfunction g() {}",
  )
  .expect("lower base");
  let variant = lower_from_source_with_kind(
    FileKind::Ts,
    "function g() {}\nconst inserted = 0;\nfunction f() { value as Foo; }",
  )
  .expect("lower variant");

  let base_f = base
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Function && base.names.resolve(def.name) == Some("f"))
    .expect("base f");
  let variant_f = variant
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Function && variant.names.resolve(def.name) == Some("f"))
    .expect("variant f");

  assert_eq!(base_f.id, variant_f.id);

  let base_body = base
    .body(base_f.body.expect("base f body"))
    .expect("base body");
  let variant_body = variant
    .body(variant_f.body.expect("variant f body"))
    .expect("variant body");

  let base_ty = base_body
    .exprs
    .iter()
    .find_map(|expr| match &expr.kind {
      ExprKind::TypeAssertion {
        type_annotation, ..
      } => *type_annotation,
      _ => None,
    })
    .expect("base type assertion");
  let variant_ty = variant_body
    .exprs
    .iter()
    .find_map(|expr| match &expr.kind {
      ExprKind::TypeAssertion {
        type_annotation, ..
      } => *type_annotation,
      _ => None,
    })
    .expect("variant type assertion");

  assert_eq!(base_ty, variant_ty);
}

proptest! {
  #[test]
  fn lowering_is_deterministic(sample in proptest::sample::select(vec![
    "const a = 1;",
    "function f(x) { return x * 2; }",
    "interface Foo { bar: string }\nnamespace NS { const x = 1; }",
  ])) {
    let ast1 = parse(sample).expect("parse");
    let ast2 = parse(sample).expect("parse");

    let res1 = lower_file(FileId(9), FileKind::Ts, &ast1);
    let res2 = lower_file(FileId(9), FileKind::Ts, &ast2);

    prop_assert_eq!(res1.defs, res2.defs);
    prop_assert_eq!(res1.hir, res2.hir);
    prop_assert_eq!(res1.bodies, res2.bodies);
  }
}
