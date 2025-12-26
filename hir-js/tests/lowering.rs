use diagnostics::FileId;
use hir_js::lower_file;
use hir_js::lower_file_with_diagnostics;
use hir_js::lower_from_source_with_kind;
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
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::loc::Loc;
use parse_js::parse;
use proptest::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

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
fn expr_at_offset_prefers_inner_expression() {
  let source = "const a = 1 + 2;";
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(1), FileKind::Ts, &ast);

  let def = result
    .defs
    .iter()
    .find(|d| d.path.kind == DefKind::Var)
    .expect("var def");
  let body_id = def.body.expect("var has initializer body");
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
  let expected = body
    .exprs
    .iter()
    .enumerate()
    .filter(|(_, expr)| expr.span.contains(offset))
    .min_by_key(|(idx, expr)| (expr.span.len(), expr.span.start, *idx))
    .map(|(idx, _)| ExprId(idx as u32))
    .unwrap();

  let mapped = map.expr_at_offset(offset).expect("expr at offset");
  assert_eq!(mapped, expected);

  let binary_span = body.exprs[binary_id.0 as usize].span;
  let mapped_binary = map
    .expr_at_offset(binary_span.start)
    .expect("mapped binary expr");
  assert!(body.exprs[mapped_binary.0 as usize].span.len() <= binary_span.len());
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

  let body_id = def.body.expect("initializer");
  let body = result.body(body_id).expect("initializer body");
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

  let def = result
    .defs
    .iter()
    .find(|d| result.names.resolve(d.path.name) == Some("obj"))
    .expect("obj definition");
  let body = result.body(def.body.unwrap()).expect("initializer body");
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
  let tsx_body = tsx
    .defs
    .iter()
    .find(|d| tsx.names.resolve(d.path.name) == Some("el"))
    .and_then(|def| def.body)
    .and_then(|body_id| tsx.body(body_id))
    .expect("el body");
  assert!(tsx_body
    .exprs
    .iter()
    .any(|e| matches!(e.kind, ExprKind::Jsx(_))));

  let jsx =
    lower_from_source_with_kind(FileKind::Jsx, "const node = <span/>;").expect("jsx should parse");
  assert_eq!(jsx.hir.file_kind, FileKind::Jsx);
  let jsx_body = jsx
    .defs
    .iter()
    .find(|d| jsx.names.resolve(d.path.name) == Some("node"))
    .and_then(|def| def.body)
    .and_then(|body_id| jsx.body(body_id))
    .expect("node body");
  assert!(jsx_body
    .exprs
    .iter()
    .any(|e| matches!(e.kind, ExprKind::Jsx(_))));
}

#[test]
fn lowers_new_expressions() {
  let ast = parse("const instance = new Foo(1);").expect("parse");
  let result = lower_file(FileId(8), FileKind::Ts, &ast);
  let def = result
    .defs
    .iter()
    .find(|d| result.names.resolve(d.path.name) == Some("instance"))
    .expect("instance def");
  let body = result.body(def.body.unwrap()).expect("initializer body");
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
