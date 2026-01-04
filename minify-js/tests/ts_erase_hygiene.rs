use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::{Expr, IdExpr};
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, ParseOptions, SourceType};

fn minify_ts_module(src: &str) -> (String, Node<TopLevel>) {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(TopLevelMode::Module).with_dialect(Dialect::Ts),
    src,
    &mut out,
  )
  .expect("minify should succeed");
  let code = String::from_utf8(out).expect("minifier output must be UTF-8");
  let parsed = parse_with_options(
    &code,
    ParseOptions {
      dialect: Dialect::Js,
      source_type: SourceType::Module,
    },
  )
  .expect("output should parse as JavaScript");
  (code, parsed)
}

fn has_top_level_var_binding(program: &Node<TopLevel>, name: &str) -> bool {
  program.stx.body.iter().any(|stmt| match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl.stx.declarators.iter().any(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == name)
    }),
    _ => false,
  })
}

fn count_top_level_var_bindings(program: &Node<TopLevel>, name: &str) -> usize {
  program
    .stx
    .body
    .iter()
    .filter_map(|stmt| match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => Some(decl),
      _ => None,
    })
    .flat_map(|decl| decl.stx.declarators.iter())
    .filter(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == name)
    })
    .count()
}

fn find_exported_local_binding(program: &Node<TopLevel>, exported: &str) -> Option<String> {
  for stmt in &program.stx.body {
    let Stmt::ExportList(export_list) = stmt.stx.as_ref() else {
      continue;
    };
    let ExportNames::Specific(entries) = &export_list.stx.names else {
      continue;
    };
    for entry in entries {
      if entry.stx.type_only {
        continue;
      }
      if entry.stx.alias.stx.name != exported {
        continue;
      }
      let parse_js::ast::import_export::ModuleExportImportName::Ident(local) =
        &entry.stx.exportable
      else {
        continue;
      };
      return Some(local.clone());
    }
  }
  None
}

fn find_iife_body_by_outer_name<'a>(
  program: &'a Node<TopLevel>,
  outer_name: &str,
) -> Option<&'a Vec<Node<Stmt>>> {
  for stmt in &program.stx.body {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      continue;
    };
    let Expr::Binary(comma) = expr_stmt.stx.expr.stx.as_ref() else {
      continue;
    };
    if comma.stx.operator != OperatorName::Comma {
      continue;
    }
    let Expr::Call(call) = comma.stx.right.stx.as_ref() else {
      continue;
    };
    if call.stx.arguments.len() != 1 {
      continue;
    }
    let arg = &call.stx.arguments[0].stx.value;
    let Expr::Binary(or) = arg.stx.as_ref() else {
      continue;
    };
    if or.stx.operator != OperatorName::LogicalOr {
      continue;
    }
    match or.stx.left.stx.as_ref() {
      Expr::Id(id) if id.stx.name == outer_name => {}
      _ => continue,
    }
    let Expr::Func(func_expr) = call.stx.callee.stx.as_ref() else {
      continue;
    };
    let func = &func_expr.stx.func.stx;
    let Some(parse_js::ast::func::FuncBody::Block(body)) = func.body.as_ref() else {
      continue;
    };
    return Some(body);
  }
  None
}

fn count_iifes_by_outer_name(program: &Node<TopLevel>, outer_name: &str) -> usize {
  program
    .stx
    .body
    .iter()
    .filter(|stmt| {
      let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
        return false;
      };
      let Expr::Binary(comma) = expr_stmt.stx.expr.stx.as_ref() else {
        return false;
      };
      if comma.stx.operator != OperatorName::Comma {
        return false;
      }
      let Expr::Call(call) = comma.stx.right.stx.as_ref() else {
        return false;
      };
      if call.stx.arguments.len() != 1 {
        return false;
      }
      let arg = &call.stx.arguments[0].stx.value;
      let Expr::Binary(or) = arg.stx.as_ref() else {
        return false;
      };
      if or.stx.operator != OperatorName::LogicalOr {
        return false;
      }
      matches!(or.stx.left.stx.as_ref(), Expr::Id(id) if id.stx.name == outer_name)
    })
    .count()
}

fn program_contains_id_expr(program: &mut Node<TopLevel>, target: &str) -> bool {
  use derive_visitor::{DriveMut, VisitorMut};
  type IdExprNode = Node<IdExpr>;

  #[derive(VisitorMut)]
  #[visitor(IdExprNode(enter))]
  struct FindIdExpr<'a> {
    target: &'a str,
    found: bool,
  }

  impl FindIdExpr<'_> {
    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      if node.stx.name == self.target {
        self.found = true;
      }
    }
  }

  let mut visitor = FindIdExpr {
    target,
    found: false,
  };
  program.drive_mut(&mut visitor);
  visitor.found
}

#[test]
fn avoids_synthetic_namespace_param_collisions_with_free_identifier_references() {
  let src = r#"
    export namespace static {
      eval("x");
      export const value = __minify_ts_namespace_static;
    }
  "#;
  let (code, mut parsed) = minify_ts_module(src);

  assert!(
    !code.contains("function(__minify_ts_namespace_static)"),
    "expected TS erasure to avoid shadowing the free identifier reference `__minify_ts_namespace_static`: {code}"
  );
  assert!(
    code.contains("function(__minify_ts_namespace_static_"),
    "expected TS erasure to disambiguate the synthesized namespace param with a suffix: {code}"
  );
  assert!(
    program_contains_id_expr(&mut parsed, "__minify_ts_namespace_static"),
    "expected the `__minify_ts_namespace_static` identifier reference to remain in output: {code}"
  );
}

#[test]
fn avoids_synthetic_enum_object_collisions_with_top_level_bindings() {
  let src = r#"
    eval("x");
    var __minify_ts_enum_obj_static = 1;
    export enum static { A = 1, B }
  "#;
  let (code, parsed) = minify_ts_module(src);

  assert!(
    has_top_level_var_binding(&parsed, "__minify_ts_enum_obj_static"),
    "expected user binding `__minify_ts_enum_obj_static` to remain in output: {code}"
  );
  assert!(
    !code.contains("(__minify_ts_enum_obj_static||"),
    "expected TS erasure to avoid reusing the user binding for the enum object: {code}"
  );
  assert!(
    code.contains("(__minify_ts_enum_obj_static_"),
    "expected TS erasure to disambiguate the enum object identifier with a suffix: {code}"
  );
}

#[test]
fn avoids_synthetic_enum_alias_collisions_with_identifier_references() {
  // Force enum alias generation by shadowing the enum object identifier inside a member
  // initializer. Also reference the previous synthetic alias name so TS erasure must pick a fresh
  // alternative and avoid shadowing a global lookup.
  let src = r#"
    export enum E {
      A = (eval("x"), 1),
      B = (function(E) { return A + __minify_ts_enum_E; })(0),
    }
  "#;
  let (code, mut parsed) = minify_ts_module(src);

  let body = find_iife_body_by_outer_name(&parsed, "E").expect("expected E enum IIFE");
  let alias_name = body
    .iter()
    .find_map(|stmt| match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => decl.stx.declarators.iter().find_map(|declarator| {
        let Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() else {
          return None;
        };
        Some(id.stx.name.clone())
      }),
      _ => None,
    })
    .expect("expected enum alias var declaration");

  assert_ne!(
    alias_name, "__minify_ts_enum_E",
    "expected enum alias name to be disambiguated to avoid colliding with user identifier references. output: {code}"
  );
  assert!(
    alias_name.starts_with("__minify_ts_enum_E_"),
    "expected enum alias to use the __minify_ts_enum_E base name with a suffix, got `{alias_name}`. output: {code}"
  );

  assert!(
    program_contains_id_expr(&mut parsed, "__minify_ts_enum_E"),
    "expected the `__minify_ts_enum_E` identifier reference to remain in output: {code}"
  );
}

#[test]
fn preserves_merging_of_invalid_top_level_runtime_namespaces() {
  let src = r#"
    eval("x");
    export namespace static { export const a = 1; }
    export namespace static { export const b = 2; }
  "#;
  let (code, parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime namespace");
  assert!(
    local.starts_with("__minify_ts_namespace_static"),
    "expected a synthesized local binding for `namespace static`, got `{local}`. output: {code}"
  );
  assert_eq!(
    count_top_level_var_bindings(&parsed, &local),
    1,
    "expected a single top-level var binding for the merged runtime namespace. output: {code}"
  );
  assert_eq!(
    count_iifes_by_outer_name(&parsed, &local),
    2,
    "expected two IIFEs targeting the same merged runtime namespace binding. output: {code}"
  );
}

#[test]
fn preserves_merging_of_invalid_top_level_runtime_enums() {
  let src = r#"
    eval("x");
    export enum static { A = 1 }
    export enum static { B }
  "#;
  let (code, parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime enum");
  assert!(
    local.starts_with("__minify_ts_enum_obj_static"),
    "expected a synthesized local binding for `enum static`, got `{local}`. output: {code}"
  );
  assert_eq!(
    count_top_level_var_bindings(&parsed, &local),
    1,
    "expected a single top-level var binding for the merged runtime enum. output: {code}"
  );
  assert_eq!(
    count_iifes_by_outer_name(&parsed, &local),
    2,
    "expected two IIFEs targeting the same merged runtime enum binding. output: {code}"
  );
}

#[test]
fn avoids_synthetic_namespace_param_collisions_with_function_decls() {
  let src = r#"
    eval("x");
    function __minify_ts_namespace_static() {}
    export namespace static { export const x = 1; }
  "#;
  let (code, parsed) = minify_ts_module(src);

  // The namespace binding is synthesized, so it must not accidentally reuse an existing user
  // function binding with the same name.
  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime namespace");
  assert_ne!(
    local, "__minify_ts_namespace_static",
    "expected TS erasure to avoid reusing the user function binding for the runtime namespace. output: {code}"
  );
  assert!(
    local.starts_with("__minify_ts_namespace_static_"),
    "expected TS erasure to disambiguate the synthesized namespace binding with a suffix, got `{local}`. output: {code}"
  );
  assert!(
    code.contains("function __minify_ts_namespace_static"),
    "expected user function decl to remain in output (eval disables DCE/renaming): {code}"
  );
  assert_eq!(
    count_top_level_var_bindings(&parsed, &local),
    1,
    "expected a single synthesized var binding for the runtime namespace. output: {code}"
  );
  assert_eq!(
    count_iifes_by_outer_name(&parsed, &local),
    1,
    "expected one namespace IIFE targeting the synthesized binding. output: {code}"
  );
}

#[test]
fn avoids_synthetic_namespace_param_collisions_with_import_equals_entity_name_base() {
  let src = r#"
    eval("x");
    import Foo = __minify_ts_namespace_static.Bar;
    export namespace static { export const x = 1; }
    console.log(Foo, x);
  "#;
  let (code, mut parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime namespace");
  assert_ne!(
    local, "__minify_ts_namespace_static",
    "expected TS erasure to avoid using a name that appears as the base of an import= entity name. output: {code}"
  );
  assert!(
    program_contains_id_expr(&mut parsed, "__minify_ts_namespace_static"),
    "expected the import= initializer to continue referring to `__minify_ts_namespace_static`. output: {code}"
  );
}

#[test]
fn avoids_synthetic_namespace_binding_collisions_with_ambient_var_decls() {
  let src = r#"
    eval("x");
    declare var __minify_ts_namespace_static: any;
    export namespace static { export const x = 1; }
  "#;
  let (code, parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime namespace");
  assert_ne!(
    local, "__minify_ts_namespace_static",
    "expected TS erasure to avoid colliding with ambient globals declared in the input. output: {code}"
  );
}

#[test]
fn avoids_synthetic_enum_object_collisions_with_free_identifier_references() {
  let src = r#"
    eval("x");
    export enum static { A = __minify_ts_enum_obj_static, B }
  "#;
  let (code, mut parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime enum");
  assert_ne!(
    local, "__minify_ts_enum_obj_static",
    "expected TS erasure to avoid shadowing free identifier references that match the enum object binding. output: {code}"
  );
  assert!(
    local.starts_with("__minify_ts_enum_obj_static_"),
    "expected TS erasure to disambiguate the enum object binding with a suffix, got `{local}`. output: {code}"
  );
  assert!(
    program_contains_id_expr(&mut parsed, "__minify_ts_enum_obj_static"),
    "expected the `__minify_ts_enum_obj_static` identifier reference to remain in output: {code}"
  );
}

#[test]
fn avoids_synthetic_namespace_binding_collisions_with_top_level_bindings() {
  let src = r#"
    eval("x");
    var __minify_ts_namespace_static = 1;
    export namespace static { export const x = 1; }
  "#;
  let (code, parsed) = minify_ts_module(src);

  assert!(
    has_top_level_var_binding(&parsed, "__minify_ts_namespace_static"),
    "expected user binding `__minify_ts_namespace_static` to remain in output: {code}"
  );

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime namespace");
  assert_ne!(
    local, "__minify_ts_namespace_static",
    "expected TS erasure to avoid reusing the user binding for the runtime namespace. output: {code}"
  );
  assert!(
    local.starts_with("__minify_ts_namespace_static_"),
    "expected TS erasure to disambiguate the synthesized namespace binding with a suffix, got `{local}`. output: {code}"
  );
  assert_eq!(
    count_iifes_by_outer_name(&parsed, "__minify_ts_namespace_static"),
    0,
    "expected the runtime namespace IIFE not to target the user binding. output: {code}"
  );
  assert_eq!(
    count_iifes_by_outer_name(&parsed, &local),
    1,
    "expected one runtime namespace IIFE targeting the synthesized binding. output: {code}"
  );
  assert_eq!(
    count_top_level_var_bindings(&parsed, "__minify_ts_namespace_static"),
    1,
    "expected the user var binding not to be redeclared. output: {code}"
  );
}

#[test]
fn avoids_synthetic_namespace_binding_collisions_with_top_level_identifier_references() {
  let src = r#"
    eval("x");
    export namespace static { export const x = 1; }
    console.log(__minify_ts_namespace_static);
  "#;
  let (code, mut parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime namespace");
  assert_ne!(
    local, "__minify_ts_namespace_static",
    "expected TS erasure to avoid shadowing top-level identifier references. output: {code}"
  );
  assert!(
    program_contains_id_expr(&mut parsed, "__minify_ts_namespace_static"),
    "expected the `__minify_ts_namespace_static` identifier reference to remain in output: {code}"
  );
}

#[test]
fn avoids_synthetic_enum_alias_collisions_with_top_level_bindings() {
  // Force enum alias generation by shadowing the enum object identifier inside a member
  // initializer, while also declaring a top-level binding with the old synthetic alias name.
  let src = r#"
    eval("x");
    var __minify_ts_enum_E = 123;
    export enum E {
      A = (eval("x"), 1),
      B = ((E) => A)(0),
    }
  "#;
  let (code, parsed) = minify_ts_module(src);

  assert!(
    has_top_level_var_binding(&parsed, "__minify_ts_enum_E"),
    "expected user binding `__minify_ts_enum_E` to remain in output: {code}"
  );

  let body = find_iife_body_by_outer_name(&parsed, "E").expect("expected E enum IIFE");
  let alias_name = body
    .iter()
    .find_map(|stmt| match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => decl.stx.declarators.iter().find_map(|declarator| {
        let Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() else {
          return None;
        };
        Some(id.stx.name.clone())
      }),
      _ => None,
    })
    .expect("expected enum alias var declaration");

  assert_ne!(
    alias_name, "__minify_ts_enum_E",
    "expected enum alias name to avoid colliding with user bindings. output: {code}"
  );
  assert!(
    alias_name.starts_with("__minify_ts_enum_E_"),
    "expected enum alias to use the __minify_ts_enum_E base name with a suffix, got `{alias_name}`. output: {code}"
  );
}

#[test]
fn avoids_synthetic_enum_object_collisions_with_top_level_identifier_references() {
  let src = r#"
    eval("x");
    export enum static { A = 1, B }
    console.log(__minify_ts_enum_obj_static);
  "#;
  let (code, mut parsed) = minify_ts_module(src);

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for runtime enum");
  assert_ne!(
    local, "__minify_ts_enum_obj_static",
    "expected TS erasure to avoid shadowing top-level identifier references. output: {code}"
  );
  assert!(
    program_contains_id_expr(&mut parsed, "__minify_ts_enum_obj_static"),
    "expected the `__minify_ts_enum_obj_static` identifier reference to remain in output: {code}"
  );
}
