use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::{Expr, IdExpr};
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
