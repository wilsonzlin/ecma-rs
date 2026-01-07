use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode, TsEraseOptions};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, ParseOptions, SourceType};

fn minify_ts_module_with_ts_erase_options(
  src: &str,
  ts_erase_options: TsEraseOptions,
) -> (String, Node<TopLevel>) {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(TopLevelMode::Module)
      .with_dialect(Dialect::Ts)
      .with_ts_erase_options(ts_erase_options),
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

fn find_exported_const_init<'a>(program: &'a Node<TopLevel>, name: &str) -> &'a Node<Expr> {
  for stmt in &program.stx.body {
    let Stmt::VarDecl(decl) = stmt.stx.as_ref() else {
      continue;
    };
    if !decl.stx.export || decl.stx.mode != VarDeclMode::Const {
      continue;
    }
    for declarator in &decl.stx.declarators {
      let Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() else {
        continue;
      };
      if id.stx.name != name {
        continue;
      }
      return declarator
        .initializer
        .as_ref()
        .expect("exported binding should have initializer");
    }
  }
  panic!("expected export const {name}=... in output");
}

fn has_runtime_iife(program: &Node<TopLevel>) -> bool {
  program.stx.body.iter().any(|stmt| {
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
    matches!(call.stx.callee.stx.as_ref(), Expr::Func(_))
  })
}

#[test]
fn const_enum_numeric_member_reference_is_inlined() {
  let src = r#"const enum E { A = 1, B = A } export const x = E.B;"#;
  let (_code, parsed) = minify_ts_module_with_ts_erase_options(src, TsEraseOptions::default());
  assert_eq!(
    parsed.stx.body.len(),
    1,
    "expected enum scaffolding to be erased"
  );
  let init = find_exported_const_init(&parsed, "x");
  match init.stx.as_ref() {
    Expr::LitNum(num) => assert_eq!(num.stx.value.0, 1.0),
    other => panic!("expected numeric literal initializer, got {other:?}"),
  }
}

#[test]
fn const_enum_bracket_access_is_inlined() {
  let src = r#"const enum E { A = 1 } export const x = E["A"];"#;
  let (_code, parsed) = minify_ts_module_with_ts_erase_options(src, TsEraseOptions::default());
  assert_eq!(
    parsed.stx.body.len(),
    1,
    "expected enum scaffolding to be erased"
  );
  let init = find_exported_const_init(&parsed, "x");
  match init.stx.as_ref() {
    Expr::LitNum(num) => assert_eq!(num.stx.value.0, 1.0),
    other => panic!("expected numeric literal initializer, got {other:?}"),
  }
}

#[test]
fn declare_const_enum_is_inlined() {
  let src = r#"declare const enum E { A = 1 } export const x = E.A;"#;
  let (_code, parsed) = minify_ts_module_with_ts_erase_options(src, TsEraseOptions::default());
  assert_eq!(
    parsed.stx.body.len(),
    1,
    "expected enum scaffolding to be erased"
  );
  let init = find_exported_const_init(&parsed, "x");
  match init.stx.as_ref() {
    Expr::LitNum(num) => assert_eq!(num.stx.value.0, 1.0),
    other => panic!("expected numeric literal initializer, got {other:?}"),
  }
}

#[test]
fn exported_const_enum_in_namespace_is_inlined() {
  let src = r#"
    export namespace N { export const enum E { A = 1 } }
    export const x = N.E.A;
  "#;
  let (code, parsed) = minify_ts_module_with_ts_erase_options(src, TsEraseOptions::default());
  let init = find_exported_const_init(&parsed, "x");
  match init.stx.as_ref() {
    Expr::LitNum(num) => assert_eq!(num.stx.value.0, 1.0),
    other => panic!("expected numeric literal initializer, got {other:?}"),
  }
  assert!(
    !code.contains(".E") && !code.contains("\"E\""),
    "expected `E` to be erased from the emitted namespace: {code}"
  );
}

#[test]
fn preserve_const_enums_option_keeps_runtime_lowering() {
  let src = r#"eval("x");const enum E{A=1,B=A}export const x=E.B;"#;
  let ts_erase_options = TsEraseOptions {
    preserve_const_enums: true,
    ..TsEraseOptions::default()
  };
  let (_code, parsed) = minify_ts_module_with_ts_erase_options(src, ts_erase_options);

  let has_enum_var = parsed.stx.body.iter().any(|stmt| match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) if decl.stx.mode == VarDeclMode::Var => decl.stx.declarators.iter().any(
      |declarator| matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == "E"),
    ),
    _ => false,
  });
  assert!(has_enum_var, "expected runtime enum `var E;` to be emitted");
  assert!(
    has_runtime_iife(&parsed),
    "expected enum IIFE to be emitted"
  );

  let init = find_exported_const_init(&parsed, "x");
  match init.stx.as_ref() {
    Expr::Member(member) => {
      assert_eq!(member.stx.right, "B");
      assert!(matches!(member.stx.left.stx.as_ref(), Expr::Id(id) if id.stx.name == "E"));
    }
    other => panic!("expected enum member access, got {other:?}"),
  }
}
