use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

#[test]
fn async_arrow_line_terminator_splits_statements() {
  let ast = parse_with_options("async\nx => x", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 2);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }

  match ast.stx.body[1].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::ArrowFunc(arrow) => {
        assert!(!arrow.stx.func.stx.async_);
        assert_eq!(arrow.stx.func.stx.parameters.len(), 1);
        let param = &arrow.stx.func.stx.parameters[0];
        match param.stx.pattern.stx.pat.stx.as_ref() {
          Pat::Id(id) => assert_eq!(id.stx.name, "x"),
          other => panic!("expected IdPat, got {other:?}"),
        }
      }
      other => panic!("expected arrow function, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }
}

#[test]
fn async_arrow_without_line_terminator_is_async() {
  let ast = parse_with_options("async x => x", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::ArrowFunc(arrow) => {
        assert!(arrow.stx.func.stx.async_);
        assert_eq!(arrow.stx.func.stx.parameters.len(), 1);
        let param = &arrow.stx.func.stx.parameters[0];
        match param.stx.pattern.stx.pat.stx.as_ref() {
          Pat::Id(id) => assert_eq!(id.stx.name, "x"),
          other => panic!("expected IdPat, got {other:?}"),
        }
      }
      other => panic!("expected arrow function, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }
}
