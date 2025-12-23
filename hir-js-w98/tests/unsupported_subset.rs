use hir_js_w98::lower::lower;
use hir_js_w98::lower::LowerError;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::stmt::Stmt;
use parse_js::loc::Loc;

type Program = parse_js::ast::node::Node<parse_js::ast::stx::TopLevel>;

fn expect_unsupported<F>(source: &str, expected_fragment: &str, expected_loc: F)
where
  F: Fn(&Program) -> Loc,
{
  let program = parse_js::parse(source).expect("parse should succeed");
  let loc = expected_loc(&program);
  match lower(program) {
    Ok(_) => panic!("expected lowering to fail for {source}"),
    Err(LowerError::Unsupported { loc: actual, what }) => {
      assert_eq!(actual, loc, "unexpected loc for {source}");
      assert!(
        what.contains(expected_fragment),
        "expected error to contain `{expected_fragment}`, got `{what}`",
      );
    }
  }
}

#[test]
fn null_literal_is_rejected() {
  expect_unsupported("null;", "literal null", |program| {
    match program.stx.body[0].stx.as_ref() {
      Stmt::Expr(expr) => expr.stx.expr.loc,
      other => panic!("unexpected stmt: {other:?}"),
    }
  });
}

#[test]
fn nullish_coalescing_is_rejected() {
  expect_unsupported("a ?? b;", "NullishCoalescing", |program| {
    match program.stx.body[0].stx.as_ref() {
      Stmt::Expr(expr) => expr.stx.expr.loc,
      other => panic!("unexpected stmt: {other:?}"),
    }
  });
}

#[test]
fn less_equal_is_rejected() {
  expect_unsupported("a <= b;", "LessThanOrEqual", |program| {
    match program.stx.body[0].stx.as_ref() {
      Stmt::Expr(expr) => expr.stx.expr.loc,
      other => panic!("unexpected stmt: {other:?}"),
    }
  });
}

#[test]
fn logical_not_is_rejected() {
  expect_unsupported("!a;", "LogicalNot", |program| {
    match program.stx.body[0].stx.as_ref() {
      Stmt::Expr(expr) => expr.stx.expr.loc,
      other => panic!("unexpected stmt: {other:?}"),
    }
  });
}

#[test]
fn using_declaration_is_rejected() {
  expect_unsupported("using x = y;", "using", |program| program.stx.body[0].loc);
}

#[test]
fn array_rest_destructuring_is_rejected() {
  expect_unsupported(
    "let [a, ...b] = xs;",
    "rest pattern",
    |program| match program.stx.body[0].stx.as_ref() {
      Stmt::VarDecl(decl) => match decl.stx.declarators[0].pattern.stx.pat.stx.as_ref() {
        Pat::Arr(arr) => arr.stx.rest.as_ref().expect("rest expected").loc,
        other => panic!("unexpected pattern: {other:?}"),
      },
      other => panic!("unexpected stmt: {other:?}"),
    },
  );
}

#[test]
fn object_rest_destructuring_is_rejected() {
  expect_unsupported(
    "({a, ...rest} = obj);",
    "rest pattern",
    |program| match program.stx.body[0].stx.as_ref() {
      Stmt::Expr(expr) => match expr.stx.expr.stx.as_ref() {
        parse_js::ast::expr::Expr::Binary(bin) => match bin.stx.left.stx.as_ref() {
          parse_js::ast::expr::Expr::ObjPat(obj) => {
            obj.stx.rest.as_ref().expect("rest expected").loc
          }
          other => panic!("unexpected lhs: {other:?}"),
        },
        other => panic!("unexpected expr: {other:?}"),
      },
      other => panic!("unexpected stmt: {other:?}"),
    },
  );
}
