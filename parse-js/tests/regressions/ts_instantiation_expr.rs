use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::type_expr::TypeEntityName;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::operator::OperatorName;

fn first_stmt(source: &str) -> parse_js::ast::node::Node<Stmt> {
  let parsed = parse_js::parse(source).unwrap_or_else(|err| panic!("failed to parse: {err:?}"));
  parsed
    .stx
    .body
    .into_iter()
    .next()
    .expect("expected at least one statement")
}

#[test]
fn generic_call_callee_is_instantiation_expr() {
  let stmt = first_stmt("foo<T>(x);");
  let expr = match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
    other => panic!("expected expression statement, got {other:?}"),
  };

  let call = match expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression, got {other:?}"),
  };

  let inst = match call.stx.callee.stx.as_ref() {
    Expr::Instantiation(inst) => inst,
    other => panic!("expected instantiation callee, got {other:?}"),
  };
  assert_eq!(inst.stx.type_arguments.len(), 1);

  match inst.stx.expression.as_ref().stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
    other => panic!("expected instantiation expression to be identifier, got {other:?}"),
  }

  match inst.stx.type_arguments[0].stx.as_ref() {
    TypeExpr::TypeReference(type_ref) => match &type_ref.stx.name {
      TypeEntityName::Identifier(name) => assert_eq!(name, "T"),
      other => panic!("expected identifier type name, got {other:?}"),
    },
    other => panic!("expected type argument to be type reference, got {other:?}"),
  }
}

#[test]
fn new_expression_preserves_type_arguments() {
  let stmt = first_stmt("new Foo<T>();");
  let expr = match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
    other => panic!("expected expression statement, got {other:?}"),
  };

  let unary = match expr.stx.as_ref() {
    Expr::Unary(unary) => unary,
    other => panic!("expected unary expression, got {other:?}"),
  };
  assert_eq!(unary.stx.operator, OperatorName::New);

  let call = match unary.stx.argument.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression as new argument, got {other:?}"),
  };
  let inst = match call.stx.callee.stx.as_ref() {
    Expr::Instantiation(inst) => inst,
    other => panic!("expected instantiation callee, got {other:?}"),
  };
  assert_eq!(inst.stx.type_arguments.len(), 1);
}

#[test]
fn class_extends_preserves_type_arguments() {
  let stmt = first_stmt("class C extends Base<T> {}");
  let class = match stmt.stx.as_ref() {
    Stmt::ClassDecl(class) => class,
    other => panic!("expected class declaration, got {other:?}"),
  };
  let extends = class
    .stx
    .extends
    .as_ref()
    .expect("expected extends clause");
  match extends.stx.as_ref() {
    Expr::Instantiation(inst) => assert_eq!(inst.stx.type_arguments.len(), 1),
    other => panic!("expected instantiation in extends, got {other:?}"),
  }
}

#[test]
fn standalone_instantiation_expression_is_allowed() {
  let stmt = first_stmt("const f = foo<string>;");
  let decl = match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected var declaration, got {other:?}"),
  };
  let init = decl.stx.declarators[0]
    .initializer
    .as_ref()
    .expect("expected initializer");
  let inst = match init.stx.as_ref() {
    Expr::Instantiation(inst) => inst,
    other => panic!("expected instantiation initializer, got {other:?}"),
  };
  assert!(matches!(inst.stx.type_arguments[0].stx.as_ref(), TypeExpr::String(_)));
}

#[test]
fn tagged_template_preserves_type_arguments() {
  let stmt = first_stmt("foo<T>`tmpl`;");
  let expr = match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
    other => panic!("expected expression statement, got {other:?}"),
  };

  let tagged = match expr.stx.as_ref() {
    Expr::TaggedTemplate(tagged) => tagged,
    other => panic!("expected tagged template expression, got {other:?}"),
  };

  match tagged.stx.function.stx.as_ref() {
    Expr::Instantiation(inst) => assert_eq!(inst.stx.type_arguments.len(), 1),
    other => panic!("expected instantiation tag, got {other:?}"),
  }
}

