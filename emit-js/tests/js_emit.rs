use emit_js::{emit_js_expr, emit_js_stmt, EmitOptions, Emitter};
use parse_js::ast::expr::lit::{LitNumExpr, LitRegexExpr};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{
  BinaryExpr, CallArg, CallExpr, ComputedMemberExpr, CondExpr, Expr, IdExpr, MemberExpr, UnaryExpr,
  UnaryPostfixExpr,
};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{
  BreakStmt, ExprStmt, ForBody, ForTripleStmt, ForTripleStmtInit, IfStmt, Stmt, WhileStmt,
};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;

fn node<T: derive_visitor::Drive + derive_visitor::DriveMut>(stx: T) -> Node<T> {
  Node::new(Loc(0, 0), stx)
}

fn emit_to_string(f: impl FnOnce(&mut Emitter)) -> String {
  let mut emitter = Emitter::new(EmitOptions::minified());
  f(&mut emitter);
  String::from_utf8(emitter.into_bytes()).expect("emitter output is UTF-8")
}

fn id_expr(name: &str) -> Node<Expr> {
  node(Expr::Id(node(IdExpr {
    name: name.to_string(),
  })))
}

fn lit_num_expr(value: f64) -> Node<Expr> {
  node(Expr::LitNum(node(LitNumExpr {
    value: JsNumber(value),
  })))
}

fn lit_regex_expr(value: &str) -> Node<Expr> {
  node(Expr::LitRegex(node(LitRegexExpr {
    value: value.to_string(),
  })))
}

fn call_expr(callee: Node<Expr>, args: Vec<Node<Expr>>) -> Node<Expr> {
  node(Expr::Call(node(CallExpr {
    optional_chaining: false,
    callee,
    arguments: args
      .into_iter()
      .map(|value| {
        node(CallArg {
          spread: false,
          value,
        })
      })
      .collect(),
  })))
}

fn member_expr(left: Node<Expr>, right: &str, optional_chaining: bool) -> Node<Expr> {
  node(Expr::Member(node(MemberExpr {
    optional_chaining,
    left,
    right: right.to_string(),
  })))
}

fn computed_member_expr(
  object: Node<Expr>,
  member: Node<Expr>,
  optional_chaining: bool,
) -> Node<Expr> {
  node(Expr::ComputedMember(node(ComputedMemberExpr {
    optional_chaining,
    object,
    member,
  })))
}

fn unary_expr(operator: OperatorName, argument: Node<Expr>) -> Node<Expr> {
  node(Expr::Unary(node(UnaryExpr { operator, argument })))
}

fn unary_postfix_expr(operator: OperatorName, argument: Node<Expr>) -> Node<Expr> {
  node(Expr::UnaryPostfix(node(UnaryPostfixExpr {
    operator,
    argument,
  })))
}

fn binary_expr(operator: OperatorName, left: Node<Expr>, right: Node<Expr>) -> Node<Expr> {
  node(Expr::Binary(node(BinaryExpr {
    operator,
    left,
    right,
  })))
}

fn cond_expr(test: Node<Expr>, consequent: Node<Expr>, alternate: Node<Expr>) -> Node<Expr> {
  node(Expr::Cond(node(CondExpr {
    test,
    consequent,
    alternate,
  })))
}

fn pat_id(name: &str) -> Node<PatDecl> {
  node(PatDecl {
    pat: node(Pat::Id(node(IdPat {
      name: name.to_string(),
    }))),
  })
}

fn expr_stmt(expr: Node<Expr>) -> Node<Stmt> {
  node(Stmt::Expr(node(ExprStmt { expr })))
}

fn assert_emit_expr(expr: Node<Expr>, expected: &str) {
  let actual = emit_to_string(|emitter| emit_js_expr(emitter, &expr).unwrap());
  assert_eq!(actual, expected);
}

fn assert_emit_stmt(stmt: Node<Stmt>, expected: &str) {
  let actual = emit_to_string(|emitter| emit_js_stmt(emitter, &stmt).unwrap());
  assert_eq!(actual, expected);
}

#[test]
fn emits_var_declarations() {
  let decl = node(Stmt::VarDecl(node(VarDecl {
    export: false,
    mode: VarDeclMode::Let,
    declarators: vec![VarDeclarator {
      pattern: pat_id("a"),
      definite_assignment: false,
      type_annotation: None,
      initializer: Some(lit_num_expr(1.0)),
    }],
  })));
  assert_emit_stmt(decl, "let a=1;");

  let decl = node(Stmt::VarDecl(node(VarDecl {
    export: false,
    mode: VarDeclMode::Const,
    declarators: vec![
      VarDeclarator {
        pattern: pat_id("a"),
        definite_assignment: false,
        type_annotation: None,
        initializer: Some(lit_num_expr(1.0)),
      },
      VarDeclarator {
        pattern: pat_id("b"),
        definite_assignment: false,
        type_annotation: None,
        initializer: Some(lit_num_expr(2.0)),
      },
    ],
  })));
  assert_emit_stmt(decl, "const a=1,b=2;");
}

#[test]
fn emits_if_else_wrapping_bodies_in_braces() {
  let stmt = node(Stmt::If(node(IfStmt {
    test: id_expr("a"),
    consequent: expr_stmt(call_expr(id_expr("b"), vec![])),
    alternate: Some(expr_stmt(call_expr(id_expr("c"), vec![]))),
  })));

  assert_emit_stmt(stmt, "if(a){b();}else{c();}");
}

#[test]
fn emits_while_with_break_body() {
  let stmt = node(Stmt::While(node(WhileStmt {
    condition: id_expr("a"),
    body: node(Stmt::Break(node(BreakStmt { label: None }))),
  })));

  assert_emit_stmt(stmt, "while(a){break;}");
}

#[test]
fn emits_for_triple_statement() {
  let stmt = node(Stmt::ForTriple(node(ForTripleStmt {
    init: ForTripleStmtInit::Decl(node(VarDecl {
      export: false,
      mode: VarDeclMode::Let,
      declarators: vec![VarDeclarator {
        pattern: pat_id("i"),
        definite_assignment: false,
        type_annotation: None,
        initializer: Some(lit_num_expr(0.0)),
      }],
    })),
    cond: Some(binary_expr(
      OperatorName::LessThan,
      id_expr("i"),
      lit_num_expr(10.0),
    )),
    post: Some(unary_postfix_expr(
      OperatorName::PostfixIncrement,
      id_expr("i"),
    )),
    body: node(ForBody {
      body: vec![expr_stmt(call_expr(id_expr("x"), vec![]))],
    }),
  })));

  assert_emit_stmt(stmt, "for(let i=0;i<10;i++){x();}");
}

#[test]
fn emits_optional_chaining() {
  assert_emit_expr(member_expr(id_expr("a"), "b", true), "a?.b");
  assert_emit_expr(
    computed_member_expr(id_expr("a"), id_expr("b"), true),
    "a?.[b]",
  );

  let optional_call = node(Expr::Call(node(CallExpr {
    optional_chaining: true,
    callee: id_expr("a"),
    arguments: vec![node(CallArg {
      spread: false,
      value: id_expr("b"),
    })],
  })));
  assert_emit_expr(optional_call, "a?.(b)");

  let optional_member_call = node(Expr::Call(node(CallExpr {
    optional_chaining: false,
    callee: member_expr(id_expr("a"), "b", true),
    arguments: vec![node(CallArg {
      spread: false,
      value: id_expr("c"),
    })],
  })));
  assert_emit_expr(optional_member_call, "a?.b(c)");
}

#[test]
fn disambiguates_adjacent_operators() {
  let expr = binary_expr(
    OperatorName::Addition,
    id_expr("a"),
    unary_expr(OperatorName::UnaryPlus, id_expr("b")),
  );
  assert_emit_expr(expr, "a+ +b");

  let expr = binary_expr(
    OperatorName::Subtraction,
    id_expr("a"),
    unary_expr(OperatorName::UnaryNegation, id_expr("b")),
  );
  assert_emit_expr(expr, "a- -b");
}

#[test]
fn conditional_expression_precedence() {
  let inner = cond_expr(id_expr("a"), id_expr("b"), id_expr("c"));
  let outer = cond_expr(inner, id_expr("d"), id_expr("e"));
  assert_emit_expr(outer, "(a?b:c)?d:e");

  let right_assoc = cond_expr(
    id_expr("a"),
    id_expr("b"),
    cond_expr(id_expr("c"), id_expr("d"), id_expr("e")),
  );
  assert_emit_expr(right_assoc, "a?b:c?d:e");
}

#[test]
fn exponentiation_and_unary_parentheses() {
  let expr = binary_expr(
    OperatorName::Exponentiation,
    unary_expr(OperatorName::UnaryNegation, id_expr("a")),
    id_expr("b"),
  );
  assert_emit_expr(expr, "(-a)**b");

  let expr = unary_expr(
    OperatorName::UnaryNegation,
    binary_expr(OperatorName::Exponentiation, id_expr("a"), id_expr("b")),
  );
  assert_emit_expr(expr, "-(a**b)");
}

#[test]
fn numeric_literal_member_access() {
  assert_emit_expr(
    member_expr(lit_num_expr(1.0), "toString", false),
    "1..toString",
  );
}

#[test]
fn emits_void_for_undefined_identifier() {
  assert_emit_expr(id_expr("undefined"), "void 0");
}

#[test]
fn division_followed_by_regex_literal_inserts_spacing() {
  let expr = binary_expr(OperatorName::Division, id_expr("a"), lit_regex_expr("/re/"));
  assert_emit_expr(expr, "a/ /re/");
}

#[test]
fn regex_literal_followed_by_division_inserts_spacing() {
  let expr = binary_expr(OperatorName::Division, lit_regex_expr("/re/"), id_expr("b"));
  assert_emit_expr(expr, "/re/ /b");
}
