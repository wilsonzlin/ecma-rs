use emit_js::{emit_js_top_level, EmitMode, EmitOptions, Emitter};
use parse_js::ast::expr::lit::LitNumExpr;
use parse_js::ast::expr::BinaryExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{
  BreakStmt, EmptyStmt, ExprStmt, ForBody, ForTripleStmt, ForTripleStmtInit, IfStmt, Stmt, WhileStmt,
};
use parse_js::ast::stx::TopLevel;
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use derive_visitor::{Drive, DriveMut};

fn node<T: Drive + DriveMut>(stx: T) -> Node<T> {
  Node::new(Loc(0, 0), stx)
}

fn stmt(stx: Stmt) -> Node<Stmt> {
  node(stx)
}

fn id(name: &str) -> Node<Expr> {
  node(Expr::Id(node(IdExpr {
    name: name.to_string(),
  })))
}

fn lit_num(value: f64) -> Node<Expr> {
  node(Expr::LitNum(node(LitNumExpr {
    value: JsNumber(value),
  })))
}

fn binary(left: Node<Expr>, operator: OperatorName, right: Node<Expr>) -> Node<Expr> {
  node(Expr::Binary(node(BinaryExpr {
    operator,
    left,
    right,
  })))
}

fn assign(left: Node<Expr>, right: Node<Expr>) -> Node<Expr> {
  binary(left, OperatorName::Assignment, right)
}

fn expr_stmt(expr: Node<Expr>) -> Node<Stmt> {
  stmt(Stmt::Expr(node(ExprStmt { expr })))
}

fn empty_stmt() -> Node<Stmt> {
  stmt(Stmt::Empty(node(EmptyStmt {})))
}

fn break_stmt(label: Option<&str>) -> Node<Stmt> {
  stmt(Stmt::Break(node(BreakStmt {
    label: label.map(|s| s.to_string()),
  })))
}

fn var_decl_stmt(name: &str, init: Node<Expr>) -> Node<Stmt> {
  stmt(Stmt::VarDecl(node(VarDecl {
    export: false,
    mode: VarDeclMode::Var,
    declarators: vec![VarDeclarator {
      pattern: node(PatDecl {
        pat: node(Pat::Id(node(IdPat {
          name: name.to_string(),
        }))),
      }),
      definite_assignment: false,
      type_annotation: None,
      initializer: Some(init),
    }],
  })))
}

fn emit_top_level(stmts: Vec<Node<Stmt>>) -> String {
  let top = TopLevel { body: stmts };
  let mut emitter = Emitter::new(EmitOptions {
    mode: EmitMode::Minified,
  });
  emit_js_top_level(&mut emitter, &top).unwrap();
  String::from_utf8(emitter.into_bytes()).unwrap()
}

fn emit_single_stmt(stmt: Node<Stmt>) -> String {
  emit_top_level(vec![stmt])
}

#[test]
fn top_level_skips_empty_statements() {
  let output = emit_top_level(vec![empty_stmt(), expr_stmt(id("x"))]);
  assert_eq!(output, "x;");
}

#[test]
fn if_wraps_non_block_bodies() {
  let if_stmt = stmt(Stmt::If(node(IfStmt {
    test: id("cond"),
    consequent: expr_stmt(assign(id("a"), lit_num(1.0))),
    alternate: Some(expr_stmt(assign(id("b"), lit_num(2.0)))),
  })));
  let output = emit_single_stmt(if_stmt);
  assert_eq!(output, "if(cond){a=1;}else{b=2;}");
}

#[test]
fn while_wraps_body() {
  let while_stmt = stmt(Stmt::While(node(WhileStmt {
    condition: id("ready"),
    body: expr_stmt(id("ready")),
  })));
  let output = emit_single_stmt(while_stmt);
  assert_eq!(output, "while(ready){ready;}");
}

#[test]
fn for_triple_emits_all_parts_and_body_block() {
  let init = var_decl_stmt("i", lit_num(0.0));
  let cond = binary(id("i"), OperatorName::LessThan, id("n"));
  let post = binary(id("i"), OperatorName::AssignmentAddition, lit_num(1.0));
  let for_stmt = stmt(Stmt::ForTriple(node(ForTripleStmt {
    init: ForTripleStmtInit::Decl(match *init.stx {
      Stmt::VarDecl(decl) => decl,
      _ => unreachable!(),
    }),
    cond: Some(cond),
    post: Some(post),
    body: node(ForBody {
      body: vec![expr_stmt(id("i"))],
    }),
  })));

  let output = emit_single_stmt(for_stmt);
  assert_eq!(output, "for(var i=0;i<n;i+=1){i;}");
}

#[test]
fn var_decl_statement_emits_semicolon() {
  let output = emit_single_stmt(var_decl_stmt("x", lit_num(1.0)));
  assert_eq!(output, "var x=1;");
}

#[test]
fn break_emits_semicolon() {
  let output = emit_single_stmt(break_stmt(Some("loop")));
  assert_eq!(output, "break loop;");
}
