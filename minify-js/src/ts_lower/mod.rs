use parse_js::ast::expr::lit::{LitNumExpr, LitObjExpr, LitStrExpr};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::*;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ParamDecl, PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::*;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;

/// Key used for accessing object members.
pub enum MemberKey {
  Name(String),
  Expr(Node<Expr>),
}

pub fn id(loc: Loc, name: impl Into<String>) -> Node<Expr> {
  Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name: name.into() })))
}

pub fn string(loc: Loc, value: impl Into<String>) -> Node<Expr> {
  Node::new(
    loc,
    Expr::LitStr(Node::new(
      loc,
      LitStrExpr {
        value: value.into(),
      },
    )),
  )
}

pub fn number(loc: Loc, value: f64) -> Node<Expr> {
  Node::new(
    loc,
    Expr::LitNum(Node::new(
      loc,
      LitNumExpr {
        value: JsNumber(value),
      },
    )),
  )
}

pub fn empty_object(loc: Loc) -> Node<Expr> {
  Node::new(
    loc,
    Expr::LitObj(Node::new(loc, LitObjExpr { members: vec![] })),
  )
}

pub fn expr_stmt(loc: Loc, expr: Node<Expr>) -> Node<Stmt> {
  Node::new(loc, Stmt::Expr(Node::new(loc, ExprStmt { expr })))
}

pub fn binary_expr(
  loc: Loc,
  operator: parse_js::operator::OperatorName,
  left: Node<Expr>,
  right: Node<Expr>,
) -> Node<Expr> {
  Node::new(
    loc,
    Expr::Binary(Node::new(
      loc,
      BinaryExpr {
        operator,
        left,
        right,
      },
    )),
  )
}

pub fn assign_expr(loc: Loc, left: Node<Expr>, right: Node<Expr>) -> Node<Expr> {
  binary_expr(
    loc,
    parse_js::operator::OperatorName::Assignment,
    left,
    right,
  )
}

pub fn member_expr(loc: Loc, object: Node<Expr>, key: MemberKey) -> Node<Expr> {
  match key {
    MemberKey::Name(name) => Node::new(
      loc,
      Expr::ComputedMember(Node::new(
        loc,
        ComputedMemberExpr {
          optional_chaining: false,
          object,
          member: string(loc, name),
        },
      )),
    ),
    MemberKey::Expr(expr) => Node::new(
      loc,
      Expr::ComputedMember(Node::new(
        loc,
        ComputedMemberExpr {
          optional_chaining: false,
          object,
          member: expr,
        },
      )),
    ),
  }
}

pub fn member_assignment_stmt(
  loc: Loc,
  object: Node<Expr>,
  key: MemberKey,
  value: Node<Expr>,
) -> Node<Stmt> {
  let left = member_expr(loc, object, key);
  expr_stmt(loc, assign_expr(loc, left, value))
}

pub fn var_decl_stmt(
  loc: Loc,
  name: impl Into<String>,
  init: Option<Node<Expr>>,
  export: bool,
  mode: VarDeclMode,
) -> Node<Stmt> {
  let pat = Node::new(loc, Pat::Id(Node::new(loc, IdPat { name: name.into() })));
  let declarator = VarDeclarator {
    pattern: Node::new(loc, PatDecl { pat }),
    definite_assignment: false,
    type_annotation: None,
    initializer: init,
  };
  let decl = VarDecl {
    export,
    mode,
    declarators: vec![declarator],
  };
  Node::new(loc, Stmt::VarDecl(Node::new(loc, decl)))
}

pub fn iife_stmt(
  loc: Loc,
  param: impl Into<String>,
  arg: Node<Expr>,
  body: Vec<Node<Stmt>>,
) -> Node<Stmt> {
  let param = param.into();
  let func = Func {
    arrow: false,
    async_: false,
    generator: false,
    type_parameters: None,
    parameters: vec![Node::new(
      loc,
      ParamDecl {
        decorators: vec![],
        rest: false,
        optional: false,
        accessibility: None,
        readonly: false,
        pattern: Node::new(
          loc,
          PatDecl {
            pat: Node::new(loc, Pat::Id(Node::new(loc, IdPat { name: param }))),
          },
        ),
        type_annotation: None,
        default_value: None,
      },
    )],
    return_type: None,
    body: Some(FuncBody::Block(body)),
  };
  let func_expr = Expr::Func(Node::new(
    loc,
    FuncExpr {
      name: None,
      func: Node::new(loc, func),
    },
  ));
  let call = CallExpr {
    optional_chaining: false,
    callee: Node::new(loc, func_expr),
    arguments: vec![Node::new(
      loc,
      CallArg {
        spread: false,
        value: arg,
      },
    )],
  };
  let call_expr = Node::new(loc, Expr::Call(Node::new(loc, call)));
  // Ensure the expression statement doesn't start with `function`, which would
  // otherwise be parsed as a declaration.
  expr_stmt(
    loc,
    binary_expr(loc, OperatorName::Comma, number(loc, 0.0), call_expr),
  )
}
