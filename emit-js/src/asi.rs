use parse_js::ast::expr::{Expr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDeclarator;
use parse_js::ast::stmt::{ForBody, Stmt};
use parse_js::operator::OperatorName;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtStartToken {
  Paren,
  Bracket,
  Plus,
  Minus,
  Slash,
  Template,
  Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtLeafEnd {
  BlockLike,
  EmptyStmt,
  Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Separator {
  None,
  Newline,
  Semicolon,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ListEnd {
  CloseBrace,
  Eof,
  StatementFollows,
}

pub fn stmt_start_token(stmt: &Node<Stmt>) -> StmtStartToken {
  match stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr_start_token(&expr.stx.expr),
    _ => StmtStartToken::Other,
  }
}

pub fn stmt_leaf_end(stmt: &Node<Stmt>) -> StmtLeafEnd {
  match stmt.stx.as_ref() {
    Stmt::Block(_)
    | Stmt::Try(_)
    | Stmt::Switch(_)
    | Stmt::FunctionDecl(_)
    | Stmt::ClassDecl(_)
    | Stmt::NamespaceDecl(_)
    | Stmt::ModuleDecl(_)
    | Stmt::GlobalDecl(_)
    | Stmt::EnumDecl(_) => StmtLeafEnd::BlockLike,
    Stmt::Empty(_) => StmtLeafEnd::EmptyStmt,
    Stmt::Label(label) => stmt_leaf_end(&label.stx.statement),
    Stmt::While(while_stmt) => stmt_leaf_end(&while_stmt.stx.body),
    Stmt::DoWhile(_) => StmtLeafEnd::Other,
    Stmt::ForIn(for_in) => for_body_leaf_end(&for_in.stx.body),
    Stmt::ForOf(for_of) => for_body_leaf_end(&for_of.stx.body),
    Stmt::ForTriple(for_triple) => for_body_leaf_end(&for_triple.stx.body),
    Stmt::With(with_stmt) => stmt_leaf_end(&with_stmt.stx.body),
    Stmt::If(if_stmt) => {
      if let Some(alt) = &if_stmt.stx.alternate {
        stmt_leaf_end(alt)
      } else {
        stmt_leaf_end(&if_stmt.stx.consequent)
      }
    }
    _ => StmtLeafEnd::Other,
  }
}

pub fn stmt_tail_is_expression_like(stmt: &Node<Stmt>) -> bool {
  match stmt.stx.as_ref() {
    Stmt::Expr(_) => true,
    Stmt::Return(ret) => ret.stx.value.is_some(),
    Stmt::Throw(_) => true,
    Stmt::ExportDefaultExpr(_) => true,
    Stmt::ExportAssignmentDecl(_) => true,
    Stmt::VarDecl(decl) => var_decl_ends_with_initializer(decl.stx.declarators.last()),
    Stmt::Label(label) => stmt_tail_is_expression_like(&label.stx.statement),
    Stmt::While(while_stmt) => stmt_tail_is_expression_like(&while_stmt.stx.body),
    Stmt::DoWhile(_) => false,
    Stmt::ForIn(for_in) => for_body_tail_is_expression_like(&for_in.stx.body),
    Stmt::ForOf(for_of) => for_body_tail_is_expression_like(&for_of.stx.body),
    Stmt::ForTriple(for_triple) => for_body_tail_is_expression_like(&for_triple.stx.body),
    Stmt::With(with_stmt) => stmt_tail_is_expression_like(&with_stmt.stx.body),
    Stmt::If(if_stmt) => {
      if let Some(alt) = &if_stmt.stx.alternate {
        stmt_tail_is_expression_like(alt)
      } else {
        stmt_tail_is_expression_like(&if_stmt.stx.consequent)
      }
    }
    _ => false,
  }
}

pub fn separator_between(prev: Option<&Node<Stmt>>, next: &Node<Stmt>) -> Separator {
  let Some(prev) = prev else {
    return Separator::None;
  };

  match stmt_leaf_end(prev) {
    StmtLeafEnd::BlockLike => Separator::None,
    StmtLeafEnd::EmptyStmt => Separator::Semicolon,
    StmtLeafEnd::Other => {
      if is_hazard_start(stmt_start_token(next)) && stmt_tail_is_expression_like(prev) {
        Separator::Semicolon
      } else {
        Separator::Newline
      }
    }
  }
}

pub fn separator_after_last(stmt: &Node<Stmt>, end: ListEnd) -> Separator {
  match stmt_leaf_end(stmt) {
    StmtLeafEnd::BlockLike => Separator::None,
    StmtLeafEnd::EmptyStmt => Separator::Semicolon,
    StmtLeafEnd::Other => match end {
      ListEnd::StatementFollows => Separator::Newline,
      ListEnd::CloseBrace | ListEnd::Eof => Separator::None,
    },
  }
}

fn for_body_leaf_end(body: &Node<ForBody>) -> StmtLeafEnd {
  match body.stx.body.len() {
    0 => StmtLeafEnd::BlockLike,
    1 => stmt_leaf_end(&body.stx.body[0]),
    _ => StmtLeafEnd::BlockLike,
  }
}

fn for_body_tail_is_expression_like(body: &Node<ForBody>) -> bool {
  match body.stx.body.len() {
    0 => false,
    1 => stmt_tail_is_expression_like(&body.stx.body[0]),
    _ => false,
  }
}

fn var_decl_ends_with_initializer(decl: Option<&VarDeclarator>) -> bool {
  decl.and_then(|decl| decl.initializer.as_ref()).is_some()
}

fn is_hazard_start(token: StmtStartToken) -> bool {
  matches!(
    token,
    StmtStartToken::Paren
      | StmtStartToken::Bracket
      | StmtStartToken::Plus
      | StmtStartToken::Minus
      | StmtStartToken::Slash
      | StmtStartToken::Template
  )
}

fn expr_start_token(expr: &Node<Expr>) -> StmtStartToken {
  match expr.stx.as_ref() {
    Expr::LitArr(_) | Expr::ArrPat(_) => StmtStartToken::Bracket,
    Expr::LitTemplate(_) => StmtStartToken::Template,
    Expr::LitRegex(_) => StmtStartToken::Slash,
    Expr::LitObj(_) | Expr::Func(_) | Expr::Class(_) | Expr::ObjPat(_) | Expr::ArrowFunc(_) => {
      StmtStartToken::Paren
    }
    Expr::Unary(unary) => unary_start_token(unary),
    Expr::UnaryPostfix(expr) => expr_start_token(&expr.stx.argument),
    Expr::Binary(expr) => expr_start_token(&expr.stx.left),
    Expr::Call(expr) => expr_start_token(&expr.stx.callee),
    Expr::Member(expr) => expr_start_token(&expr.stx.left),
    Expr::ComputedMember(expr) => expr_start_token(&expr.stx.object),
    Expr::Cond(expr) => expr_start_token(&expr.stx.test),
    Expr::TaggedTemplate(expr) => expr_start_token(&expr.stx.function),
    Expr::TypeAssertion(expr) => expr_start_token(&expr.stx.expression),
    Expr::NonNullAssertion(expr) => expr_start_token(&expr.stx.expression),
    Expr::SatisfiesExpr(expr) => expr_start_token(&expr.stx.expression),
    _ => StmtStartToken::Other,
  }
}

fn unary_start_token(unary: &Node<UnaryExpr>) -> StmtStartToken {
  match unary.stx.operator {
    OperatorName::UnaryPlus | OperatorName::PrefixIncrement => StmtStartToken::Plus,
    OperatorName::UnaryNegation | OperatorName::PrefixDecrement => StmtStartToken::Minus,
    _ => StmtStartToken::Other,
  }
}
