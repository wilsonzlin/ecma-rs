use super::{OptCtx, Pass};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::expr::lit::{LitNullExpr, LitNumExpr};
use parse_js::ast::expr::{BinaryExpr, Expr, IdExpr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::ReturnStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use semantic_js::assoc::js::{resolved_symbol, scope_id};
use semantic_js::js::SymbolId;

pub(super) struct SemanticRewritePass;

impl Pass for SemanticRewritePass {
  fn name(&self) -> &'static str {
    "sem-rewrite"
  }

  fn run(&mut self, cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    let mut visitor = SemanticRewriteVisitor::new(cx);
    top.drive_mut(&mut visitor);
    let mut undefined_visitor = GlobalUndefinedToVoidZeroVisitor::new(cx);
    top.drive_mut(&mut undefined_visitor);
    visitor.changed || undefined_visitor.changed
  }
}

type ExprNode = Node<Expr>;
type ReturnStmtNode = Node<ReturnStmt>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NullishKind {
  Null,
  Undefined,
}

#[derive(VisitorMut)]
#[visitor(ExprNode(exit), ReturnStmtNode(exit))]
struct SemanticRewriteVisitor<'a> {
  cx: &'a OptCtx,
  changed: bool,
}

impl<'a> SemanticRewriteVisitor<'a> {
  fn new(cx: &'a OptCtx) -> Self {
    Self { cx, changed: false }
  }

  fn is_disabled(&self, assoc: &parse_js::ast::node::NodeAssocData) -> bool {
    scope_id(assoc)
      .map(|scope| self.cx.disabled_scopes.contains(&scope))
      .unwrap_or(false)
  }

  fn exit_return_stmt_node(&mut self, node: &mut ReturnStmtNode) {
    if self.is_disabled(&node.assoc) {
      return;
    }
    let Some(value) = node.stx.value.as_ref() else {
      return;
    };
    if is_global_undefined(value) {
      self.changed = true;
      node.stx.value = None;
    }
  }

  fn exit_expr_node(&mut self, node: &mut ExprNode) {
    if self.is_disabled(&node.assoc) {
      return;
    }
    let replacement = match node.stx.as_ref() {
      Expr::Binary(or_expr) if or_expr.stx.operator == OperatorName::LogicalOr => {
        match_nullish_check(or_expr).map(|name| build_loose_null_check(node.loc, name))
      }
      _ => None,
    };
    if let Some(expr) = replacement {
      self.changed = true;
      *node.stx = expr;
    }
  }
}

#[derive(VisitorMut)]
#[visitor(ExprNode(exit))]
struct GlobalUndefinedToVoidZeroVisitor<'a> {
  cx: &'a OptCtx,
  changed: bool,
}

impl<'a> GlobalUndefinedToVoidZeroVisitor<'a> {
  fn new(cx: &'a OptCtx) -> Self {
    Self { cx, changed: false }
  }

  fn is_disabled(&self, assoc: &parse_js::ast::node::NodeAssocData) -> bool {
    scope_id(assoc)
      .map(|scope| self.cx.disabled_scopes.contains(&scope))
      .unwrap_or(false)
  }

  fn exit_expr_node(&mut self, node: &mut ExprNode) {
    if self.is_disabled(&node.assoc) {
      return;
    }

    let Expr::Id(id) = node.stx.as_ref() else {
      return;
    };
    if id.stx.name == "undefined" && resolved_symbol(&id.assoc).is_none() {
      self.changed = true;
      *node.stx = build_void_zero(node.loc);
    }
  }
}

fn is_global_undefined(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::Id(id) => id.stx.name == "undefined" && resolved_symbol(&id.assoc).is_none(),
    _ => false,
  }
}

fn match_nullish_check(or_expr: &Node<BinaryExpr>) -> Option<String> {
  let left = match_strict_eq_nullish(&or_expr.stx.left)?;
  let right = match_strict_eq_nullish(&or_expr.stx.right)?;
  if left.0 != right.0 {
    return None;
  }
  if (left.1 == NullishKind::Null && right.1 == NullishKind::Undefined)
    || (left.1 == NullishKind::Undefined && right.1 == NullishKind::Null)
  {
    return Some(left.2);
  }
  None
}

fn match_strict_eq_nullish(expr: &Node<Expr>) -> Option<(SymbolId, NullishKind, String)> {
  let Expr::Binary(bin) = expr.stx.as_ref() else {
    return None;
  };
  if bin.stx.operator != OperatorName::StrictEquality {
    return None;
  }

  match_id_and_nullish(&bin.stx.left, &bin.stx.right)
    .or_else(|| match_id_and_nullish(&bin.stx.right, &bin.stx.left))
}

fn match_id_and_nullish(
  maybe_id: &Node<Expr>,
  other: &Node<Expr>,
) -> Option<(SymbolId, NullishKind, String)> {
  let Expr::Id(id) = maybe_id.stx.as_ref() else {
    return None;
  };
  let sym = resolved_symbol(&id.assoc)?;
  let kind = match other.stx.as_ref() {
    Expr::LitNull(_) => NullishKind::Null,
    Expr::Id(other_id)
      if other_id.stx.name == "undefined" && resolved_symbol(&other_id.assoc).is_none() =>
    {
      NullishKind::Undefined
    }
    _ => return None,
  };
  Some((sym, kind, id.stx.name.clone()))
}

fn build_loose_null_check(loc: Loc, name: String) -> Expr {
  Expr::Binary(Node::new(
    loc,
    BinaryExpr {
      operator: OperatorName::Equality,
      left: Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name }))),
      right: Node::new(loc, Expr::LitNull(Node::new(loc, LitNullExpr {}))),
    },
  ))
}

fn build_void_zero(loc: Loc) -> Expr {
  Expr::Unary(Node::new(
    loc,
    UnaryExpr {
      operator: OperatorName::Void,
      argument: Node::new(
        loc,
        Expr::LitNum(Node::new(
          loc,
          LitNumExpr {
            value: JsNumber(0.0),
          },
        )),
      ),
    },
  ))
}
