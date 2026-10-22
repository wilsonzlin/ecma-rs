use super::{OptCtx, Pass};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::expr::lit::{LitNullExpr, LitNumExpr};
use parse_js::ast::expr::{BinaryExpr, Expr, IdExpr, UnaryExpr};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{ReturnStmt, Stmt};
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
    let mut trailing_visitor = TrailingReturnTrimVisitor { changed: false };
    top.drive_mut(&mut trailing_visitor);
    visitor.changed || undefined_visitor.changed || trailing_visitor.changed
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
    let Some(scope) = scope_id(assoc) else {
      return false;
    };
    if self.cx.disabled_scopes.contains(&scope) {
      return true;
    }

    // `eval` in an ancestor scope can introduce new bindings into the parent
    // environment record at runtime. Nested functions close over that record, so
    // rewrites that assume global `undefined` is unshadowed (e.g. `return
    // undefined;` → `return;`) are not safe in descendant scopes either.
    let sem = self.cx.sem();
    let mut current = sem.scope(scope).parent;
    while let Some(scope_id) = current {
      if sem.scope(scope_id).has_direct_eval {
        return true;
      }
      current = sem.scope(scope_id).parent;
    }
    false
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
    let loc = node.loc;
    let replacement = match node.stx.as_ref() {
      // `x === null || x === undefined` -> `x == null`.
      Expr::Binary(bin) if bin.stx.operator == OperatorName::LogicalOr => {
        match_nullish_check(bin, OperatorName::StrictEquality)
          .map(|name| build_loose_null_check(loc, name, false))
      }
      // `x !== null && x !== undefined` -> `x != null` (the De Morgan dual).
      Expr::Binary(bin) if bin.stx.operator == OperatorName::LogicalAnd => {
        match_nullish_check(bin, OperatorName::StrictInequality)
          .map(|name| build_loose_null_check(loc, name, true))
      }
      // `typeof x === "undefined"` -> `x === void 0` (and the `!==` dual).
      //
      // Only strict comparisons are handled: `typeof x` always yields a string,
      // so `==`/`===` against `"undefined"` are equivalent for the *input*, but
      // the rewrite must stay strict because `x == null` would also match
      // `null`. Requiring `===`/`!==` on input keeps the mapping to `void 0`
      // unambiguous.
      Expr::Binary(bin)
        if matches!(
          bin.stx.operator,
          OperatorName::StrictEquality | OperatorName::StrictInequality
        ) =>
      {
        match_typeof_undefined(bin)
          .map(|(name, negated)| build_typeof_undefined_check(loc, name, negated))
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
#[visitor(FuncNode(exit))]
struct TrailingReturnTrimVisitor {
  changed: bool,
}

type FuncNode = Node<Func>;

impl TrailingReturnTrimVisitor {
  fn exit_func_node(&mut self, node: &mut FuncNode) {
    let Some(FuncBody::Block(stmts)) = node.stx.body.as_mut() else {
      return;
    };
    // A bare `return;` as the final statement of a function body is redundant:
    // control falls off the end returning `undefined` regardless. This holds for
    // every function kind — normal, async (resolves with `undefined`), generator
    // (`{value: undefined, done: true}`), getters, setters, and constructors
    // (`return;` in a constructor still yields the constructed `this`, exactly
    // like falling off the end). We only touch the final *direct* statement so
    // returns that guard later code (e.g. inside `try`/`finally` or a nested
    // block) are never removed.
    if stmts.last().is_some_and(is_bare_return) {
      stmts.pop();
      self.changed = true;
    }
  }
}

fn is_bare_return(stmt: &Node<Stmt>) -> bool {
  matches!(stmt.stx.as_ref(), Stmt::Return(ret) if ret.stx.value.is_none())
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
    let Some(scope) = scope_id(assoc) else {
      return false;
    };
    if self.cx.disabled_scopes.contains(&scope) {
      return true;
    }

    // See `SemanticRewriteVisitor::is_disabled` for why descendant scopes of
    // `eval` hazards must also be excluded from `undefined` rewrites.
    let sem = self.cx.sem();
    let mut current = sem.scope(scope).parent;
    while let Some(scope_id) = current {
      if sem.scope(scope_id).has_direct_eval {
        return true;
      }
      current = sem.scope(scope_id).parent;
    }
    false
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

/// Matches `<x> <eq_op> null <join> <x> <eq_op> undefined` (in either member
/// order) where both sides reference the *same* resolved binding, returning the
/// identifier name. `join`/`eq_op` are supplied by the caller: `||`/`===` for the
/// `== null` rewrite and `&&`/`!==` for the `!= null` rewrite.
fn match_nullish_check(bin: &Node<BinaryExpr>, eq_op: OperatorName) -> Option<String> {
  let left = match_eq_nullish(&bin.stx.left, eq_op)?;
  let right = match_eq_nullish(&bin.stx.right, eq_op)?;
  // Same resolved binding on both sides. Requiring a resolved `SymbolId` (rather
  // than matching by spelling) restricts this to plain identifiers: member paths
  // like `a.b` have observable getters and must not be read twice.
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

fn match_eq_nullish(
  expr: &Node<Expr>,
  eq_op: OperatorName,
) -> Option<(SymbolId, NullishKind, String)> {
  let Expr::Binary(bin) = expr.stx.as_ref() else {
    return None;
  };
  if bin.stx.operator != eq_op {
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

fn build_loose_null_check(loc: Loc, name: String, negated: bool) -> Expr {
  Expr::Binary(Node::new(
    loc,
    BinaryExpr {
      operator: if negated {
        OperatorName::Inequality
      } else {
        OperatorName::Equality
      },
      left: Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name }))),
      right: Node::new(loc, Expr::LitNull(Node::new(loc, LitNullExpr {}))),
    },
  ))
}

/// Matches `typeof <x> === "undefined"` (in either member order), returning the
/// identifier name and whether the comparison was negated (`!==`).
///
/// The rewrite to `x === void 0` is only sound when `x` resolves to a real
/// binding: `typeof x` tolerates a completely *undeclared* `x` (yielding
/// `"undefined"`), whereas a bare `x === void 0` read throws `ReferenceError`.
/// TDZ is unaffected — both `typeof x` and `x === void 0` throw on a `let`/`const`
/// still in its temporal dead zone.
fn match_typeof_undefined(bin: &Node<BinaryExpr>) -> Option<(String, bool)> {
  let negated = match bin.stx.operator {
    OperatorName::StrictEquality => false,
    OperatorName::StrictInequality => true,
    _ => return None,
  };
  let name = match_typeof_id(&bin.stx.left, &bin.stx.right)
    .or_else(|| match_typeof_id(&bin.stx.right, &bin.stx.left))?;
  Some((name, negated))
}

fn match_typeof_id(maybe_typeof: &Node<Expr>, other: &Node<Expr>) -> Option<String> {
  let Expr::LitStr(lit) = other.stx.as_ref() else {
    return None;
  };
  if lit.stx.value != "undefined" {
    return None;
  }
  let Expr::Unary(unary) = maybe_typeof.stx.as_ref() else {
    return None;
  };
  if unary.stx.operator != OperatorName::Typeof {
    return None;
  }
  let Expr::Id(id) = unary.stx.argument.stx.as_ref() else {
    return None;
  };
  // Require a resolved binding; see `match_typeof_undefined`.
  resolved_symbol(&id.assoc)?;
  Some(id.stx.name.clone())
}

fn build_typeof_undefined_check(loc: Loc, name: String, negated: bool) -> Expr {
  Expr::Binary(Node::new(
    loc,
    BinaryExpr {
      operator: if negated {
        OperatorName::StrictInequality
      } else {
        OperatorName::StrictEquality
      },
      left: Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name }))),
      right: Node::new(loc, build_void_zero(loc)),
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
