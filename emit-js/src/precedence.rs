use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::operator::{Associativity, OperatorName, OPERATORS};

/// Wrapper around a precedence value with total ordering.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Prec(u8);

impl Prec {
  pub const LOWEST: Prec = Prec(0);

  pub const fn new(value: u8) -> Self {
    Prec(value)
  }

  pub const fn tighter(self) -> Self {
    Prec(self.0 + 1)
  }

  pub const fn value(self) -> u8 {
    self.0
  }
}

/// Precedence for `expr!` postfix.
pub const NON_NULL_ASSERTION_PRECEDENCE: Prec = Prec::new(18);
/// Precedence for `expr as Type` / `expr as const`.
pub const TYPE_ASSERTION_PRECEDENCE: Prec = Prec::new(15);
/// Precedence for `expr satisfies Type`.
pub const SATISFIES_PRECEDENCE: Prec = TYPE_ASSERTION_PRECEDENCE;
/// Precedence for optional chaining, member access, and call-like operators.
pub const CALL_MEMBER_PRECEDENCE: Prec = Prec::new(18);
/// Precedence for atomic expressions (identifiers, literals, etc.).
pub const PRIMARY_PRECEDENCE: Prec = Prec::new(19);
/// Precedence for arrow functions (lower than assignment to force parentheses when
/// used as operands).
pub const ARROW_FUNCTION_PRECEDENCE: Prec = Prec::new(2);

#[derive(Clone, Copy, Debug)]
pub enum Side {
  Left,
  Right,
}

pub fn needs_parens(child_prec: Prec, min_prec: Prec) -> bool {
  child_prec < min_prec
}

pub fn child_min_prec_for_binary(op: OperatorName, side: Side) -> Prec {
  let operator = OPERATORS
    .get(&op)
    .expect("operator precedence should be defined for all binary operators");
  let prec = Prec::new(operator.precedence);
  match operator.associativity {
    Associativity::Left => match side {
      Side::Left => prec,
      Side::Right => prec.tighter(),
    },
    Associativity::Right => match side {
      Side::Left => prec.tighter(),
      Side::Right => prec,
    },
  }
}

/// Returns the precedence of an expression kind. This is derived from the parser's
/// precedence table so that emitting without explicit `parenthesised` flags
/// re-parses to the same AST.
pub fn expr_prec(expr: &Node<Expr>) -> Prec {
  match expr.stx.as_ref() {
    Expr::Binary(binary) => Prec::new(OPERATORS[&binary.stx.operator].precedence),
    Expr::Cond(_) => Prec::new(OPERATORS[&OperatorName::Conditional].precedence),
    Expr::Unary(unary) => Prec::new(OPERATORS[&unary.stx.operator].precedence),
    Expr::UnaryPostfix(unary) => Prec::new(OPERATORS[&unary.stx.operator].precedence),
    Expr::Call(_) | Expr::Member(_) | Expr::ComputedMember(_) => CALL_MEMBER_PRECEDENCE,
    Expr::TaggedTemplate(_) => CALL_MEMBER_PRECEDENCE,
    Expr::NonNullAssertion(_) => NON_NULL_ASSERTION_PRECEDENCE,
    Expr::TypeAssertion(_) => TYPE_ASSERTION_PRECEDENCE,
    Expr::SatisfiesExpr(_) => SATISFIES_PRECEDENCE,
    Expr::ArrowFunc(_) => ARROW_FUNCTION_PRECEDENCE,
    Expr::Func(_) => PRIMARY_PRECEDENCE,
    Expr::Class(_) => PRIMARY_PRECEDENCE,
    Expr::Import(_) => CALL_MEMBER_PRECEDENCE,
    Expr::Id(id) => {
      if id.stx.name == "undefined" {
        Prec::new(OPERATORS[&OperatorName::Void].precedence)
      } else {
        PRIMARY_PRECEDENCE
      }
    }
    Expr::This(_)
    | Expr::Super(_)
    | Expr::NewTarget(_)
    | Expr::ImportMeta(_)
    | Expr::JsxElem(_)
    | Expr::JsxExprContainer(_)
    | Expr::JsxMember(_)
    | Expr::JsxName(_)
    | Expr::JsxSpreadAttr(_)
    | Expr::JsxText(_)
    | Expr::LitArr(_)
    | Expr::LitBigInt(_)
    | Expr::LitBool(_)
    | Expr::LitNull(_)
    | Expr::LitNum(_)
    | Expr::LitObj(_)
    | Expr::LitRegex(_)
    | Expr::LitStr(_)
    | Expr::LitTemplate(_)
    | Expr::ArrPat(_)
    | Expr::IdPat(_)
    | Expr::ObjPat(_) => PRIMARY_PRECEDENCE,
  }
}

pub fn starts_with_optional_chaining(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::Member(member) => {
      member.stx.optional_chaining || starts_with_optional_chaining(&member.stx.left)
    }
    Expr::ComputedMember(member) => {
      member.stx.optional_chaining || starts_with_optional_chaining(&member.stx.object)
    }
    Expr::Call(call) => {
      call.stx.optional_chaining || starts_with_optional_chaining(&call.stx.callee)
    }
    _ => false,
  }
}
