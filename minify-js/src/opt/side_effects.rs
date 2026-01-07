use parse_js::ast::class_or_object::{ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::lit::{LitArrElem, LitTemplatePart};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::operator::OperatorName;

#[derive(Copy, Clone, Eq, PartialEq)]
enum BigIntKind {
  BigInt,
  NotBigInt,
  Unknown,
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum BigIntSign {
  Negative,
  Zero,
  Positive,
}

fn expr_definitely_string(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::LitStr(_) | Expr::LitTemplate(_) => true,
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Addition => {
      expr_definitely_string(&bin.stx.left) || expr_definitely_string(&bin.stx.right)
    }
    Expr::Cond(cond) => {
      expr_definitely_string(&cond.stx.consequent) && expr_definitely_string(&cond.stx.alternate)
    }
    _ => false,
  }
}

fn expr_bigint_kind(expr: &Node<Expr>) -> BigIntKind {
  match expr.stx.as_ref() {
    Expr::LitBigInt(_) => BigIntKind::BigInt,
    Expr::LitNull(_) | Expr::LitBool(_) | Expr::LitNum(_) | Expr::LitStr(_) | Expr::LitTemplate(_) => {
      BigIntKind::NotBigInt
    }
    Expr::LitRegex(_) => BigIntKind::NotBigInt,
    Expr::ArrowFunc(_) | Expr::Func(_) | Expr::LitArr(_) | Expr::LitObj(_) | Expr::Class(_) => {
      BigIntKind::NotBigInt
    }
    Expr::Unary(unary) => match unary.stx.operator {
      OperatorName::UnaryNegation | OperatorName::BitwiseNot => expr_bigint_kind(&unary.stx.argument),
      OperatorName::UnaryPlus => match expr_bigint_kind(&unary.stx.argument) {
        // `+1n` throws, so treat it as unknown to avoid assuming it's safe.
        BigIntKind::BigInt | BigIntKind::Unknown => BigIntKind::Unknown,
        BigIntKind::NotBigInt => BigIntKind::NotBigInt,
      },
      OperatorName::LogicalNot | OperatorName::Void => BigIntKind::NotBigInt,
      _ => BigIntKind::Unknown,
    },
    Expr::Binary(bin) => {
      use OperatorName::*;
      match bin.stx.operator {
        Addition => {
          if expr_definitely_string(&bin.stx.left) || expr_definitely_string(&bin.stx.right) {
            return BigIntKind::NotBigInt;
          }
          let left = expr_bigint_kind(&bin.stx.left);
          let right = expr_bigint_kind(&bin.stx.right);
          if left == right {
            left
          } else {
            BigIntKind::Unknown
          }
        }
        Subtraction
        | Multiplication
        | Division
        | Remainder
        | Exponentiation
        | BitwiseAnd
        | BitwiseOr
        | BitwiseXor
        | BitwiseLeftShift
        | BitwiseRightShift => {
          let left = expr_bigint_kind(&bin.stx.left);
          let right = expr_bigint_kind(&bin.stx.right);
          if left == right {
            left
          } else {
            BigIntKind::Unknown
          }
        }
        BitwiseUnsignedRightShift => {
          let left = expr_bigint_kind(&bin.stx.left);
          let right = expr_bigint_kind(&bin.stx.right);
          if left == BigIntKind::NotBigInt && right == BigIntKind::NotBigInt {
            BigIntKind::NotBigInt
          } else {
            BigIntKind::Unknown
          }
        }
        LessThan
        | LessThanOrEqual
        | GreaterThan
        | GreaterThanOrEqual
        | Equality
        | Inequality
        | StrictEquality
        | StrictInequality => BigIntKind::NotBigInt,
        LogicalAnd | LogicalOr | NullishCoalescing => {
          let left = expr_bigint_kind(&bin.stx.left);
          let right = expr_bigint_kind(&bin.stx.right);
          if left == right {
            left
          } else {
            BigIntKind::Unknown
          }
        }
        _ => BigIntKind::Unknown,
      }
    }
    Expr::Cond(cond) => {
      let consequent = expr_bigint_kind(&cond.stx.consequent);
      let alternate = expr_bigint_kind(&cond.stx.alternate);
      if consequent == alternate {
        consequent
      } else {
        BigIntKind::Unknown
      }
    }
    _ => BigIntKind::Unknown,
  }
}

fn expr_bigint_sign(expr: &Node<Expr>) -> Option<BigIntSign> {
  match expr.stx.as_ref() {
    Expr::LitBigInt(lit) => {
      if lit.stx.value == "0" {
        Some(BigIntSign::Zero)
      } else {
        Some(BigIntSign::Positive)
      }
    }
    Expr::Unary(unary) if unary.stx.operator == OperatorName::UnaryNegation => match expr_bigint_sign(&unary.stx.argument)? {
      BigIntSign::Negative => Some(BigIntSign::Positive),
      BigIntSign::Positive => Some(BigIntSign::Negative),
      BigIntSign::Zero => Some(BigIntSign::Zero),
    },
    _ => None,
  }
}

pub(super) fn is_side_effect_free_expr(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::LitNull(_)
    | Expr::LitBool(_)
    | Expr::LitNum(_)
    | Expr::LitStr(_)
    | Expr::LitBigInt(_)
    | Expr::LitRegex(_) => true,
    Expr::ArrowFunc(_) | Expr::Func(_) => true,
    Expr::Unary(unary) => match unary.stx.operator {
      OperatorName::UnaryPlus => {
        is_side_effect_free_expr(&unary.stx.argument)
          && expr_bigint_kind(&unary.stx.argument) == BigIntKind::NotBigInt
      }
      OperatorName::UnaryNegation
      | OperatorName::LogicalNot
      | OperatorName::BitwiseNot
      | OperatorName::Void => is_side_effect_free_expr(&unary.stx.argument),
      _ => false,
    },
    Expr::Binary(bin) => {
      if !is_side_effect_free_expr(&bin.stx.left) || !is_side_effect_free_expr(&bin.stx.right) {
        return false;
      }
      use OperatorName::*;
      match bin.stx.operator {
        Addition => {
          if expr_definitely_string(&bin.stx.left) || expr_definitely_string(&bin.stx.right) {
            return true;
          }
          match (expr_bigint_kind(&bin.stx.left), expr_bigint_kind(&bin.stx.right)) {
            (BigIntKind::BigInt, BigIntKind::BigInt)
            | (BigIntKind::NotBigInt, BigIntKind::NotBigInt) => true,
            _ => false,
          }
        }
        Subtraction
        | Multiplication
        | BitwiseAnd
        | BitwiseOr
        | BitwiseXor => match (expr_bigint_kind(&bin.stx.left), expr_bigint_kind(&bin.stx.right)) {
          (BigIntKind::BigInt, BigIntKind::BigInt)
          | (BigIntKind::NotBigInt, BigIntKind::NotBigInt) => true,
          _ => false,
        },
        Division | Remainder => match (expr_bigint_kind(&bin.stx.left), expr_bigint_kind(&bin.stx.right)) {
          (BigIntKind::NotBigInt, BigIntKind::NotBigInt) => true,
          (BigIntKind::BigInt, BigIntKind::BigInt) => match expr_bigint_sign(&bin.stx.right) {
            Some(BigIntSign::Zero) => false,
            Some(BigIntSign::Negative) | Some(BigIntSign::Positive) => true,
            None => false,
          },
          _ => false,
        },
        Exponentiation => match (expr_bigint_kind(&bin.stx.left), expr_bigint_kind(&bin.stx.right)) {
          (BigIntKind::NotBigInt, BigIntKind::NotBigInt) => true,
          (BigIntKind::BigInt, BigIntKind::BigInt) => match expr_bigint_sign(&bin.stx.right) {
            Some(BigIntSign::Negative) => false,
            Some(BigIntSign::Zero) | Some(BigIntSign::Positive) => true,
            None => false,
          },
          _ => false,
        },
        BitwiseLeftShift | BitwiseRightShift => {
          match (expr_bigint_kind(&bin.stx.left), expr_bigint_kind(&bin.stx.right)) {
            (BigIntKind::NotBigInt, BigIntKind::NotBigInt) => true,
            (BigIntKind::BigInt, BigIntKind::BigInt) => match expr_bigint_sign(&bin.stx.right) {
              Some(BigIntSign::Negative) => false,
              Some(BigIntSign::Zero) | Some(BigIntSign::Positive) => true,
              None => false,
            },
            _ => false,
          }
        }
        BitwiseUnsignedRightShift => {
          match (expr_bigint_kind(&bin.stx.left), expr_bigint_kind(&bin.stx.right)) {
            (BigIntKind::NotBigInt, BigIntKind::NotBigInt) => true,
            _ => false,
          }
        }
        LessThan
        | LessThanOrEqual
        | GreaterThan
        | GreaterThanOrEqual
        | Equality
        | Inequality
        | StrictEquality
        | StrictInequality
        | LogicalAnd
        | LogicalOr
        | NullishCoalescing => true,
        _ => false,
      }
    }
    Expr::Cond(cond) => {
      is_side_effect_free_expr(&cond.stx.test)
        && is_side_effect_free_expr(&cond.stx.consequent)
        && is_side_effect_free_expr(&cond.stx.alternate)
    }
    Expr::LitArr(arr) => arr.stx.elements.iter().all(|elem| match elem {
      LitArrElem::Single(expr) => is_side_effect_free_expr(expr),
      LitArrElem::Empty => true,
      LitArrElem::Rest(_) => false,
    }),
    Expr::LitObj(obj) => obj.stx.members.iter().all(|member| match &member.stx.typ {
      ObjMemberType::Valued { key, val } => {
        if matches!(key, ClassOrObjKey::Computed(_)) {
          return false;
        }
        match val {
          ClassOrObjVal::Prop(Some(expr)) => is_side_effect_free_expr(expr),
          ClassOrObjVal::Prop(None) => true,
          ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_) | ClassOrObjVal::Method(_) => true,
          ClassOrObjVal::StaticBlock(_) => false,
          ClassOrObjVal::IndexSignature(_) => true,
        }
      }
      ObjMemberType::Shorthand { .. } => false,
      ObjMemberType::Rest { .. } => false,
    }),
    Expr::Class(class) => {
      if !class.stx.decorators.is_empty() {
        return false;
      }
      if class.stx.extends.is_some() {
        // Conservatively treat `extends` as potentially throwing even if the
        // expression itself is "pure" (e.g. `class extends 1 {}` throws).
        return false;
      }
      class
        .stx
        .members
        .iter()
        .all(|member| is_side_effect_free_class_member(member))
    }
    Expr::LitTemplate(tpl) => tpl.stx.parts.iter().all(|part| match part {
      LitTemplatePart::String(_) => true,
      LitTemplatePart::Substitution(expr) => is_side_effect_free_expr(expr),
    }),
    _ => false,
  }
}

pub(super) fn is_side_effect_free_class_decl(decl: &Node<ClassDecl>) -> bool {
  if !decl.stx.decorators.is_empty() {
    return false;
  }
  if decl.stx.extends.is_some() {
    // Conservatively treat `extends` as potentially throwing even if the
    // expression itself is "pure" (e.g. `class extends 1 {}` throws).
    return false;
  }
  decl
    .stx
    .members
    .iter()
    .all(|member| is_side_effect_free_class_member(member))
}

fn is_side_effect_free_class_member(member: &Node<ClassMember>) -> bool {
  if !member.stx.decorators.is_empty() {
    return false;
  }
  if matches!(&member.stx.key, ClassOrObjKey::Computed(_)) {
    return false;
  }
  match &member.stx.val {
    ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_) | ClassOrObjVal::Method(_) => true,
    ClassOrObjVal::Prop(init) => {
      if member.stx.static_ {
        init.as_ref().map_or(true, is_side_effect_free_expr)
      } else {
        // Instance field initializers are not evaluated at class-definition
        // time.
        true
      }
    }
    ClassOrObjVal::IndexSignature(_) => true,
    // Static blocks execute during class definition.
    ClassOrObjVal::StaticBlock(_) => false,
  }
}
