use parse_js::ast::class_or_object::{ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::lit::{LitArrElem, LitTemplatePart};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::operator::OperatorName;

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
      OperatorName::UnaryPlus
      | OperatorName::UnaryNegation
      | OperatorName::LogicalNot
      | OperatorName::BitwiseNot
      | OperatorName::Void => is_side_effect_free_expr(&unary.stx.argument),
      _ => false,
    },
    Expr::Binary(bin) => {
      use OperatorName::*;
      if !is_side_effect_free_expr(&bin.stx.left) || !is_side_effect_free_expr(&bin.stx.right) {
        return false;
      }
      matches!(
        bin.stx.operator,
        Addition
          | Subtraction
          | Multiplication
          | Division
          | Remainder
          | Exponentiation
          | BitwiseAnd
          | BitwiseOr
          | BitwiseXor
          | BitwiseLeftShift
          | BitwiseRightShift
          | BitwiseUnsignedRightShift
          | LessThan
          | LessThanOrEqual
          | GreaterThan
          | GreaterThanOrEqual
          | Equality
          | Inequality
          | StrictEquality
          | StrictInequality
          | LogicalAnd
          | LogicalOr
          | NullishCoalescing
      )
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
