use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::class_or_object::ClassOrObjMemberDirectKey;
use crate::ast::class_or_object::ClassOrObjVal;
use crate::ast::class_or_object::ObjMember;
use crate::ast::class_or_object::ObjMemberType;
use crate::ast::expr::lit::LitArrElem;
use crate::ast::expr::lit::LitArrExpr;
use crate::ast::expr::lit::LitObjExpr;
use crate::ast::expr::pat::ArrPat;
use crate::ast::expr::pat::ArrPatElem;
use crate::ast::expr::pat::IdPat;
use crate::ast::expr::pat::ObjPat;
use crate::ast::expr::pat::ObjPatProp;
use crate::ast::expr::pat::Pat;
use crate::ast::expr::BinaryExpr;
use crate::ast::expr::Expr;
use crate::ast::node::Node;
use crate::ast::node::ParenthesizedExpr;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::operator::OperatorName;
use crate::token::TT;

/// Converts a literal expression subtree into a pattern (assignment target).
/// `{ a: [b] }` could be an object literal or object pattern. This function is useful for when a pattern was misinterpreted as a literal expression, without needing to rewind and reparse.
pub fn lit_to_pat(node: Node<Expr>) -> SyntaxResult<Node<Pat>> {
  lit_to_pat_with_recover(node, true)
}

pub(crate) fn lit_to_pat_with_recover(node: Node<Expr>, recover: bool) -> SyntaxResult<Node<Pat>> {
  let loc = node.loc;

  // Parenthesized assignment targets are invalid in ECMAScript (e.g. `(a) = b`,
  // `([a]) = b`, `({a}) = b`). Preserve TypeScript-style recovery behaviour in
  // non-strict dialects.
  if !recover && node.assoc.get::<ParenthesizedExpr>().is_some() {
    return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
  }

  // TypeScript: Accept member expressions for error recovery, even with optional chaining.
  // Check for member expressions first (without moving the value).
  let is_member = match node.stx.as_ref() {
    Expr::Member(member) => {
      if !recover && member.stx.optional_chaining {
        return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
      }
      true
    }
    _ => false,
  };
  if is_member {
    return Ok(Node::new(loc, Pat::AssignTarget(node)));
  }
  let is_computed_member = match node.stx.as_ref() {
    Expr::ComputedMember(member) => {
      if !recover && member.stx.optional_chaining {
        return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
      }
      true
    }
    _ => false,
  };
  if is_computed_member {
    return Ok(Node::new(loc, Pat::AssignTarget(node)));
  }

  match *node.stx {
    Expr::LitArr(n) => {
      let LitArrExpr { elements } = *n.stx;
      let mut pat_elements = Vec::<Option<ArrPatElem>>::new();
      let mut rest = None;
      for element in elements {
        if rest.is_some() {
          return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
        };
        match element {
          LitArrElem::Single(elem) => {
            match *elem.stx {
              Expr::Binary(n) => {
                let BinaryExpr {
                  operator,
                  left,
                  right,
                } = *n.stx;
                if operator != OperatorName::Assignment {
                  return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
                };
                pat_elements.push(Some(ArrPatElem {
                  target: lit_to_pat_with_recover(left, recover)?,
                  default_value: Some(right),
                }));
              }
              _ => pat_elements.push(Some(ArrPatElem {
                target: lit_to_pat_with_recover(elem, recover)?,
                default_value: None,
              })),
            };
          }
          LitArrElem::Rest(expr) => {
            if recover {
              rest = Some(lit_to_pat_with_recover(expr, recover)?);
            } else {
              // Rest elements must be assignment targets (not patterns) in strict
              // ECMAScript mode.
              let rest_target = match expr.stx.as_ref() {
                Expr::Id(_) => lit_to_pat_with_recover(expr, recover)?,
                Expr::Member(member) if !member.stx.optional_chaining => {
                  Node::new(expr.loc, Pat::AssignTarget(expr))
                }
                Expr::ComputedMember(member) if !member.stx.optional_chaining => {
                  Node::new(expr.loc, Pat::AssignTarget(expr))
                }
                _ => return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None)),
              };
              rest = Some(rest_target);
            }
          }
          LitArrElem::Empty => pat_elements.push(None),
        };
      }
      Ok(
        Node::new(
          loc,
          ArrPat {
            elements: pat_elements,
            rest,
          },
        )
        .into_wrapped(),
      )
    }
    Expr::LitObj(n) => {
      let LitObjExpr { members } = *n.stx;
      let mut properties = Vec::new();
      let mut rest: Option<Node<Pat>> = None;
      for member in members {
        let loc = member.loc;
        if rest.is_some() {
          return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
        };
        match *member.stx {
          ObjMember { typ } => match typ {
            ObjMemberType::Valued { key, val: value } => {
              let (target, default_value) = match value {
                ClassOrObjVal::Prop(Some(initializer)) => match *initializer.stx {
                  Expr::Binary(n) => {
                    let BinaryExpr {
                      operator,
                      left,
                      right,
                    } = *n.stx;
                    if operator != OperatorName::Assignment {
                      return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
                    };
                    (lit_to_pat_with_recover(left, recover)?, Some(right))
                  }
                  _ => (lit_to_pat_with_recover(initializer, recover)?, None),
                },
                _ => return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None)),
              };
              properties.push(Node::new(
                loc,
                ObjPatProp {
                  key,
                  target,
                  default_value,
                  shorthand: true,
                },
              ));
            }
            ObjMemberType::Shorthand { id } => {
              properties.push(Node::new(
                loc,
                ObjPatProp {
                  key: ClassOrObjKey::Direct(id.derive_stx(|id| ClassOrObjMemberDirectKey {
                    key: id.name.clone(),
                    tt: TT::Identifier,
                  })),
                  target: id
                    .derive_stx(|id| IdPat {
                      name: id.name.clone(),
                    })
                    .into_wrapped(),
                  default_value: None,
                  shorthand: true,
                },
              ));
            }
            ObjMemberType::Rest { val: value } => {
              if recover {
                // TypeScript: For error recovery, allow any pattern in rest position
                // e.g., `{...{}}` or `{...[]}`.
                rest = Some(lit_to_pat_with_recover(value, recover)?);
              } else {
                // Rest properties must be assignment targets (not patterns) in
                // strict ECMAScript mode.
                let rest_target = match value.stx.as_ref() {
                  Expr::Id(_) => lit_to_pat_with_recover(value, recover)?,
                  Expr::Member(member) if !member.stx.optional_chaining => {
                    Node::new(loc, Pat::AssignTarget(value))
                  }
                  Expr::ComputedMember(member) if !member.stx.optional_chaining => {
                    Node::new(loc, Pat::AssignTarget(value))
                  }
                  _ => return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None)),
                };
                rest = Some(rest_target);
              }
            }
          },
        };
      }
      Ok(Node::new(loc, ObjPat { properties, rest }).into_wrapped())
    }
    Expr::Id(n) => Ok(
      Node::new(
        loc,
        IdPat {
          name: n.stx.name.clone(),
        },
      )
      .into_wrapped(),
    ),
    // It's possible to encounter patterns already parsed e.g. `{a: [b] = 1}`, where `[b]` was already converted to a pattern.
    Expr::IdPat(n) => Ok(n.into_wrapped()),
    Expr::ArrPat(n) => Ok(n.into_wrapped()),
    Expr::ObjPat(n) => Ok(n.into_wrapped()),
    // TypeScript: For any other expression type, wrap it as an assignment target for error recovery
    // This allows destructuring with call expressions, unary operators, etc.
    // The type checker will validate these patterns semantically.
    _ => {
      if recover {
        Ok(Node::new(loc, Pat::AssignTarget(node)))
      } else {
        Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None))
      }
    }
  }
}

// Trying to check if every object, array, or identifier expression operand is actually an assignment target first is too expensive and wasteful, so simply retroactively transform the LHS of a BinaryExpr with Assignment* operator into a target, raising an error if it can't (and is an invalid assignment target). A valid target is:
// - A chain of non-optional-chaining member, computed member, and call operators, not ending in a call.
// - A pattern.
// TypeScript: Be maximally permissive and accept most expression types for error recovery.
pub fn lhs_expr_to_assign_target(
  lhs: Node<Expr>,
  operator_name: OperatorName,
) -> SyntaxResult<Node<Expr>> {
  lhs_expr_to_assign_target_with_recover(lhs, operator_name, true)
}

pub(crate) fn lhs_expr_to_assign_target_with_recover(
  lhs: Node<Expr>,
  operator_name: OperatorName,
  recover: bool,
) -> SyntaxResult<Node<Expr>> {
  // Parenthesized assignment targets are invalid in ECMAScript (e.g. `(a) = b`,
  // `(obj.prop) = b`). Preserve TypeScript-style recovery behaviour in non-strict
  // dialects.
  if !recover && lhs.assoc.get::<ParenthesizedExpr>().is_some() {
    return Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget));
  }

  if !recover {
    return match lhs.stx.as_ref() {
      e @ (Expr::LitArr(_) | Expr::LitObj(_) | Expr::Id(_)) => {
        if operator_name != OperatorName::Assignment && !matches!(e, Expr::Id(_)) {
          return Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget));
        }
        // We must transform into a pattern.
        let root = lit_to_pat_with_recover(lhs, false)?;
        Ok(root.into_stx())
      }
      Expr::ComputedMember(member) if !member.stx.optional_chaining => Ok(lhs),
      Expr::Member(member) if !member.stx.optional_chaining => Ok(lhs),
      _ => Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget)),
    };
  }

  match lhs.stx.as_ref() {
    e @ (Expr::LitArr(_) | Expr::LitObj(_) | Expr::Id(_)) => {
      if operator_name != OperatorName::Assignment && !matches!(e, Expr::Id(_)) {
        return Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget));
      }
      // We must transform into a pattern.
      let root = lit_to_pat_with_recover(lhs, true)?;
      Ok(root.into_stx())
    }
    // TypeScript: Accept member/computed member expressions for error recovery, even with optional chaining
    // Patterns like `obj?.a = 1` are syntactically parseable but semantically invalid
    // The type checker will validate these
    Expr::ComputedMember(_) => Ok(lhs),
    Expr::Member(_) => Ok(lhs),
    // TypeScript: Accept call expressions, unary expressions, and postfix expressions for error recovery
    // This allows patterns like `foo() = bar`, `++x = 5`, `x++ = 5`, `++x++`, etc.
    // The type checker will reject these, but the parser accepts them.
    Expr::Call(_) | Expr::Unary(_) | Expr::UnaryPostfix(_) => Ok(lhs),
    // TypeScript: Accept literal expressions for error recovery
    // This allows patterns like `1 >>= 2`, `"str" = value`, etc.
    // The type checker will reject these, but the parser accepts them.
    Expr::LitNum(_)
    | Expr::LitStr(_)
    | Expr::LitBool(_)
    | Expr::LitNull(_)
    | Expr::LitBigInt(_)
    | Expr::LitRegex(_) => Ok(lhs),
    // TypeScript: Accept this, super, type assertions, and other TypeScript expressions for error recovery
    // This allows patterns like `this *= value`, `super = value`, `(expr as T) = value`, `expr! = value`
    Expr::This(_)
    | Expr::Super(_)
    | Expr::TypeAssertion(_)
    | Expr::NonNullAssertion(_)
    | Expr::SatisfiesExpr(_)
    // Allow import.meta as an assignment target for error recovery.
    // While it's not a valid target, TypeScript still parses it to produce semantic errors.
    | Expr::ImportMeta(_) => Ok(lhs),
    Expr::Binary(binary) if binary.stx.operator.is_assignment() => Ok(lhs),
    _ => Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget)),
  }
}
