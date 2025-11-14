use crate::{ast::{class_or_object::{ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType}, expr::{BinaryExpr, ComputedMemberExpr, Expr, IdExpr, MemberExpr}, expr::lit::{LitArrElem, LitArrExpr, LitObjExpr}, node::Node, expr::pat::{ArrPat, ArrPatElem, IdPat, ObjPat, ObjPatProp, Pat}}, error::{SyntaxErrorType, SyntaxResult}, operator::OperatorName, token::TT};



/// Converts a literal expression subtree into a pattern (assignment target).
/// `{ a: [b] }` could be an object literal or object pattern. This function is useful for when a pattern was misinterpreted as a literal expression, without needing to rewind and reparse.
pub fn lit_to_pat(node: Node<Expr>) -> SyntaxResult<Node<Pat>> {
  let loc = node.loc;
  // TypeScript: Accept member expressions for error recovery, even with optional chaining
  // Check for member expressions first (without moving the value).
  match node.stx.as_ref() {
    Expr::Member(_) => {
      return Ok(Node::new(loc, Pat::AssignTarget(node)));
    }
    Expr::ComputedMember(_) => {
      return Ok(Node::new(loc, Pat::AssignTarget(node)));
    }
    _ => {}
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
                  target: lit_to_pat(left)?,
                  default_value: Some(right),
                }));
              }
              _ => pat_elements.push(Some(ArrPatElem {
                target: lit_to_pat(elem)?,
                default_value: None,
              })),
            };
          }
          LitArrElem::Rest(expr) => {
            rest = Some(lit_to_pat(expr)?);
          }
          LitArrElem::Empty => pat_elements.push(None),
        };
      }
      Ok(Node::new(loc, ArrPat {
        elements: pat_elements,
        rest,
      }).into_wrapped())
    }
    Expr::LitObj(n) => {
      let LitObjExpr { members } = *n.stx;
      let mut properties = Vec::new();
      let mut rest: Option<Node<IdPat>> = None;
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
                    (
                      lit_to_pat(left)?,
                      Some(right),
                    )
                  }
                  _ => (
                    lit_to_pat(initializer)?,
                    None,
                  ),
                },
                _ => return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None)),
              };
              properties.push(Node::new(loc, ObjPatProp {
                key,
                target,
                default_value,
                shorthand: true,
              }));
            }
            ObjMemberType::Shorthand { id } => {
              properties.push(Node::new(loc, ObjPatProp {
                key: ClassOrObjKey::Direct(
                  id.derive_stx(|id| ClassOrObjMemberDirectKey { key: id.name.clone(), tt: TT::Identifier }),
                ),
                target: id.derive_stx(|id| IdPat {
                  name: id.name.clone(),
                }).into_wrapped(),
                default_value: None,
                shorthand: true,
              }));
            }
            ObjMemberType::Rest { val: value } => {
              let maybe_rest = lit_to_pat(value)?;
              // The rest element must be an identifier.
              let rest_loc = maybe_rest.loc;
              let Pat::Id(rest_pat) = *maybe_rest.stx else {
                return Err(rest_loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
              };
              rest = Some(rest_pat);
            }
          },
          _ => unreachable!(),
        };
      }
      Ok(Node::new(loc, ObjPat { properties, rest }).into_wrapped())
    }
    Expr::Id(n) => {
      Ok(Node::new(loc, IdPat { name: n.stx.name.clone() }).into_wrapped())
    }
    // It's possible to encounter patterns already parsed e.g. `{a: [b] = 1}`, where `[b]` was already converted to a pattern.
    Expr::IdPat(n) => {
      Ok(n.into_wrapped())
    }
    Expr::ArrPat(n) => {
      Ok(n.into_wrapped())
    }
    Expr::ObjPat(n) => {
      Ok(n.into_wrapped())
    }
    // TypeScript: For any other expression type, wrap it as an assignment target for error recovery
    // This allows destructuring with call expressions, unary operators, etc.
    // The type checker will validate these patterns semantically.
    _ => Ok(Node::new(loc, Pat::AssignTarget(node))),
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
  match lhs.stx.as_ref() {
    e @ (Expr::LitArr(_)
    | Expr::LitObj(_)
    | Expr::Id(_)) => {
      if operator_name != OperatorName::Assignment
        && !matches!(e, Expr::Id(_))
      {
        return Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget));
      }
      // We must transform into a pattern.
      let root = lit_to_pat(lhs)?;
      Ok(root.into_stx())
    }
    // TypeScript: Accept member/computed member expressions for error recovery, even with optional chaining
    // Patterns like `obj?.a = 1` are syntactically parseable but semantically invalid
    // The type checker will validate these
    Expr::ComputedMember(_) => {
      Ok(lhs)
    }
    Expr::Member(_) => {
      Ok(lhs)
    }
    // TypeScript: Accept call expressions, unary expressions, and postfix expressions for error recovery
    // This allows patterns like `foo() = bar`, `++x = 5`, `x++ = 5`, `++x++`, etc.
    // The type checker will reject these, but the parser accepts them.
    Expr::Call(_) | Expr::Unary(_) | Expr::UnaryPostfix(_) => {
      Ok(lhs)
    }
    _ => Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget)),
  }
}
