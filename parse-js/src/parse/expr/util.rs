use crate::{ast::{class_or_object::{ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType}, expr::{BinaryExpr, ComputedMemberExpr, Expr, IdExpr, MemberExpr}, expr::lit::{LitArrElem, LitArrExpr, LitObjExpr}, node::Node, expr::pat::{ArrPat, ArrPatElem, IdPat, ObjPat, ObjPatProp, Pat}}, error::{SyntaxErrorType, SyntaxResult}, operator::OperatorName, token::TT};



/// Converts a literal expression subtree into a pattern (assignment target).
/// `{ a: [b] }` could be an object literal or object pattern. This function is useful for when a pattern was misinterpreted as a literal expression, without needing to rewind and reparse.
pub fn lit_to_pat(node: Node<Expr>) -> SyntaxResult<Node<Pat>> {
  let loc = node.loc;
  match *node.stx {
    Expr::LitArr(LitArrExpr { elements }) => {
      let mut pat_elements = Vec::<Option<ArrPatElem>>::new();
      let mut rest = None;
      for element in elements {
        if rest.is_some() {
          return Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None));
        };
        match element {
          LitArrElem::Single(elem) => {
            match *elem.stx {
              Expr::Binary(BinaryExpr {
                operator,
                left,
                right,
              }) => {
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
      Ok(Node::new(loc, Pat::Arr(ArrPat {
        elements: pat_elements,
        rest,
      })))
    }
    Expr::LitObj(LitObjExpr { members }) => {
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
                  Expr::Binary(BinaryExpr {
                    operator,
                    left,
                    right,
                  }) => {
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
            ObjMemberType::Shorthand { id: identifier } => {
              properties.push(Node::new(loc, ObjPatProp {
                key: ClassOrObjKey::Direct(
                  identifier.derive_stx(|id| ClassOrObjMemberDirectKey { key: id.name.clone(), tt: TT::Identifier }),
                ),
                target: identifier.derive_stx(|id| Pat::Id(IdPat {
                  name: id.name.clone(),
                })),
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
              rest = Some(Node::new(rest_loc, rest_pat));
            }
          },
          _ => unreachable!(),
        };
      }
      Ok(Node::new(loc, Pat::Obj(ObjPat { properties, rest })))
    }
    // It's possible to encounter an IdPat e.g. `{ a: b = 1 } = x`, where `b = 1` was already parsed as an assignment.
    Expr::Id(IdExpr { name }) | Expr::IdPat(IdPat { name }) => {
      Ok(Node::new(loc, Pat::Id(IdPat {
        name: name.clone(),
      })))
    }
    _ => Err(loc.error(SyntaxErrorType::InvalidAssigmentTarget, None)),
  }
}


// Trying to check if every object, array, or identifier expression operand is actually an assignment target first is too expensive and wasteful, so simply retroactively transform the LHS of a BinaryExpr with Assignment* operator into a target, raising an error if it can't (and is an invalid assignment target). A valid target is:
// - A chain of non-optional-chaining member, computed member, and call operators, not ending in a call.
// - A pattern.
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
    Expr::ComputedMember(ComputedMemberExpr {
      optional_chaining, ..
    })
    | Expr::Member(MemberExpr {
      optional_chaining, ..
    }) if !optional_chaining => {
      // As long as the expression ends with ComputedMemberExpr or MemberExpr, it's valid e.g. `(a, b?.a ?? 3, c = d || {})[1] = x`. Note that this is after parsing, so `a + b.c = 3` is invalid because that parses to `(a + b.c) = 3`, with a LHS of BinaryExpr with Addition operator.
      // TODO Technically there cannot be any optional chaining in the entire access/call path, not just in the last part (e.g. `a.b?.c.d = e` is invalid).
      Ok(lhs)
    }
    _ => Err(lhs.error(SyntaxErrorType::InvalidAssigmentTarget)),
  }
}
