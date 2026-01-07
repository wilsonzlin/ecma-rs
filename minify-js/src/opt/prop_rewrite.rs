use super::{OptCtx, Pass};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::class_or_object::{
  ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::lit::{LitNullExpr, LitNumExpr};
use parse_js::ast::expr::{ComputedMemberExpr, Expr, MemberExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::lex::{lex_next, LexMode, Lexer};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::token::TT;
use parse_js::Dialect;

pub(super) struct PropRewritePass;

impl Pass for PropRewritePass {
  fn name(&self) -> &'static str {
    "prop-rewrite"
  }

  fn run(&mut self, _cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    let mut visitor = PropRewriteVisitor { changed: false };
    top.drive_mut(&mut visitor);
    visitor.changed
  }
}

type ExprNode = Node<Expr>;
type ObjMemberNode = Node<ObjMember>;

#[derive(VisitorMut)]
#[visitor(ExprNode(exit), ObjMemberNode(exit))]
struct PropRewriteVisitor {
  changed: bool,
}

impl PropRewriteVisitor {
  fn exit_expr_node(&mut self, node: &mut ExprNode) {
    let Expr::ComputedMember(_) = node.stx.as_ref() else {
      return;
    };

    let dummy = dummy_expr(node.loc);
    let expr = std::mem::replace(&mut *node.stx, dummy);
    let Expr::ComputedMember(member) = expr else {
      *node.stx = expr;
      return;
    };

    let (replacement, changed) = simplify_computed_member(member, node.loc);
    self.changed |= changed;
    *node.stx = replacement;
  }

  fn exit_obj_member_node(&mut self, node: &mut ObjMemberNode) {
    let dummy = dummy_obj_member_type();
    let typ = std::mem::replace(&mut node.stx.typ, dummy);
    let (typ, changed) = simplify_object_member_key(typ);
    node.stx.typ = typ;
    self.changed |= changed;
  }
}

fn simplify_computed_member(member: Node<ComputedMemberExpr>, loc: Loc) -> (Expr, bool) {
  let mut member = member;
  let Expr::LitStr(lit) = member.stx.member.stx.as_ref() else {
    return (Expr::ComputedMember(member), false);
  };

  let key = lit.stx.value.as_str();

  if is_identifier_name_token(key) {
    return (
      Expr::Member(Node::new(
        loc,
        MemberExpr {
          optional_chaining: member.stx.optional_chaining,
          left: member.stx.object,
          right: key.to_string(),
        },
      )),
      true,
    );
  }

  if let Some(idx) = parse_canonical_u32_index(key) {
    member.stx.member = Node::new(
      member.stx.member.loc,
      Expr::LitNum(Node::new(
        member.stx.member.loc,
        LitNumExpr {
          value: JsNumber(idx as f64),
        },
      )),
    );
    return (Expr::ComputedMember(member), true);
  }

  (Expr::ComputedMember(member), false)
}

fn simplify_object_member_key(typ: ObjMemberType) -> (ObjMemberType, bool) {
  let ObjMemberType::Valued { key, val } = typ else {
    return (typ, false);
  };

  let (key, changed) = simplify_object_literal_key(key);
  (ObjMemberType::Valued { key, val }, changed)
}

fn simplify_object_literal_key(key: ClassOrObjKey) -> (ClassOrObjKey, bool) {
  match key {
    ClassOrObjKey::Direct(mut direct) => {
      if direct.stx.tt != TT::LiteralString {
        return (ClassOrObjKey::Direct(direct), false);
      }

      if let Some(tt) = identifier_name_token_tt(&direct.stx.key) {
        direct.stx.tt = tt;
        return (ClassOrObjKey::Direct(direct), true);
      }

      if let Some(idx) = parse_canonical_u32_index(&direct.stx.key) {
        direct.stx.key = idx.to_string();
        direct.stx.tt = TT::LiteralNumber;
        return (ClassOrObjKey::Direct(direct), true);
      }

      (ClassOrObjKey::Direct(direct), false)
    }
    ClassOrObjKey::Computed(expr) => {
      match expr.stx.as_ref() {
        Expr::LitStr(lit) => {
          let key = lit.stx.value.as_str();
          // `{["__proto__"]: ... }` defines a normal data property, while
          // `{__proto__: ... }` can change the object's prototype.
          if key == "__proto__" {
            return (ClassOrObjKey::Computed(expr), false);
          }

          let (tt, key) = if let Some(tt) = identifier_name_token_tt(key) {
            (tt, key.to_string())
          } else if let Some(idx) = parse_canonical_u32_index(key) {
            (TT::LiteralNumber, idx.to_string())
          } else {
            (TT::LiteralString, key.to_string())
          };

          (
            ClassOrObjKey::Direct(Node::new(
              expr.loc,
              ClassOrObjMemberDirectKey { key, tt },
            )),
            true,
          )
        }
        Expr::LitNum(num) => (
          ClassOrObjKey::Direct(Node::new(
            expr.loc,
            ClassOrObjMemberDirectKey {
              key: num.stx.value.to_string(),
              tt: TT::LiteralNumber,
            },
          )),
          true,
        ),
        _ => (ClassOrObjKey::Computed(expr), false),
      }
    }
  }
}

fn try_shorthand_prop(typ: ObjMemberType) -> (ObjMemberType, bool) {
  let ObjMemberType::Valued { key, val } = typ else {
    return (typ, false);
  };

  let key = match key {
    ClassOrObjKey::Direct(key) => key,
    other => return (ObjMemberType::Valued { key: other, val }, false),
  };

  if key.stx.key == "__proto__" {
    return (
      ObjMemberType::Valued {
        key: ClassOrObjKey::Direct(key),
        val,
      },
      false,
    );
  }

  let val = match val {
    ClassOrObjVal::Prop(Some(expr)) => expr,
    other => {
      return (
        ObjMemberType::Valued {
          key: ClassOrObjKey::Direct(key),
          val: other,
        },
        false,
      );
    }
  };

  let is_shorthand_candidate =
    matches!(val.stx.as_ref(), Expr::Id(id) if id.stx.name == key.stx.key);
  if !is_shorthand_candidate {
    return (
      ObjMemberType::Valued {
        key: ClassOrObjKey::Direct(key),
        val: ClassOrObjVal::Prop(Some(val)),
      },
      false,
    );
  }

  let Expr::Id(id) = *val.stx else {
    unreachable!("shorthand candidate check ensures identifier expression");
  };
  (ObjMemberType::Shorthand { id }, true)
}

fn is_identifier_name_token(name: &str) -> bool {
  identifier_name_token_tt(name).is_some()
}

fn identifier_name_token_tt(name: &str) -> Option<TT> {
  let mut lexer = Lexer::new(name);
  let token = lex_next(&mut lexer, LexMode::Standard, Dialect::Ts);

  if token.loc.0 != 0 || token.loc.1 != name.len() {
    return None;
  }

  if matches!(
    token.typ,
    TT::Identifier | TT::LiteralFalse | TT::LiteralTrue | TT::LiteralNull
  ) || token.typ.is_keyword()
  {
    return Some(token.typ);
  }

  None
}

fn parse_canonical_u32_index(value: &str) -> Option<u32> {
  if value.is_empty() {
    return None;
  }

  let bytes = value.as_bytes();
  if bytes.len() > 1 && bytes[0] == b'0' {
    return None;
  }
  if !bytes.iter().all(|b| b.is_ascii_digit()) {
    return None;
  }

  let parsed: u32 = value.parse().ok()?;
  if parsed.to_string() != value {
    return None;
  }
  Some(parsed)
}

fn dummy_expr(loc: Loc) -> Expr {
  Expr::LitNull(Node::new(loc, LitNullExpr {}))
}

fn dummy_obj_member_type() -> ObjMemberType {
  ObjMemberType::Rest {
    val: Node::new(Loc(0, 0), dummy_expr(Loc(0, 0))),
  }
}

pub(crate) fn rewrite_object_shorthand_props(top: &mut Node<TopLevel>) -> bool {
  type ObjMemberNode = Node<ObjMember>;

  #[derive(VisitorMut)]
  #[visitor(ObjMemberNode(exit))]
  struct ShorthandVisitor {
    changed: bool,
  }

  impl ShorthandVisitor {
    fn exit_obj_member_node(&mut self, node: &mut ObjMemberNode) {
      let dummy = dummy_obj_member_type();
      let typ = std::mem::replace(&mut node.stx.typ, dummy);
      let (typ, changed) = try_shorthand_prop(typ);
      node.stx.typ = typ;
      self.changed |= changed;
    }
  }

  let mut visitor = ShorthandVisitor { changed: false };
  top.drive_mut(&mut visitor);
  visitor.changed
}
