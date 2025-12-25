use emit_js::{emit_expr, emit_jsx_elem, EmitOptions, Emitter};
use parse_js::ast::expr::jsx::*;
use parse_js::ast::expr::{Expr, IdExpr};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::loc::Loc;
use std::fmt;

fn id_expr(name: &str) -> Node<IdExpr> {
  let len = name.len();
  Node::new(Loc(0, len), IdExpr { name: name.into() })
}

fn expr_from_id(name: &str) -> Node<Expr> {
  let ident = id_expr(name);
  Node::new(ident.loc, Expr::Id(ident))
}

fn jsx_text(value: &str) -> Node<JsxText> {
  Node::new(
    Loc(0, value.len()),
    JsxText {
      value: value.into(),
    },
  )
}

fn jsx_elem_from(
  name: Option<JsxElemName>,
  attributes: Vec<JsxAttr>,
  children: Vec<JsxElemChild>,
) -> Node<JsxElem> {
  Node::new(
    Loc(0, 0),
    JsxElem {
      name,
      attributes,
      children,
    },
  )
}

fn emit_elem_to_string(elem: &Node<JsxElem>) -> String {
  let mut emitter = Emitter::default();
  emit_jsx_elem(&mut emitter, elem).unwrap();
  String::from_utf8(emitter.into_bytes()).unwrap()
}

struct EmitterWriter<'a> {
  emitter: &'a mut Emitter,
}

impl fmt::Write for EmitterWriter<'_> {
  fn write_str(&mut self, s: &str) -> fmt::Result {
    self.emitter.write_str(s);
    Ok(())
  }
}

fn emit_elem_with_emitter_to_string(elem: &Node<JsxElem>) -> String {
  let mut emitter = Emitter::new(EmitOptions::default());
  {
    let mut writer = EmitterWriter {
      emitter: &mut emitter,
    };
    emit_jsx_elem(&mut writer, elem).unwrap();
  }
  String::from_utf8(emitter.into_bytes()).unwrap()
}

fn emit_expr_to_string(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr(&mut out, expr, &mut emit_type).unwrap();
  out
}

fn div_elem_name() -> JsxElemName {
  JsxElemName::Name(Node::new(
    Loc(0, 3),
    JsxName {
      namespace: None,
      name: "div".into(),
    },
  ))
}

fn empty_attr_placeholder_expr() -> Node<Expr> {
  let loc = Loc(0, 0);
  let empty_id = Node::new(
    loc,
    IdExpr {
      name: String::new(),
    },
  );
  Node::new(loc, Expr::Id(empty_id))
}

fn jsx_container(value: Node<Expr>, spread: bool) -> Node<JsxExprContainer> {
  Node::new(value.loc, JsxExprContainer { spread, value })
}

#[test]
fn emits_fragments() {
  let empty = jsx_elem_from(None, vec![], vec![]);
  assert_eq!(emit_elem_to_string(&empty), "<></>");

  let with_child = jsx_elem_from(None, vec![], vec![JsxElemChild::Text(jsx_text("x"))]);
  assert_eq!(emit_elem_to_string(&with_child), "<>x</>");
}

#[test]
fn emits_element_names() {
  let div = jsx_elem_from(
    Some(JsxElemName::Name(Node::new(
      Loc(0, 3),
      JsxName {
        namespace: None,
        name: "div".into(),
      },
    ))),
    vec![],
    vec![],
  );
  assert_eq!(
    emit_expr_to_string(&Node::new(div.loc, Expr::JsxElem(div))),
    "<div/>"
  );

  let ns = jsx_elem_from(
    Some(JsxElemName::Name(Node::new(
      Loc(0, 6),
      JsxName {
        namespace: Some("ns".into()),
        name: "div".into(),
      },
    ))),
    vec![],
    vec![],
  );
  assert_eq!(
    emit_expr_to_string(&Node::new(ns.loc, Expr::JsxElem(ns))),
    "<ns:div/>"
  );

  let id = jsx_elem_from(Some(JsxElemName::Id(id_expr("Foo"))), vec![], vec![]);
  assert_eq!(
    emit_expr_to_string(&Node::new(id.loc, Expr::JsxElem(id))),
    "<Foo/>"
  );

  let member = jsx_elem_from(
    Some(JsxElemName::Member(Node::new(
      Loc(0, 0),
      JsxMemberExpr {
        base: id_expr("Foo"),
        path: vec!["Bar".into(), "Baz".into()],
      },
    ))),
    vec![],
    vec![],
  );
  assert_eq!(
    emit_expr_to_string(&Node::new(member.loc, Expr::JsxElem(member))),
    "<Foo.Bar.Baz/>"
  );
}

#[test]
fn emits_attributes() {
  let boolean = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "disabled".into(),
        },
      ),
      value: None,
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&boolean), "<div disabled/>");

  let string_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("hello"))),
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&string_attr), "<div title=\"hello\"/>");

  let quote_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("She said \"hi\""))),
    }],
    vec![],
  );
  assert_eq!(
    emit_elem_to_string(&quote_attr),
    "<div title=\"She said &quot;hi&quot;\"/>"
  );

  let newline_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("\n"))),
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&newline_attr), "<div title=\"&#xA;\"/>");

  let nul_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("\u{0}"))),
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&nul_attr), "<div title=\"&#0;\"/>");

  let spread_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Spread {
      value: Node::new(
        Loc(0, 0),
        JsxSpreadAttr {
          value: expr_from_id("props"),
        },
      ),
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&spread_attr), "<div {...props}/>");

  let empty_expr_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "a".into(),
        },
      ),
      value: Some(JsxAttrVal::Expression(jsx_container(empty_attr_placeholder_expr(), false))),
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&empty_expr_attr), "<div a={}/>");

  let elem_attr_value = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "a".into(),
        },
      ),
      value: Some(JsxAttrVal::Element(jsx_elem_from(
        Some(JsxElemName::Name(Node::new(
          Loc(0, 4),
          JsxName {
            namespace: None,
            name: "span".into(),
          },
        ))),
        vec![],
        vec![],
      ))),
    }],
    vec![],
  );
  assert_eq!(emit_elem_to_string(&elem_attr_value), "<div a=<span/>/>");

  let lt_after_text = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("a<b"))),
    }],
    vec![],
  );
  assert_eq!(
    emit_elem_to_string(&lt_after_text),
    "<div title=\"a<b\"/>"
  );
}

#[test]
fn emitter_does_not_insert_spaces_in_text_attributes() {
  let string_attr = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("ab"))),
    }],
    vec![],
  );
  assert_eq!(
    emit_elem_with_emitter_to_string(&string_attr),
    "<div title=\"ab\"/>"
  );
}

#[test]
fn emits_children() {
  let text_child = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![JsxElemChild::Text(jsx_text("hi"))],
  );
  assert_eq!(emit_elem_to_string(&text_child), "<div>hi</div>");

  let expr_child = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![JsxElemChild::Expr(jsx_container(expr_from_id("x"), false))],
  );
  assert_eq!(emit_elem_to_string(&expr_child), "<div>{x}</div>");

  let spread_expr_child = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![JsxElemChild::Expr(jsx_container(expr_from_id("xs"), true))],
  );
  assert_eq!(
    emit_elem_to_string(&spread_expr_child),
    "<div>{...xs}</div>"
  );

  let escaped_child = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![JsxElemChild::Text(jsx_text("<{>}"))],
  );
  assert_eq!(
    emit_elem_to_string(&escaped_child),
    "<div>&lt;&#123;&gt;&#125;</div>"
  );

  let lt_followed_by_text = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![JsxElemChild::Text(jsx_text("<div>"))],
  );
  assert_eq!(
    emit_elem_to_string(&lt_followed_by_text),
    "<div>&lt;div&gt;</div>"
  );
}

#[test]
fn emits_unicode_text_and_attributes() {
  let unicode = jsx_elem_from(
    Some(div_elem_name()),
    vec![JsxAttr::Named {
      name: Node::new(
        Loc(0, 0),
        JsxName {
          namespace: None,
          name: "title".into(),
        },
      ),
      value: Some(JsxAttrVal::Text(jsx_text("你好"))),
    }],
    vec![JsxElemChild::Text(jsx_text("你好"))],
  );

  assert_eq!(
    emit_elem_to_string(&unicode),
    "<div title=\"你好\">你好</div>"
  );
}

#[test]
fn emitter_does_not_insert_spaces_between_adjacent_text_children() {
  let elem = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![
      JsxElemChild::Text(jsx_text("a")),
      JsxElemChild::Text(jsx_text("b")),
    ],
  );
  assert_eq!(emit_elem_with_emitter_to_string(&elem), "<div>ab</div>");
}

#[test]
fn emits_adjacent_text_children_without_spaces() {
  let adjacent_text = jsx_elem_from(
    Some(div_elem_name()),
    vec![],
    vec![
      JsxElemChild::Text(jsx_text("a")),
      JsxElemChild::Text(jsx_text("b")),
    ],
  );

  assert_eq!(emit_elem_to_string(&adjacent_text), "<div>ab</div>");
}
