use emit_js::{emit_param_decl, emit_pat, emit_pat_decl};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjMemberDirectKey};
use parse_js::ast::expr::lit::LitNumExpr;
use parse_js::ast::expr::pat::{ArrPat, ArrPatElem, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::expr::{Expr, IdExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, ParamDecl};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::token::TT;

fn dummy_loc() -> Loc {
  Loc(0, 0)
}

fn id_pat(name: &str) -> Node<Pat> {
  Node::new(dummy_loc(), Pat::Id(Node::new(dummy_loc(), IdPat { name: name.into() })))
}

fn id_expr(name: &str) -> Node<Expr> {
  Node::new(dummy_loc(), Expr::Id(Node::new(dummy_loc(), IdExpr { name: name.into() })))
}

fn num_expr(value: f64) -> Node<Expr> {
  Node::new(
    dummy_loc(),
    Expr::LitNum(Node::new(
      dummy_loc(),
      LitNumExpr {
        value: JsNumber(value),
      },
    )),
  )
}

fn direct_key(name: &str) -> ClassOrObjKey {
  ClassOrObjKey::Direct(Node::new(
    dummy_loc(),
    ClassOrObjMemberDirectKey {
      key: name.into(),
      tt: TT::Identifier,
    },
  ))
}

fn emit_pat_to_string(pat: &Node<Pat>) -> String {
  let mut out = String::new();
  emit_pat(&mut out, pat).unwrap();
  out
}

#[test]
fn emits_array_pattern_with_elisions_and_rest() {
  let pattern = Node::new(
    dummy_loc(),
    Pat::Arr(Node::new(
      dummy_loc(),
      ArrPat {
        elements: vec![None, Some(ArrPatElem {
          target: id_pat("a"),
          default_value: None,
        }), None],
        rest: Some(id_pat("b")),
      },
    )),
  );

  assert_eq!(emit_pat_to_string(&pattern), "[,a,,...b]");
}

#[test]
fn emits_object_pattern_with_defaults_rest_and_computed_keys() {
  let properties = vec![
    Node::new(
      dummy_loc(),
      ObjPatProp {
        key: direct_key("a"),
        target: id_pat("a"),
        shorthand: true,
        default_value: None,
      },
    ),
    Node::new(
      dummy_loc(),
      ObjPatProp {
        key: direct_key("b"),
        target: id_pat("c"),
        shorthand: false,
        default_value: Some(num_expr(1.0)),
      },
    ),
    Node::new(
      dummy_loc(),
      ObjPatProp {
        key: ClassOrObjKey::Computed(id_expr("d")),
        target: id_pat("e"),
        shorthand: false,
        default_value: None,
      },
    ),
  ];

  let pattern = Node::new(
    dummy_loc(),
    Pat::Obj(Node::new(
      dummy_loc(),
      ObjPat {
        properties,
        rest: Some(id_pat("rest")),
      },
    )),
  );

  assert_eq!(emit_pat_to_string(&pattern), "{a,b:c=1,[d]:e,...rest}");
}

#[test]
fn emits_nested_patterns_with_defaults() {
  let nested_array = Node::new(
    dummy_loc(),
    Pat::Arr(Node::new(
      dummy_loc(),
      ArrPat {
        elements: vec![Some(ArrPatElem {
          target: id_pat("b"),
          default_value: Some(id_expr("c")),
        })],
        rest: None,
      },
    )),
  );

  let object = Node::new(
    dummy_loc(),
    Pat::Obj(Node::new(
      dummy_loc(),
      ObjPat {
        properties: vec![Node::new(
          dummy_loc(),
          ObjPatProp {
            key: direct_key("a"),
            target: nested_array,
            shorthand: false,
            default_value: None,
          },
        )],
        rest: None,
      },
    )),
  );

  let pattern = Node::new(
    dummy_loc(),
    Pat::Arr(Node::new(
      dummy_loc(),
      ArrPat {
        elements: vec![Some(ArrPatElem {
          target: object,
          default_value: Some(id_expr("d")),
        })],
        rest: None,
      },
    )),
  );

  assert_eq!(emit_pat_to_string(&pattern), "[{a:[b=c]}=d]");
}

#[test]
fn emits_pat_decl_wrapper() {
  let decl = Node::new(dummy_loc(), PatDecl { pat: id_pat("x") });
  let mut out = String::new();
  emit_pat_decl(&mut out, &decl).unwrap();
  assert_eq!(out, "x");
}

#[test]
fn emits_param_decl_with_rest() {
  let param = Node::new(
    dummy_loc(),
    ParamDecl {
      decorators: Vec::new(),
      rest: true,
      optional: false,
      accessibility: None,
      readonly: false,
      pattern: Node::new(dummy_loc(), PatDecl { pat: id_pat("args") }),
      type_annotation: None,
      default_value: None,
    },
  );
  let mut out = String::new();
  emit_param_decl(&mut out, &param).unwrap();
  assert_eq!(out, "...args");
}

#[test]
fn emits_assignment_target_pattern() {
  let pat = Node::new(dummy_loc(), Pat::AssignTarget(id_expr("value")));
  assert_eq!(emit_pat_to_string(&pat), "value");
}

