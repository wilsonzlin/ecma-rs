use emit_js::emit_type_expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::TypeExpr;

fn parse_type_expr(src_type: &str) -> Node<TypeExpr> {
  let src = format!("type X = {};", src_type);
  let top = parse_js::parse(&src).expect("parse failed");
  let TopLevel { mut body } = *top.stx;
  let stmt = body.pop().expect("expected a statement");
  match *stmt.stx {
    Stmt::TypeAliasDecl(type_alias) => type_alias.stx.type_expr,
    other => panic!("unexpected statement: {:?}", other),
  }
}

fn emit_type_expr_to_string(node: &Node<TypeExpr>) -> String {
  let mut out = String::new();
  emit_type_expr(&mut out, node).expect("emit should succeed");
  out
}

fn roundtrip_type_expr(src_type: &str) {
  let original = parse_type_expr(src_type);
  let emitted = emit_type_expr_to_string(&original);
  let reparsed = parse_type_expr(&emitted);

  let left = serde_json::to_value(&original).expect("serialize original");
  let right = serde_json::to_value(&reparsed).expect("serialize reparsed");
  assert_eq!(
    left, right,
    "roundtrip mismatch for `{}` => `{}`",
    src_type, emitted
  );
}

#[test]
fn precedence_parentheses_and_unions() {
  let cases = [
    ("A|B&C", "A | B & C"),
    ("(A|B)&C", "(A | B) & C"),
    ("(A|B)[]", "(A | B)[]"),
    ("A|B[]", "A | B[]"),
    ("T[K]", "T[K]"),
    ("(A|B)[K]", "(A | B)[K]"),
    ("T extends U ? X : Y", "T extends U ? X : Y"),
    ("(T extends U ? X : Y)|Z", "(T extends U ? X : Y) | Z"),
    ("()=>string|number", "() => string | number"),
    ("(()=>string)|number", "(() => string) | number"),
    ("(new()=>T)|U", "(new () => T) | U"),
    ("(new()=>T)[]", "(new () => T)[]"),
    ("keyof(A|B)", "keyof (A | B)"),
  ];

  for (input, expected) in cases {
    let parsed = parse_type_expr(input);
    let printed = emit_type_expr_to_string(&parsed);
    assert_eq!(printed, expected, "case `{}`", input);
    roundtrip_type_expr(input);
  }
}

