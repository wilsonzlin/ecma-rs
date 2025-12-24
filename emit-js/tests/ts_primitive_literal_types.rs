use emit_js::emit_type_alias_decl;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::TypeAliasDecl;

fn parse_type_alias(source: &str) -> Node<TypeAliasDecl> {
  let parsed = parse_js::parse(source).expect("parse failed");
  let TopLevel { body } = *parsed.stx;
  for stmt in body {
    if let Stmt::TypeAliasDecl(alias) = *stmt.stx {
      return alias;
    }
  }
  panic!("missing type alias");
}

fn emit_type_alias_to_string(decl: &Node<TypeAliasDecl>) -> String {
  let mut out = String::new();
  emit_type_alias_decl(&mut out, decl.stx.as_ref()).expect("emit type alias");
  out
}

fn roundtrip(src: &str, expected: &str) {
  let decl = parse_type_alias(src);
  let emitted = emit_type_alias_to_string(&decl);
  assert_eq!(emitted, expected);

  // Ensure the emitted output is stable under repeated emit cycles.
  let emitted_again = emit_type_alias_to_string(&parse_type_alias(&emitted));
  assert_eq!(emitted_again, expected);
}

#[test]
fn primitive_keyword_types_roundtrip() {
  let cases = [
    ("type T = any;", "type T = any;"),
    ("type T = unknown;", "type T = unknown;"),
    ("type T = never;", "type T = never;"),
    ("type T = void;", "type T = void;"),
    ("type T = string", "type T = string;"),
    ("type T = number", "type T = number;"),
    ("type T = boolean", "type T = boolean;"),
    ("type T = bigint", "type T = bigint;"),
    ("type T = symbol", "type T = symbol;"),
    ("type T = unique symbol", "type T = unique symbol;"),
    ("type T = object", "type T = object;"),
    ("type T = null", "type T = null;"),
    ("type T = undefined", "type T = undefined;"),
    ("type T = this", "type T = this;"),
  ];

  for (src, expected) in cases {
    roundtrip(src, expected);
  }
}

#[test]
fn literal_types_roundtrip() {
  let cases = [
    ("type T = 'hello';", r#"type T = "hello";"#),
    (r#"type T = "a\\b\"c";"#, r#"type T = "a\\b\"c";"#),
    ("type T = 123;", "type T = 123;"),
    ("type T = -123;", "type T = -123;"),
    ("type T = 1.5;", "type T = 1.5;"),
    ("type T = 123n;", "type T = 123n;"),
    ("type T = -123n;", "type T = -123n;"),
    ("type T = true;", "type T = true;"),
    ("type T = false;", "type T = false;"),
  ];

  for (src, expected) in cases {
    roundtrip(src, expected);
  }
}

