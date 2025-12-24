use emit_js::emit_type_alias_decl;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::TypeAliasDecl;

fn parse_type_alias(source: &str) -> Node<TypeAliasDecl> {
  let parsed = parse_js::parse(source).expect("parse");
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

fn roundtrip(source: &str, expected: &str) {
  let printed = emit_type_alias_to_string(&parse_type_alias(source));
  assert_eq!(printed, expected);

  let reprinted = emit_type_alias_to_string(&parse_type_alias(&printed));
  assert_eq!(reprinted, expected);
}

#[test]
fn emits_unnamed_single_param_function_type() {
  roundtrip("type F = (string)=>void", "type F = (string) => void;");
}

#[test]
fn emits_multiple_unnamed_params_function_type() {
  roundtrip(
    "type G = (string, number)=>string;",
    "type G = (string, number) => string;",
  );
}

#[test]
fn emits_mixed_named_and_unnamed_params_function_type() {
  roundtrip(
    "type H = (x: string, number)=>void;",
    "type H = (x: string, number) => void;",
  );
}
