use emit_js::{emit_interface_decl, ts_type_to_string, EmitMode};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::type_expr::{TypeExpr, TypeMember, TypePropertyKey};
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::{ParseCtx, Parser};
use parse_js::token::TT;
use parse_js::Dialect;
use parse_js::ParseOptions;
use parse_js::SourceType;

fn default_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  }
}

fn default_ctx(opts: &ParseOptions) -> ParseCtx {
  ParseCtx {
    rules: ParsePatternRules {
      await_allowed: !matches!(opts.source_type, SourceType::Module),
      yield_allowed: true,
    },
    top_level: true,
  }
}

fn parse_type_expr(src: &str) -> Node<TypeExpr> {
  let opts = default_opts();
  let mut parser = Parser::new(Lexer::new(src), opts);
  let ty = parser
    .type_expr(default_ctx(&opts))
    .expect("parse type expression");
  parser.require(TT::EOF).expect("expected EOF");
  ty
}

fn parse_interface(src: &str) -> Node<InterfaceDecl> {
  let top = parse_js::parse(src).expect("parse interface");
  let TopLevel { mut body } = *top.stx;
  assert_eq!(body.len(), 1, "expected single statement");
  let stmt = body.pop().unwrap();
  match *stmt.stx {
    Stmt::InterfaceDecl(decl) => decl,
    other => panic!("expected interface declaration, got {other:?}"),
  }
}

fn object_member_key(type_expr: &Node<TypeExpr>) -> &TypePropertyKey {
  match type_expr.stx.as_ref() {
    TypeExpr::ObjectType(literal) => first_member_key(&literal.stx.members),
    other => panic!("expected object type, got {other:?}"),
  }
}

fn interface_member_key(decl: &Node<InterfaceDecl>) -> &TypePropertyKey {
  first_member_key(&decl.stx.members)
}

fn first_member_key(members: &[Node<TypeMember>]) -> &TypePropertyKey {
  let member = members.first().expect("missing member");
  match member.stx.as_ref() {
    TypeMember::Property(sig) => &sig.stx.key,
    other => panic!("expected property signature, got {other:?}"),
  }
}

fn expect_identifier(key: &TypePropertyKey) {
  match key {
    TypePropertyKey::Identifier(actual) => assert_eq!(actual, "foo"),
    other => panic!("expected identifier key, got {other:?}"),
  }
}

fn expect_string(key: &TypePropertyKey) {
  match key {
    TypePropertyKey::String(actual) => assert_eq!(actual, "x"),
    other => panic!("expected string key, got {other:?}"),
  }
}

fn expect_number(key: &TypePropertyKey) {
  match key {
    TypePropertyKey::Number(actual) => assert_eq!(actual, "1"),
    other => panic!("expected number key, got {other:?}"),
  }
}

fn expect_computed(key: &TypePropertyKey) {
  if matches!(key, TypePropertyKey::Computed(_)) {
    return;
  }
  panic!("expected computed key, got {key:?}");
}

fn check_object_case(src: &str, expected: &str, assert_key: impl Fn(&TypePropertyKey)) {
  let parsed = parse_type_expr(src);
  assert_key(object_member_key(&parsed));

  let out = ts_type_to_string(&parsed, EmitMode::Canonical);
  assert_eq!(out, expected);

  let reparsed = parse_type_expr(&out);
  assert_key(object_member_key(&reparsed));
}

fn check_interface_case(src: &str, expected: &str, assert_key: impl Fn(&TypePropertyKey)) {
  let parsed = parse_interface(src);
  assert_key(interface_member_key(&parsed));

  let mut out = String::new();
  emit_interface_decl(&mut out, parsed.stx.as_ref()).expect("emit interface");
  assert_eq!(out, expected);

  let reparsed = parse_interface(&out);
  assert_key(interface_member_key(&reparsed));
}

#[test]
fn emits_identifier_property_keys() {
  check_object_case("{foo:string}", "{foo: string;}", expect_identifier);
  check_interface_case(
    "interface I{foo:string}",
    "interface I {foo: string;}",
    expect_identifier,
  );
}

#[test]
fn emits_string_property_keys() {
  check_object_case("{\"x\":number}", "{\"x\": number;}", expect_string);
  check_interface_case(
    "interface I{\"x\":number}",
    "interface I {\"x\": number;}",
    expect_string,
  );
}

#[test]
fn emits_numeric_property_keys() {
  check_object_case("{1:boolean}", "{1: boolean;}", expect_number);
  check_interface_case(
    "interface I{1:boolean}",
    "interface I {1: boolean;}",
    expect_number,
  );
}

#[test]
fn emits_computed_property_keys() {
  check_object_case("{[foo]?:T}", "{[foo]?: T;}", expect_computed);
  check_interface_case(
    "interface I{[foo]?:T}",
    "interface I {[foo]?: T;}",
    expect_computed,
  );
}
