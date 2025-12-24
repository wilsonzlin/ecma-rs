use emit_js::{emit_interface_decl, emit_type_expr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::ParseCtx;
use parse_js::parse::Parser;
use parse_js::token::TT;
use parse_js::Dialect;
use parse_js::ParseOptions;
use parse_js::SourceType;

fn parse_type_expr(src: &str) -> Node<TypeExpr> {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(src), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: !matches!(opts.source_type, SourceType::Module),
      yield_allowed: true,
    },
  };
  let expr = parser.type_expr(ctx).expect("parse type expression");
  parser.require(TT::EOF).expect("exhaust input");
  expr
}

fn parse_interface(src: &str) -> Node<InterfaceDecl> {
  let top = parse_js::parse(src).expect("parse interface");
  let TopLevel { mut body } = *top.stx;
  let first = body.remove(0);
  match *first.stx {
    Stmt::InterfaceDecl(interface) => interface,
    _ => panic!("expected interface declaration"),
  }
}

fn emit_type_expr_to_string(node: &Node<TypeExpr>) -> String {
  let mut out = String::new();
  emit_type_expr(&mut out, node).expect("emit type");
  out
}

fn assert_emit_type(src: &str, expected: &str) {
  let parsed = parse_type_expr(src);
  let emitted = emit_type_expr_to_string(&parsed);
  assert_eq!(emitted, expected);

  let roundtrip = emit_type_expr_to_string(&parse_type_expr(&emitted));
  assert_eq!(roundtrip, expected);
}

#[test]
fn emits_mapped_types() {
  assert_emit_type("{ [ K in keyof T ] : T [ K ] }", "{ [K in keyof T]: T[K] }");
  assert_emit_type("{ readonly [K in T] ? : U }", "{ readonly [K in T]?: U }");
  assert_emit_type(
    "{ +readonly [ K in T as NewK ] -? : U }",
    "{ +readonly [K in T as NewK]-?: U }",
  );
}

#[test]
fn emits_mapped_members_in_interfaces() {
  let parsed = parse_interface("interface I { [ K in keyof T ] : T[K]; foo : string }");
  let mut out = String::new();
  emit_interface_decl(&mut out, parsed.stx.as_ref()).expect("emit interface");
  assert_eq!(out, "interface I {[K in keyof T]: T[K]; foo: string;}");

  let roundtrip = {
    let reparsed = parse_interface(&out);
    let mut buf = String::new();
    emit_interface_decl(&mut buf, reparsed.stx.as_ref()).expect("emit interface roundtrip");
    buf
  };
  assert_eq!(
    roundtrip,
    "interface I {[K in keyof T]: T[K]; foo: string;}"
  );
}
