use emit_js::emit_top_level_stmt;
use emit_js::emit_type_alias_decl;
use emit_js::EmitOptions;
use emit_js::Emitter;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::TypeAliasDecl;

fn parse_type_alias(src: &str) -> Node<TypeAliasDecl> {
  let top = parse_js::parse(src).expect("parse failed");
  let TopLevel { mut body } = *top.stx;
  let stmt = body.pop().expect("expected a statement");
  match *stmt.stx {
    Stmt::TypeAliasDecl(type_alias) => type_alias,
    other => panic!("unexpected statement: {:?}", other),
  }
}

fn emit_type_alias_to_string(decl: &Node<TypeAliasDecl>) -> String {
  let mut out = String::new();
  emit_type_alias_decl(&mut out, decl.stx.as_ref()).expect("emit should succeed");
  out
}

#[test]
fn type_alias_roundtrip() {
  let alias = parse_type_alias("type Foo<T extends U = V> = T | U;");
  let emitted = emit_type_alias_to_string(&alias);
  assert_eq!(emitted, "type Foo<T extends U = V> = T | U;");

  let reparsed = parse_type_alias(&emitted);
  assert_eq!(alias.stx.name, reparsed.stx.name);
  assert_eq!(alias.stx.export, reparsed.stx.export);
  assert_eq!(alias.stx.declare, reparsed.stx.declare);
  let re_emitted = emit_type_alias_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}

fn normalized_stmts(top: &Node<TopLevel>) -> Vec<String> {
  fn scrub_locs(value: String) -> String {
    let mut out = String::with_capacity(value.len());
    let mut rest = value.as_str();
    while let Some(idx) = rest.find("Loc(") {
      out.push_str(&rest[..idx]);
      out.push_str("Loc(..)");
      rest = &rest[idx + "Loc(".len()..];
      match rest.find(')') {
        Some(end) => rest = &rest[end + 1..],
        None => {
          out.push_str(rest);
          return out;
        }
      }
    }
    out.push_str(rest);
    out
  }

  top
    .stx
    .body
    .iter()
    .filter(|stmt| !matches!(stmt.stx.as_ref(), Stmt::Empty(_)))
    .map(|stmt| scrub_locs(format!("{:#?}", stmt.stx)))
    .collect()
}

#[test]
fn emitter_roundtrips_ts_statements() {
  let source = r#"
    export declare interface Foo<T> extends Bar {
      readonly x?: string;
    }
    declare namespace A.B.C {
      interface Nested {}
    }
    declare module "x" { type Foo = string }
    declare global { interface Foo {} }
    export type T = string | number;
    const enum E { A = 1, B }
    declare var v: Foo;
    declare function fn<T>(arg?: T): void;
    declare abstract class Cls<T> extends Base<T> implements Foo<T> {}
    import type { Foo as FooType, Bar } from "mod";
    export type { FooType as FooExport } from "mod2";
    export import Alias = require("pkg");
    export = v;
  "#;

  let top: Node<TopLevel> = parse_js::parse(source).expect("parse failed");

  let mut emitter = Emitter::new(EmitOptions::default());
  emit_top_level_stmt(&mut emitter, top.stx.as_ref()).expect("emit");
  let output = String::from_utf8(emitter.into_bytes()).expect("utf-8 output");

  let reparsed = parse_js::parse(&output).expect("reparse emitted code");

  assert_eq!(normalized_stmts(&top), normalized_stmts(&reparsed));
}
