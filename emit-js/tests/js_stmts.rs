use emit_js::{emit_stmt_top_level, Emitter};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use serde_json::Value;

fn emit(source: &str) -> String {
  let parsed = parse_js::parse(source).expect("parse failure");
  let mut emitter = Emitter::default();
  emit_stmt_top_level(&mut emitter, &parsed).expect("emit failure");
  String::from_utf8(emitter.into_bytes()).expect("utf-8")
}

fn ast_value(top: &Node<TopLevel>) -> Value {
  serde_json::to_value(top).expect("serialize")
}

#[test]
fn emits_expression_statement_with_parens() {
  assert_eq!(emit("({a:1});"), "({a:1});");
}

#[test]
fn emits_control_flow_statements() {
  let src = "if (test) foo(); else bar(); while (flag) foo(); do { bar(); } while (flag);";
  let expected = "if(test)foo();else bar();while(flag)foo();do{bar();}while(flag);";
  assert_eq!(emit(src), expected);
}

#[test]
fn emits_loops() {
  let src =
    "for (let i = 0;;) break; for (const k in obj) continue; for await (const v of values) break;";
  let expected =
    "for(let i=0;;)break;for(const k in obj)continue;for await(const v of values)break;";
  assert_eq!(emit(src), expected);
}

#[test]
fn emits_switch_try_and_labels() {
  let src = r#"
    switch (value) { case 1: break; default: throw value; }
    try { work(); } catch (err) { handle(); } finally { cleanup(); }
    label: while (flag) break label;
  "#;
  let expected = concat!(
    "switch(value){case 1:break;default:throw value;}",
    "try{work();}catch(err){handle();}finally{cleanup();}",
    "label:while(flag)break label;"
  );
  assert_eq!(emit(src), expected);
}

#[test]
fn emits_var_func_and_class_decls() {
  let src = r#"
    export const a = 1;
    let b!: number;
    using res = foo;
    await using u = foo;
    export default function foo(a) { return a; }
    class C extends D implements E { field: number = 1; method(x) { return x; } }
  "#;
  let expected = concat!(
    "export const a=1;",
    "let b!:number;",
    "using res=foo;",
    "await using u=foo;",
    "export default function foo(a){return a;}",
    "class C extends D implements E{field:number=1;method(x){return x;}}"
  );
  assert_eq!(emit(src), expected);
}

#[test]
fn emits_import_export_statements() {
  let src = r#"
    import "side";
    import foo, { a as b, type c } from "mod";
    import * as ns from "pkg" with { type: "json" };
    export { a, b as c } from "mod";
    export * as ns from "pkg";
    export default ({ value: 1 });
  "#;
  let expected = concat!(
    "import\"side\";",
    "import foo,{a as b,type c}from\"mod\";",
    "import*as ns from\"pkg\"with{type:\"json\"};",
    "export{a,b as c}from\"mod\";",
    "export*as ns from\"pkg\";",
    "export default({value:1});"
  );
  assert_eq!(emit(src), expected);
}

#[test]
fn roundtrips_simple_programs() {
  let sources = [
    "let x = 1; function f() { return x; }",
    "export default ({ value: 1 });",
  ];
  for src in sources {
    let first = parse_js::parse(src).expect("parse");
    let emitted = emit(src);
    let reparsed = parse_js::parse(&emitted).expect("reparse");
    assert_eq!(ast_value(&first), ast_value(&reparsed));
  }
}
