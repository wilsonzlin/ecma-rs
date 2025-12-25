use emit_js::{emit_top_level_stmt, EmitMode, EmitOptions, Emitter};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use serde_json::Value;

#[derive(Clone, Copy)]
struct Case {
  name: &'static str,
  source: &'static str,
  parse_options: Option<ParseOptions>,
}

impl Case {
  fn parse_options(&self) -> ParseOptions {
    self.parse_options.unwrap_or_default()
  }
}

fn emit_program(program: &Node<TopLevel>, options: EmitOptions) -> Result<String, String> {
  let mut emitter = Emitter::new(options);
  emit_top_level_stmt(&mut emitter, program.stx.as_ref()).map_err(|err| format!("{err:?}"))?;
  String::from_utf8(emitter.into_bytes()).map_err(|_| "emitter output is not UTF-8".into())
}

fn parse_with_case(case: &Case) -> Node<TopLevel> {
  let opts = case.parse_options();
  parse_with_options(case.source, opts)
    .unwrap_or_else(|err| panic!("parse failed for {}: {err:?}", case.name))
}

fn syntax_value(node: &Node<TopLevel>) -> Value {
  serde_json::to_value(&node.stx).expect("serialize syntax")
}

fn roundtrip_case(case: &Case, mode: EmitMode) {
  let parse_opts = case.parse_options();
  let parsed = parse_with_case(case);
  let emitted = emit_program(&parsed, EmitOptions::from(mode))
    .unwrap_or_else(|reason| panic!("emit failed for {} in {mode:?}: {reason}", case.name));

  let reparsed = parse_with_options(&emitted, parse_opts)
    .unwrap_or_else(|err| panic!("reparse failed for {} in {mode:?}: {err:?}", case.name));

  assert_eq!(
    syntax_value(&parsed),
    syntax_value(&reparsed),
    "roundtrip mismatch in {mode:?} for {name}\noriginal:\n{}\nemitted:\n{}",
    case.source,
    emitted,
    name = case.name
  );
}

fn cases() -> Vec<Case> {
  let tsx = ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Module,
  };

  vec![
    Case {
      name: "binary_precedence_chain",
      source: "a + b * c / d % e - f ** g",
      parse_options: None,
    },
    Case {
      name: "logical_precedence_chain",
      source: "a || b && c ?? d && e",
      parse_options: None,
    },
    Case {
      name: "conditional_nesting_left",
      source: "a ? b ? c : d : e ? f : g",
      parse_options: None,
    },
    Case {
      name: "conditional_nesting_right",
      source: "a ? (b ? c : d) : (e ? f : g)",
      parse_options: None,
    },
    Case {
      name: "optional_chaining_call_and_member",
      source: "foo?.bar?.(baz)?.qux",
      parse_options: None,
    },
    Case {
      name: "optional_chaining_computed",
      source: "foo?.[bar]?.(baz)[qux]",
      parse_options: None,
    },
    Case {
      name: "new_target_vs_new_operator",
      source: "function C(){ return new.target; } const v = new Thing();",
      parse_options: None,
    },
    Case {
      name: "await_in_async_function",
      source: "async function run(){ return await (a ?? b?.c); }",
      parse_options: None,
    },
    Case {
      name: "yield_in_generator",
      source: "function* iter(){ yield* another(); yield value ?? (a && b); }",
      parse_options: None,
    },
    Case {
      name: "template_literal_nested",
      source: "const tpl = `a${b}c${`d${e}`}`;",
      parse_options: None,
    },
    Case {
      name: "tagged_template_literal",
      source: "tag`a${b}c${d}`;",
      parse_options: None,
    },
    Case {
      name: "object_literal_at_statement_start",
      source: "({a:1,b(){return this.a;},['c']:3});",
      parse_options: None,
    },
    Case {
      name: "class_expression_at_statement_start",
      source: "(class X { #field = 1; static get v(){ return new.target; } })",
      parse_options: None,
    },
    Case {
      name: "do_while_nested",
      source: "do { do work(); while(check()); } while (done());",
      parse_options: None,
    },
    Case {
      name: "dangling_else",
      source: "if (a) if (b) c(); else d();",
      parse_options: None,
    },
    Case {
      name: "for_simple",
      source: "for(;;) action();",
      parse_options: None,
    },
    Case {
      name: "for_in_single_statement",
      source: "for (const k in obj) handle(k);",
      parse_options: None,
    },
    Case {
      name: "for_of_async",
      source: "async function run(){ for await (const v of stream) { await v; } }",
      parse_options: None,
    },
    Case {
      name: "import_default_named",
      source: "import def, {a as b, c} from \"./mod\";",
      parse_options: None,
    },
    Case {
      name: "export_named_and_default",
      source: "export { foo as default, bar };",
      parse_options: None,
    },
    Case {
      name: "export_namespace_from",
      source: "export * as ns from \"./dep\";",
      parse_options: None,
    },
    Case {
      name: "export_default_function",
      source: "export default function(a){ return a ??= 1; }",
      parse_options: None,
    },
    Case {
      name: "ts_type_assertion",
      source: "const a = foo as Foo;",
      parse_options: None,
    },
    Case {
      name: "ts_satisfies",
      source: "const b = value satisfies Constraint;",
      parse_options: None,
    },
    Case {
      name: "ts_non_null",
      source: "const c = maybe!;",
      parse_options: None,
    },
    Case {
      name: "ts_type_alias",
      source: "type T = {a: number} & {b?: string};",
      parse_options: None,
    },
    Case {
      name: "ts_interface",
      source: "interface I { method(a: string): number; readonly value: boolean; }",
      parse_options: None,
    },
    Case {
      name: "ts_namespace",
      source: "namespace N { export const x = 1; export function f(){ return x; } }",
      parse_options: None,
    },
    Case {
      name: "ts_nested_namespace",
      source: "declare namespace D { namespace Inner { export let v: number; } }",
      parse_options: None,
    },
    Case {
      name: "ts_import_type",
      source: "type IT = import(\"./types\").Thing;",
      parse_options: None,
    },
    Case {
      name: "for_of_without_braces",
      source: "for (const v of values) console.log(v);",
      parse_options: None,
    },
    Case {
      name: "if_else_without_braces",
      source: "if (flag) doThing(); else doOther();",
      parse_options: None,
    },
    Case {
      name: "new_expression_with_call",
      source: "new Foo(bar)(baz);",
      parse_options: None,
    },
    Case {
      name: "await_optional_chaining",
      source: "async function g(){ return await foo?.bar?.(); }",
      parse_options: None,
    },
    Case {
      name: "yield_optional_chaining",
      source: "function* h(){ yield foo?.bar?.(); }",
      parse_options: None,
    },
    Case {
      name: "jsx_with_optional_chaining",
      source: "const view=<div data-value={item?.value}>{items.map(x => <span>{x}</span>)}</div>;",
      parse_options: Some(tsx),
    },
    Case {
      name: "jsx_fragment_and_tagged_template",
      source: "const frag=<><Component a={`x${y}`}/></>;",
      parse_options: Some(tsx),
    },
  ]
}

#[test]
fn roundtrip_canonical_mode() {
  let cases = cases();
  assert!(
    cases.len() >= 30,
    "roundtrip corpus should stay large enough to catch regressions"
  );
  for case in cases.iter() {
    roundtrip_case(case, EmitMode::Canonical);
  }
}

#[test]
fn roundtrip_minified_mode() {
  let cases = cases();
  assert!(
    cases.len() >= 30,
    "roundtrip corpus should stay large enough to catch regressions"
  );
  for case in cases.iter() {
    roundtrip_case(case, EmitMode::Minified);
  }
}
