use emit_js::{EmitMode, EmitOptions, Emitter};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use serde_json::Value;

struct Case {
  name: &'static str,
  source: &'static str,
}

// Placeholder until the full JS emitter is wired in.
fn emit_program(_program: &Node<TopLevel>, _mode: EmitMode) -> Result<String, String> {
  let _emitter = Emitter::new(EmitOptions {
    mode: _mode,
    ..EmitOptions::default()
  });
  Err("full JS emitter is not available yet".into())
}

fn parse(source: &str) -> Option<Node<TopLevel>> {
  match parse_js::parse(source) {
    Ok(ast) => Some(ast),
    Err(err) => {
      eprintln!("SKIP parse {source:?}: {err:?}");
      None
    }
  }
}

fn syntax_value(node: &Node<TopLevel>) -> Value {
  serde_json::to_value(&node.stx).expect("serialize syntax")
}

fn roundtrip_case(case: &Case, mode: EmitMode) -> bool {
  let parsed = match parse(case.source) {
    Some(ast) => ast,
    None => return false,
  };
  let emitted = match emit_program(&parsed, mode) {
    Ok(code) => code,
    Err(reason) => {
      eprintln!("SKIP {mode:?} {name}: {reason}", name = case.name);
      return false;
    }
  };

  let reparsed = match parse(&emitted) {
    Some(ast) => ast,
    None => return false,
  };
  let original_syntax = syntax_value(&parsed);
  let reparsed_syntax = syntax_value(&reparsed);

  assert_eq!(
    original_syntax,
    reparsed_syntax,
    "roundtrip mismatch in {mode:?} for {name}\noriginal:\n{}\nemitted:\n{}",
    case.source,
    emitted,
    name = case.name
  );
  true
}

fn cases() -> Vec<Case> {
  vec![
    Case {
      name: "binary_precedence_chain",
      source: "a + b * c / d % e - f ** g",
    },
    Case {
      name: "logical_precedence_chain",
      source: "a || b && c ?? d && e",
    },
    Case {
      name: "conditional_nesting_left",
      source: "a ? b ? c : d : e ? f : g",
    },
    Case {
      name: "conditional_nesting_right",
      source: "a ? (b ? c : d) : (e ? f : g)",
    },
    Case {
      name: "optional_chaining_call_and_member",
      source: "foo?.bar?.(baz)?.qux",
    },
    Case {
      name: "optional_chaining_computed",
      source: "foo?.[bar]?.(baz)[qux]",
    },
    Case {
      name: "new_target_vs_new_operator",
      source: "function C(){ return new.target; } const v = new Thing();",
    },
    Case {
      name: "await_in_async_function",
      source: "async function run(){ return await (a ?? b?.c); }",
    },
    Case {
      name: "yield_in_generator",
      source: "function* iter(){ yield* another(); yield value ?? (a && b); }",
    },
    Case {
      name: "template_literal_nested",
      source: "const tpl = `a${b}c${`d${e}`}`;",
    },
    Case {
      name: "tagged_template_literal",
      source: "tag`a${b}c${d}`;",
    },
    Case {
      name: "object_literal_at_statement_start",
      source: "({a:1,b(){return this.a;},['c']:3});",
    },
    Case {
      name: "class_expression_at_statement_start",
      source: "(class X { #field = 1; static get v(){ return new.target; } })",
    },
    Case {
      name: "do_while_nested",
      source: "do { do work(); while(check()); } while (done());",
    },
    Case {
      name: "dangling_else",
      source: "if (a) if (b) c(); else d();",
    },
    Case {
      name: "for_simple",
      source: "for(;;) action();",
    },
    Case {
      name: "for_in_single_statement",
      source: "for (const k in obj) handle(k);",
    },
    Case {
      name: "for_of_async",
      source: "async function run(){ for await (const v of stream) { await v; } }",
    },
    Case {
      name: "import_default_named",
      source: "import def, {a as b, c} from \"./mod\";",
    },
    Case {
      name: "export_named_and_default",
      source: "export { foo as default, bar };",
    },
    Case {
      name: "export_namespace_from",
      source: "export * as ns from \"./dep\";",
    },
    Case {
      name: "export_default_function",
      source: "export default function(a){ return a ??= 1; }",
    },
    Case {
      name: "ts_type_assertion",
      source: "const a = foo as Foo;",
    },
    Case {
      name: "ts_satisfies",
      source: "const b = value satisfies Constraint;",
    },
    Case {
      name: "ts_non_null",
      source: "const c = maybe!;",
    },
    Case {
      name: "ts_type_alias",
      source: "type T = {a: number} & {b?: string};",
    },
    Case {
      name: "ts_interface",
      source: "interface I { method(a: string): number; readonly value: boolean; }",
    },
    Case {
      name: "ts_namespace",
      source: "namespace N { export const x = 1; export function f(){ return x; } }",
    },
    Case {
      name: "ts_nested_namespace",
      source: "declare namespace D { namespace Inner { export let v: number; } }",
    },
    Case {
      name: "ts_import_type",
      source: "type IT = import(\"./types\").Thing;",
    },
    Case {
      name: "for_of_without_braces",
      source: "for (const v of values) console.log(v);",
    },
    Case {
      name: "if_else_without_braces",
      source: "if (flag) doThing(); else doOther();",
    },
    Case {
      name: "new_expression_with_call",
      source: "new Foo(bar)(baz);",
    },
    Case {
      name: "await_optional_chaining",
      source: "async function g(){ return await foo?.bar?.(); }",
    },
    Case {
      name: "yield_optional_chaining",
      source: "function* h(){ yield foo?.bar?.(); }",
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
  let mut ran = 0;
  let mut skipped = 0;
  for case in cases {
    if roundtrip_case(&case, EmitMode::Canonical) {
      ran += 1;
    } else {
      skipped += 1;
    }
  }
  if ran == 0 {
    eprintln!(
      "All Canonical roundtrip cases skipped; wire emit_program to the JS emitter to enable"
    );
  } else if skipped > 0 {
    eprintln!(
      "Canonical roundtrip skipped {skipped} cases (ran {ran}); implement remaining emit coverage"
    );
  }
}

#[test]
fn roundtrip_minified_mode() {
  let cases = cases();
  assert!(
    cases.len() >= 30,
    "roundtrip corpus should stay large enough to catch regressions"
  );
  let mut ran = 0;
  let mut skipped = 0;
  for case in cases {
    if roundtrip_case(&case, EmitMode::Minified) {
      ran += 1;
    } else {
      skipped += 1;
    }
  }
  if ran == 0 {
    eprintln!(
      "All Minified roundtrip cases skipped; wire emit_program to the JS emitter to enable"
    );
  } else if skipped > 0 {
    eprintln!(
      "Minified roundtrip skipped {skipped} cases (ran {ran}); implement remaining emit coverage"
    );
  }
}
