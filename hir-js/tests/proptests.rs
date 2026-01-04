use hir_js::lower_from_source;
use proptest::prelude::*;

fn arb_noise() -> impl Strategy<Value = String> {
  prop::collection::vec(any::<char>(), 0..64).prop_map(|chars| chars.into_iter().collect())
}

fn arb_snippet() -> impl Strategy<Value = String> {
  let expressions = vec![
    "foo()",
    "foo?.bar",
    "1 + 2 * 3",
    "x ? y : z",
    "(async () => await task)()",
    "[1, 2, ...rest]",
    "({a: 1, b: 2}).a",
  ];
  let statements = vec![
    "let x = 1;",
    "const y = () => foo;",
    "if (flag) { doThing(); } else { other(); }",
    "while (count-- > 0) { call(); }",
    "for (const k in obj) { console.log(k); }",
    "for (const v of list) { break; }",
    "return maybe ?? 0;",
    "type T<U> = U extends string ? `${U}` : number;",
    "type M<K extends keyof any> = { [P in K]: string };",
    "class C { m<T>(x: T) { return x; } }",
    "function f(arg?: number) { return arg ?? 0; }",
    "const tpl: `${\"a\" | \"b\"}` = \"a\";",
  ];
  prop_oneof![
    prop::sample::select(expressions).prop_map(|expr| format!("{expr};")),
    prop::sample::select(statements).prop_map(|stmt| stmt.to_string()),
  ]
}

fn arb_structured_program() -> impl Strategy<Value = String> {
  prop::collection::vec(arb_snippet(), 1..20).prop_map(|parts| parts.join("\n"))
}

fn arb_source() -> impl Strategy<Value = String> {
  prop_oneof![arb_noise(), arb_structured_program()]
}

proptest! {
  #![proptest_config(ProptestConfig::with_cases(64))]

  #[test]
  fn lowering_never_panics(src in arb_source()) {
    let _ = lower_from_source(&src);
  }

  #[test]
  fn lowering_is_deterministic(src in arb_source()) {
    let first = lower_from_source(&src).map_err(|err| format!("{err:?}"));
    let second = lower_from_source(&src).map_err(|err| format!("{err:?}"));
    prop_assert_eq!(first, second);
  }

  #[test]
  fn spans_stay_within_source(src in arb_structured_program()) {
    let limit = src.len() as u32;
    if let Ok(result) = lower_from_source(&src) {
      for def in result.defs.iter() {
        prop_assert!(def.span.start <= def.span.end);
        prop_assert!(def.span.end <= limit);
      }

      for body in result.bodies.iter() {
        for expr in body.exprs.iter() {
          prop_assert!(expr.span.start <= expr.span.end);
          prop_assert!(expr.span.end <= limit);
        }
        for stmt in body.stmts.iter() {
          prop_assert!(stmt.span.start <= stmt.span.end);
          prop_assert!(stmt.span.end <= limit);
        }
        for pat in body.pats.iter() {
          prop_assert!(pat.span.start <= pat.span.end);
          prop_assert!(pat.span.end <= limit);
        }
      }

      for arenas in result.types.values() {
        for ty in arenas.type_exprs.iter() {
          prop_assert!(ty.span.start <= ty.span.end);
          prop_assert!(ty.span.end <= limit);
        }
        for member in arenas.type_members.iter() {
          prop_assert!(member.span.start <= member.span.end);
          prop_assert!(member.span.end <= limit);
        }
        for param in arenas.type_params.iter() {
          prop_assert!(param.span.start <= param.span.end);
          prop_assert!(param.span.end <= limit);
        }
      }
    }
  }
}
