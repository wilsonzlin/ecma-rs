use diagnostics::FileId;
use hir_js::{lower_file, DefKind, ExprId, ExprKind};
use parse_js::parse;
use proptest::prelude::*;

#[test]
fn def_ids_are_sorted_and_stable() {
  let source = "function f() {}\nconst b = 2;\nconst a = 1;";
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(0), &ast);

  let names: Vec<_> = result
    .defs
    .iter()
    .map(|def| result.names.resolve(def.path.name).unwrap().to_string())
    .collect();
  let kinds: Vec<_> = result.defs.iter().map(|def| def.path.kind).collect();

  assert_eq!(names, vec!["f", "a", "b"]);
  assert_eq!(kinds, vec![DefKind::Function, DefKind::Var, DefKind::Var]);

  let ast_again = parse(source).expect("parse");
  let result_again = lower_file(FileId(0), &ast_again);
  let names_again: Vec<_> = result_again
    .defs
    .iter()
    .map(|def| result_again.names.resolve(def.path.name).unwrap().to_string())
    .collect();
  assert_eq!(names, names_again);
}

#[test]
fn expr_at_offset_prefers_inner_expression() {
  let source = "const a = 1 + 2;";
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(1), &ast);

  let def = result
    .defs
    .iter()
    .find(|d| d.path.kind == DefKind::Var)
    .expect("var def");
  let body_id = def.body.expect("var has initializer body");
  let body = result.bodies[body_id.0 as usize].as_ref();
  let map = &result.hir.span_map;

  let (binary_id, left_span) = body
    .exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      ExprKind::Binary { left, right: _ } => Some((ExprId(idx as u32), body.exprs[left.0 as usize].span)),
      _ => None,
    })
    .expect("binary expression present");

  let offset = left_span.start;
  let expected = body
    .exprs
    .iter()
    .enumerate()
    .filter(|(_, expr)| expr.span.contains(offset))
    .min_by_key(|(idx, expr)| (expr.span.len(), expr.span.start, *idx))
    .map(|(idx, _)| ExprId(idx as u32))
    .unwrap();

  let mapped = map.expr_at_offset(offset).expect("expr at offset");
  assert_eq!(mapped, expected);

  let binary_span = body.exprs[binary_id.0 as usize].span;
  let mapped_binary = map.expr_at_offset(binary_span.start).expect("mapped binary expr");
  assert!(body.exprs[mapped_binary.0 as usize].span.len() <= binary_span.len());
}

#[test]
fn lowers_common_ts_constructs() {
  let source = r#"
interface Foo { bar: string }
type Alias = Foo;
enum Color { Red }
namespace NS { export const x = 1; }
"#;
  let ast = parse(source).expect("parse");
  let result = lower_file(FileId(2), &ast);
  let kinds: Vec<_> = result.defs.iter().map(|d| d.path.kind).collect();

  assert!(kinds.contains(&DefKind::Interface));
  assert!(kinds.contains(&DefKind::TypeAlias));
  assert!(kinds.contains(&DefKind::Enum));
  assert!(kinds.contains(&DefKind::Namespace));
}

proptest! {
  #[test]
  fn lowering_is_deterministic(sample in proptest::sample::select(vec![
    "const a = 1;",
    "function f(x) { return x * 2; }",
    "interface Foo { bar: string }\nnamespace NS { export const x = 1; }",
  ])) {
    let ast1 = parse(sample).expect("parse");
    let ast2 = parse(sample).expect("parse");

    let res1 = lower_file(FileId(9), &ast1);
    let res2 = lower_file(FileId(9), &ast2);

    prop_assert_eq!(res1.defs, res2.defs);
    prop_assert_eq!(res1.hir, res2.hir);
    prop_assert_eq!(res1.bodies, res2.bodies);
  }
}
