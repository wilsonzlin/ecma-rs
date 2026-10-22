//! Decorated class expressions inside field initializers
//! (`esDecorators-classExpression-namedEvaluation.10.ts`): the decorator's
//! evaluation body (`BodyKind::Class`) must not ICE with "missing class body
//! for checker" — exprs covered by an enclosing field initializer are checked
//! by that initializer's own body, so they count as covered for the
//! missing-body decision.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn decorated_class_expr_in_static_field_is_not_ice() {
  let src = "declare let dec: any;\nclass C { static x = @dec class {}; }\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn decorated_class_expr_in_instance_field_is_not_ice() {
  let src = "declare let dec: any;\nclass C { x = @dec class {}; }\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn decorated_class_expr_with_members_in_field() {
  let src = "declare let dec: any;\nclass C { static x = @dec class { y = 1 }; }\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn decorator_still_checks_args() {
  // The decorator expression itself is still checked (unresolved name → TS2304).
  let src = "class C { static x = @missingDec class {}; }\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2304"),
    "unresolved decorator must still error: {c:?}"
  );
}
