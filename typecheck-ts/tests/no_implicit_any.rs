use diagnostics::TextRange;
use typecheck_ts::codes;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn reports_implicit_any_for_params_and_destructuring() {
  let source = "function f(x) { return x; }\nconst {a} = something;";
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  let implicit: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str())
    .collect();
  // tsc emits TS7006 for the unannotated parameter only — the destructured
  // `a` from an unresolved RHS gets no implicit-any diagnostic (only the
  // TS2304 for `something`).
  assert_eq!(
    implicit.len(),
    1,
    "expected exactly one implicit-any diagnostic, got {implicit:?} (all={diagnostics:?})",
  );

  let x_start = source.find("f(x)").expect("expected f(x) in source") as u32 + 2;
  let x_span = TextRange::new(x_start, x_start + 1);
  assert!(
    implicit
      .iter()
      .any(|diag| diag.primary.file == file_id && diag.primary.range == x_span),
    "missing implicit-any diagnostic on parameter `x` at {x_span:?}: {implicit:?}",
  );

  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == "TS2304"),
    "expected TS2304 for unresolved `something`: {diagnostics:?}",
  );
}

#[test]
fn parameter_default_value_suppresses_implicit_any() {
  // Spec (tsc, --strict): a parameter with an initializer infers its type from
  // the (widened) initializer, so `--noImplicitAny` does not flag it. Mirrors
  // upstream conformance case
  // `expressions/nullishCoalescingOperator/nullishCoalescingOperator6.ts`:
  //   function foo(foo: string, bar = foo ?? "bar") { }
  // tsc reports no diagnostics; the checker must not report TC3000 for `bar`.
  let source = "function foo(foo: string, bar = foo ?? \"bar\") { bar; }";
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    strict_null_checks: true,
    strict_function_types: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str()),
    "parameter with a default value must not be implicit-any, got {diagnostics:?}",
  );

  // The inferred type of `bar` should come from the initializer (`string`).
  let bar_use = source.rfind("bar;").expect("bar; use") as u32;
  let bar_ty = program.type_at(file_id, bar_use).expect("type at bar use");
  assert_eq!(program.display_type(bar_ty).to_string(), "string");
}

#[test]
fn reports_implicit_any_for_uncontextualized_arrow_params() {
  let source = "const f = (x) => x;";
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  let implicit: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str())
    .collect();
  assert_eq!(
    implicit.len(),
    1,
    "expected exactly one implicit-any diagnostic, got {implicit:?} (all={diagnostics:?})",
  );

  let x_start = source.find("(x) =>").expect("expected `(x) =>` in source") as u32 + 1;
  let x_span = TextRange::new(x_start, x_start + 1);
  assert!(
    implicit
      .iter()
      .any(|diag| diag.primary.file == file_id && diag.primary.range == x_span),
    "missing implicit-any diagnostic on arrow parameter `x` at {x_span:?}: {implicit:?}",
  );
}

#[test]
fn annotated_class_fields_suppress_implicit_any() {
  // Spec (tsc, --strict): a class field with an explicit type annotation is not
  // implicit-any, including private `#name` fields. Mirrors upstream
  // `classes/members/privateNames/privateNameField.ts` (`#name: string`).
  // The checker must read HIR `DefData.declared_type` / class-member annotations
  // so annotated public and private fields do not emit TC3000.
  let source = r#"
class A {
  #name: string;
  publicName: string;
  constructor(name: string) {
    this.#name = name;
    this.publicName = name;
  }
}
"#;
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    strict_null_checks: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str()),
    "annotated class fields (#name / publicName) must not be implicit-any, got {diagnostics:?}",
  );
}

#[test]
fn contextual_rest_param_types_are_applied_to_extra_parameters() {
  let source = r#"
 type Fn = (...args: { x: number }[]) => void;
 const f: Fn = (a, b) => { const n: number = a.x + b.x; };
 "#;
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str()),
    "did not expect implicit-any diagnostics for contextually typed rest params, got {diagnostics:?}",
  );

  let a_offset = source.find("a.x").expect("a.x") as u32 + 1;
  let a_ty = program.type_at(file_id, a_offset).expect("type at a.x");
  assert_eq!(program.display_type(a_ty).to_string(), "number");

  let b_offset = source.find("b.x").expect("b.x") as u32 + 1;
  let b_ty = program.type_at(file_id, b_offset).expect("type at b.x");
  assert_eq!(program.display_type(b_ty).to_string(), "number");
}
