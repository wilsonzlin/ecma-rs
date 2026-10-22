//! HIR-only body-checking slice: Instantiation type arguments prefer HIR
//! `ExprKind::Instantiation` (`Vec<TypeExprId>`) via body type arenas +
//! `HirDeclLowerer` / body `TypeResolver`, matching var annotations and
//! `as` / `satisfies`.
//!
//! Residual AST path: `import(...)` / `typeof import(...)` type args (body
//! lowerer has no host) and missing arenas.

use diagnostics::TextRange;
use std::sync::Arc;
use typecheck_ts::{codes, FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn instantiation_primitive_type_args_from_hir() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source =
    "function f<T>(x: T): T { return x; }\nconst g = f<string>;\nconst ok: string = g(\"hi\");\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags
      .iter()
      .any(|d| d.code == "TS2322" || d.code == "TS2345"),
    "expected HIR-lowered `f<string>` to type as string-callable, got: {diags:?}"
  );
}

#[test]
fn instantiation_named_ref_type_arg_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type Id = string;
      function f<T>(x: T): T { return x; }
      const g = f<Id>;
      const ok: Id = g("hi");
      const bad: Id = g(1);
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags
      .iter()
      .any(|d| d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str() || d.code == "TS2345"),
    "expected HIR-lowered `f<Id>` to reject number arg, got: {diags:?}"
  );
}

#[test]
fn instantiation_call_type_args_from_hir_reject_mismatch() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source = "function f<T>(x: T): T { return x; }\nf<string>(1);\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected a single diagnostic, got {diagnostics:?}"
  );
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::ARGUMENT_TYPE_MISMATCH.as_str());

  let start = source.find('1').expect("numeric literal present") as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, start + 1));
}

#[test]
fn instantiation_arity_from_hir() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source = "function f<T>(x: T): T { return x; }\nf<string, number>(\"x\");\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected a single diagnostic, got {diagnostics:?}"
  );
  let diag = &diagnostics[0];
  assert_eq!(
    diag.code.as_str(),
    codes::WRONG_TYPE_ARGUMENT_COUNT.as_str()
  );

  let needle = "f<string, number>";
  let start = source.find(needle).expect("type arguments present") as u32;
  let end = start + needle.len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

#[test]
fn nested_function_instantiation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function outer() {
        function f<T>(x: T): T { return x; }
        const g = f<number>;
        return g("no");
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags
      .iter()
      .any(|d| d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str() || d.code == "TS2345"),
    "expected body-local HIR Instantiation type args, got: {diags:?}"
  );
}

#[test]
fn instantiation_typeof_type_arg_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f<T>(x: T): T { return x; }
      function g() {
        const base = "hi";
        const h = f<typeof base>;
        const ok: string = h("x");
        return ok;
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags.iter().any(|d| d.code == "TS2322"),
    "expected HIR `f<typeof base>` type arg, got: {diags:?}"
  );
}

#[test]
fn instantiation_union_type_arg_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f<T>(x: T): T { return x; }
      const g = f<string | number>;
      const a: string | number = g(1);
      const b: string | number = g("x");
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let diags = program.check();
  assert!(
    !diags
      .iter()
      .any(|d| d.code == "TS2322" || d.code == "TS2345"),
    "expected HIR union Instantiation type arg, got: {diags:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let a = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("a"))
    .expect("a");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(a)),
      TypeKind::Union(_) | TypeKind::String | TypeKind::Number
    ),
    "a should reflect union Instantiation, got {:?}",
    program.interned_type_kind(program.type_of_def(a))
  );
}
