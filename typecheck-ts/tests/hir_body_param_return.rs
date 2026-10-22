//! HIR-only body-checking slice: function param/return annotations are consumed
//! from `hir_js::FunctionData` (`TypeExprId`) when the AST function matches the
//! body being checked — not from AST `TypeLowerer` for the supported subset
//! (including generics via seeded type-param bindings).
//!
//! Residual AST path: nested function-expression signature synthesis /
//! refine while checking an outer body, `typeof import(...)`, missing arenas,
//! JSDoc `@param`/`@returns`, and function type-parameter *registration*
//! (`register_type_params` still AST).

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn body_param_annotation_from_hir_rejects_bad_arg() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f(x: string) {
        return x;
      }
      f(1);
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2345"
      || d.message.contains("not assignable")
      || d.message.contains("string")),
    "expected HIR-lowered param `string` to reject number arg, got: {diags:?}"
  );
}

#[test]
fn body_return_annotation_from_hir_rejects_bad_return() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f(): string {
        return 1;
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("string")),
    "expected HIR-lowered return `string` to reject number, got: {diags:?}"
  );
}

#[test]
fn body_param_used_inside_body_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f(x: number) {
        const bad: string = x;
        return bad;
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags
      .iter()
      .any(|d| d.code == "TS2322" || d.message.contains("not assignable")),
    "expected HIR param type to bind inside body, got: {diags:?}"
  );
}

#[test]
fn generic_param_return_annotations_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function id<T>(value: T): T {
        return value;
      }
      const ok: string = id<string>("hi");
      id<string>(1);
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let diags = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let id_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("id"))
    .expect("id");
  let ty = program.type_of_def(id_def);
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1);
  let sig = &sigs[0].signature;
  assert_eq!(sig.type_params.len(), 1);
  assert!(
    matches!(
      program.interned_type_kind(sig.params[0].ty),
      TypeKind::TypeParam(_)
    ),
    "value: T should be a type parameter"
  );
  assert!(
    matches!(program.interned_type_kind(sig.ret), TypeKind::TypeParam(_)),
    "return T should be a type parameter"
  );

  assert!(
    diags
      .iter()
      .any(|d| d.code == "TS2345" || d.message.contains("not assignable")),
    "expected generic instantiation to reject number for string, got: {diags:?}"
  );
}

#[test]
fn nested_arrow_param_still_typed() {
  // Nested arrows are refined/synthesized against an outer body; param
  // annotations remain AST TypeLowerer there, but must still type-check.
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function outer() {
        const g = (x: string) => x;
        g(1);
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2345"
      || d.message.contains("not assignable")
      || d.message.contains("string")),
    "expected nested arrow param annotation to still reject number, got: {diags:?}"
  );
}

#[test]
fn named_ref_param_return_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type Id = string;
      function f(x: Id): Id {
        return x;
      }
      f(0);
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags
      .iter()
      .any(|d| d.code == "TS2345" || d.message.contains("not assignable")),
    "expected HIR named-ref param to reject number, got: {diags:?}"
  );
}
