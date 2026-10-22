//! HIR-only body-checking slice: var declarator annotations are consumed from
//! `hir_js::VarDeclarator.type_annotation` (`TypeExprId`) when type arenas are
//! present — not from AstIndex / AST `TypeLowerer` for simple annotations,
//! named type refs, `typeof`, function/object/mapped/conditional (and related)
//! types.
//!
//! Residual AST path: `import(...)` / `typeof import(...)` (body lowerer has
//! no host), and JSDoc `@type` when there is no TS annotation.

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn body_var_annotation_from_hir_suppresses_assignability_error() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const ok: string = "hi";
      const bad: number = "no";
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let diags = program.check();

  let file_id = program.file_id(&file).expect("file id");
  // Binding types come from HIR annotations (string / number).
  let ok = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("ok"))
    .expect("ok");
  let bad = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("bad"))
    .expect("bad");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(ok)),
      TypeKind::String
    ),
    "ok should be string from HIR VarDeclarator annotation"
  );
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(bad)),
      TypeKind::Number
    ),
    "bad should be number from HIR VarDeclarator annotation"
  );

  let assign_errors: Vec<_> = diags
    .iter()
    .filter(|d| d.code == "TS2322" || d.message.contains("not assignable"))
    .collect();
  assert!(
    !assign_errors.is_empty(),
    "expected assignability diagnostic for `const bad: number = \"no\"`, got: {diags:?}"
  );
}

#[test]
fn nested_function_var_annotation_from_hir() {
  // Body-local vars are not module DefIds; check via diagnostics that the
  // annotation is applied (wrong initializer → assignability error).
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f() {
        let x: boolean = 1;
        return x;
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("boolean")),
    "expected HIR-lowered `boolean` annotation to reject number initializer, got: {diags:?}"
  );
}

#[test]
fn union_and_array_var_annotations_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const a: string | number = true;
      const b: string[] = 0;
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let errors: Vec<_> = diags
    .iter()
    .filter(|d| d.code == "TS2322" || d.message.contains("not assignable"))
    .collect();
  assert!(
    errors.len() >= 2,
    "expected two assignability errors from HIR union/array annotations, got: {diags:?}"
  );
}

#[test]
fn named_type_ref_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type Id = string;
      const ok: Id = "hi";
      const bad: Id = 1;
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let diags = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let ok = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("ok"))
    .expect("ok");
  // Annotation is a named ref; expanded/aliased type should still be string-like
  // for assignability (wrong init must error).
  let _ = program.type_of_def(ok);

  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("string")),
    "expected HIR-lowered named ref `Id` to reject number initializer, got: {diags:?}"
  );
}

#[test]
fn interface_type_ref_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      interface Point { x: number; y: number }
      const bad: Point = { x: 1 };
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("y")
      || d.message.contains("Point")),
    "expected HIR-lowered interface ref `Point` to reject incomplete object, got: {diags:?}"
  );
}

#[test]
fn typeof_local_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f() {
        const base = "hi";
        const ok: typeof base = "there";
        const bad: typeof base = 1;
        return ok;
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("string")),
    "expected HIR-lowered `typeof base` to reject number initializer, got: {diags:?}"
  );
}

#[test]
fn typeof_module_value_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const base = 1;
      const bad: typeof base = "no";
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("number")),
    "expected HIR-lowered module `typeof base` to reject string initializer, got: {diags:?}"
  );
}

#[test]
fn union_with_named_ref_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type Flag = boolean;
      const bad: string | Flag = 0;
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags
      .iter()
      .any(|d| d.code == "TS2322" || d.message.contains("not assignable")),
    "expected HIR union+named-ref annotation to reject number, got: {diags:?}"
  );
}

#[test]
fn function_type_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const ok: (x: string) => number = (x) => x.length;
      const bad: (x: string) => number = (x) => x;
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let diags = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let ok = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("ok"))
    .expect("ok");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(ok)),
      TypeKind::Callable { .. }
    ),
    "ok should be callable from HIR function-type annotation"
  );

  assert!(
    diags
      .iter()
      .any(|d| d.code == "TS2322" || d.message.contains("not assignable")),
    "expected HIR function-type annotation to reject string-returning fn, got: {diags:?}"
  );
}

#[test]
fn object_type_literal_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const bad: { x: number; y: string } = { x: 1 };
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("y")),
    "expected HIR object-literal type annotation to reject missing `y`, got: {diags:?}"
  );
}

#[test]
fn mapped_type_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const mapped: { [K in "a" | "b"]: number } = { a: 1, b: 2 };
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let mapped = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("mapped"))
    .expect("mapped");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(mapped)),
      TypeKind::Mapped(_)
    ),
    "mapped should keep HIR Mapped annotation, got {:?}",
    program.interned_type_kind(program.type_of_def(mapped))
  );
}

#[test]
fn conditional_type_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type IsStr<T> = T extends string ? true : false;
      const ok: IsStr<"hi"> = true;
      const bad: IsStr<"hi"> = false;
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  // `IsStr<"hi">` should lower via HIR type-alias + conditional; false is not
  // assignable to true.
  assert!(
    diags.iter().any(|d| d.code == "TS2322"
      || d.message.contains("not assignable")
      || d.message.contains("true")
      || d.message.contains("false")),
    "expected HIR conditional-via-alias annotation to reject false, got: {diags:?}"
  );
}

#[test]
fn inline_conditional_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const cond: string extends number ? string : number = 1;
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let cond = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("cond"))
    .expect("cond");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(cond)),
      TypeKind::Conditional { .. }
    ),
    "cond should keep HIR Conditional annotation, got {:?}",
    program.interned_type_kind(program.type_of_def(cond))
  );
}

#[test]
fn nested_function_object_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f() {
        const bad: { n: number } = { n: "x" };
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
    "expected nested HIR object-literal annotation to reject string, got: {diags:?}"
  );
}

#[test]
fn constructor_type_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const ctor: new () => object = class {};
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let ctor = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("ctor"))
    .expect("ctor");
  // `new () => T` lowers to an object type carrying a construct signature
  // (tsc's model), not a call signature
  // (`assignmentCompatWithConstructSignatures*.ts`).
  let ty = program.type_of_def(ctor);
  assert!(
    !program.construct_signatures(ty).is_empty(),
    "ctor should carry a construct signature from the HIR constructor-type annotation, got {:?}",
    program.interned_type_kind(ty)
  );
}

#[test]
fn template_literal_type_var_annotation_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const tpl: `id-${number}` = "id-1";
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let tpl = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("tpl"))
    .expect("tpl");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(tpl)),
      TypeKind::TemplateLiteral(_)
    ),
    "tpl should keep HIR TemplateLiteral annotation, got {:?}",
    program.interned_type_kind(program.type_of_def(tpl))
  );
}
