//! HIR-only body-checking slice: type assertions / `satisfies` / `as const`
//! prefer HIR `ExprKind::TypeAssertion` / `Satisfies` (`TypeExprId` +
//! `const_assertion`) via body type arenas + `HirDeclLowerer`, matching var
//! annotation lowering (named refs / `typeof` via body `TypeResolver`).
//!
//! Residual AST path: `import(...)` / `typeof import(...)` assertion targets
//! (body lowerer has no host) and missing arenas.

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn type_assertion_primitive_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const x = ("hi" as number);
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let x = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("x"))
    .expect("x");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(x)),
      TypeKind::Number
    ),
    "x should be number from HIR TypeAssertion annotation"
  );
}

#[test]
fn type_assertion_named_ref_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type Id = string;
      const x = (1 as Id);
      const y: Id = x;
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  // `1 as Id` yields string (via HIR named ref); assigning to Id is fine.
  // If HIR lowering failed and fell back incorrectly, y would error or x
  // would not behave as string.
  assert!(
    !diags.iter().any(|d| d.code == "TS2322"),
    "expected HIR-lowered `as Id` to type as string-compatible, got: {diags:?}"
  );
}

#[test]
fn as_const_literal_from_hir_flag() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const x = (1 as const);
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let x = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("x"))
    .expect("x");
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(x)),
      TypeKind::NumberLiteral(_)
    ),
    "x should be numeric literal from HIR `as const`, got {:?}",
    program.interned_type_kind(program.type_of_def(x))
  );
}

#[test]
fn satisfies_primitive_from_hir_rejects_mismatch() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const bad = ("hi" satisfies number);
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.message.contains("satisfy")
      || d.message.contains("assignable")
      || d.code == "TS2322"),
    "expected HIR-lowered `satisfies number` to reject string, got: {diags:?}"
  );
}

#[test]
fn satisfies_named_ref_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      type Flag = boolean;
      const ok = (true satisfies Flag);
      const bad = (1 satisfies Flag);
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.message.contains("satisfy")
      || d.message.contains("assignable")
      || d.code == "TS2322"),
    "expected HIR-lowered `satisfies Flag` to reject number, got: {diags:?}"
  );
}

#[test]
fn nested_function_assertion_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f() {
        const x = ("hi" as number);
        return x;
      }
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  // Body-local; probe via type_at / expression side tables through check.
  // Assert no ICE and that module check completes (HIR path exercised).
  let file_id = program.file_id(&file).expect("file id");
  let f = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("f"))
    .expect("f");
  let _ = program.type_of_def(f);
}

#[test]
fn typeof_in_type_assertion_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f() {
        const base = "hi";
        const x = (0 as typeof base);
        const bad: typeof base = x;
        return bad;
      }
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  // `0 as typeof base` → string; assigning number-as-string to typeof base is ok.
  // If typeof lowering failed, we may get assignability errors on `bad`.
  assert!(
    !diags.iter().any(|d| d.code == "TS2322"),
    "expected HIR `as typeof base` to yield string, got: {diags:?}"
  );
}

#[test]
fn type_assertion_function_target_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const f = ((x: string) => x.length) as (x: string) => number;
      const n: number = f("hi");
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags.iter().any(|d| d.code == "TS2322"),
    "expected HIR `as (x: string) => number` to type as callable, got: {diags:?}"
  );
}

#[test]
fn type_assertion_object_literal_target_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const x = ({ x: 1 } as { x: number; y?: string });
      const y: number = x.x;
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags.iter().any(|d| d.code == "TS2322"),
    "expected HIR object-literal assertion target, got: {diags:?}"
  );
}

#[test]
fn satisfies_object_literal_from_hir_rejects_mismatch() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const bad = ({ x: 1 } satisfies { x: number; y: string });
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.message.contains("satisfy")
      || d.message.contains("assignable")
      || d.code == "TS2322"
      || d.message.contains("y")),
    "expected HIR `satisfies` object-literal target to reject missing y, got: {diags:?}"
  );
}

#[test]
fn type_assertion_mapped_target_from_hir() {
  let file = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      const x = ({ a: 1, b: 2 } as { [K in "a" | "b"]: number });
      const n: number = x.a;
    "#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags.iter().any(|d| d.code == "TS2322"),
    "expected HIR mapped assertion target, got: {diags:?}"
  );
}
