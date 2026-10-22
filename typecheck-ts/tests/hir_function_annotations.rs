//! HIR-only binder slice: function param/return annotations are consumed from
//! `hir_js::FunctionData` (not binder AST `type_from_type_expr`).
//!
//! Namespace-nested functions are not covered by the top-level AST
//! `collect_function_decl_types` path, so `type_of_def` → `function_type` must
//! lower signatures from HIR.

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn namespace_function_param_return_annotations_from_hir() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      namespace N {
        export function f(x: string, y?: number): boolean {
          return true;
        }
      }
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let f_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("f"))
    .expect("function f");

  let ty = program.type_of_def(f_def);
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1, "expected single call signature");
  let sig = &sigs[0].signature;
  assert_eq!(sig.params.len(), 2);
  assert!(
    matches!(
      program.interned_type_kind(sig.params[0].ty),
      TypeKind::String
    ),
    "param x should be string from HIR"
  );
  assert!(
    matches!(
      program.interned_type_kind(sig.params[1].ty),
      TypeKind::Number
    ),
    "param y should be number from HIR"
  );
  assert!(sig.params[1].optional, "y? should be optional");
  assert!(
    matches!(program.interned_type_kind(sig.ret), TypeKind::Boolean),
    "return should be boolean from HIR"
  );
}

#[test]
fn namespace_generic_function_annotations_from_hir() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      namespace N {
        export function id<T>(value: T): T {
          return value;
        }
      }
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let id_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("id"))
    .expect("function id");

  let ty = program.type_of_def(id_def);
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1);
  let sig = &sigs[0].signature;
  assert_eq!(sig.type_params.len(), 1, "expected one type parameter");
  assert_eq!(sig.params.len(), 1);
  assert!(
    matches!(
      program.interned_type_kind(sig.params[0].ty),
      TypeKind::TypeParam(_)
    ),
    "value: T should lower to a type parameter"
  );
  assert!(
    matches!(program.interned_type_kind(sig.ret), TypeKind::TypeParam(_)),
    "return T should lower to a type parameter"
  );
}

#[test]
fn top_level_annotated_function_still_types() {
  // Smoke: top-level decls also keep correct param/return types after the
  // binder stops AST-lowering annotations (HIR +/or collect path).
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "export function add(a: number, b: number): number { return a + b; }",
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let entry = exports.get("add").expect("export add");
  let ty = entry.type_id.expect("type for add");
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1);
  let sig = &sigs[0].signature;
  assert_eq!(sig.params.len(), 2);
  assert!(matches!(
    program.interned_type_kind(sig.params[0].ty),
    TypeKind::Number
  ));
  assert!(matches!(
    program.interned_type_kind(sig.ret),
    TypeKind::Number
  ));
}

#[test]
fn top_level_overloads_collected_from_hir() {
  // `collect_function_decl_types` must lower overload signatures from HIR
  // `FunctionData` (including bodiless overloads) without AST TypeLowerer.
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      function f(x: string): string;
      function f(x: number): number;
      function f(x: string | number): string | number {
        return x;
      }
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let f_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("f"))
    .expect("function f");
  let ty = program.type_of_def(f_def);
  let sigs = program.call_signatures(ty);
  assert_eq!(
    sigs.len(),
    2,
    "overload set should keep signature decls only (drop implementation)"
  );
  let param_kinds: Vec<_> = sigs
    .iter()
    .map(|s| program.interned_type_kind(s.signature.params[0].ty))
    .collect();
  assert!(
    param_kinds.iter().any(|k| matches!(k, TypeKind::String)),
    "expected string overload, got {param_kinds:?}"
  );
  assert!(
    param_kinds.iter().any(|k| matches!(k, TypeKind::Number)),
    "expected number overload, got {param_kinds:?}"
  );
}

#[test]
fn declare_function_signature_from_hir_collect() {
  let file = FileKey::new("mod.d.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "declare function greet(name: string): boolean;",
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let greet = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("greet"))
    .expect("greet");
  let ty = program.type_of_def(greet);
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1);
  let sig = &sigs[0].signature;
  assert_eq!(sig.params.len(), 1);
  assert!(matches!(
    program.interned_type_kind(sig.params[0].ty),
    TypeKind::String
  ));
  assert!(matches!(
    program.interned_type_kind(sig.ret),
    TypeKind::Boolean
  ));
}
