use std::sync::Arc;

use typecheck_ts::{DefId, FileKey, MemoryHost, Program, PropertyKey, TypeKindSummary};

fn def_by_name(program: &Program, file: FileKey, name: &str) -> Option<DefId> {
  let file_id = program.file_id(&file).unwrap();
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some(name))
}

#[test]
fn recursive_alias_type_of_def_is_bounded() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("node.ts");
  host.insert(
    file.clone(),
    Arc::from("type ListNode<T> = { next: ListNode<T> };"),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics: {diagnostics:?}"
  );

  let def = def_by_name(&program, file, "ListNode").expect("ListNode defined");
  let ty = program.type_of_def_interned(def);
  let summary = program.type_kind(ty);
  assert!(
    matches!(summary, TypeKindSummary::Ref { def: d, .. } if d == def)
      || matches!(summary, TypeKindSummary::Object),
    "recursive alias should not infinitely expand: {summary:?}"
  );
}

#[test]
fn relate_ctx_handles_cyclic_refs() {
  let mut host = MemoryHost::default();
  host.insert(
    FileKey::new("types.ts"),
    r#"
type A = { next: A };
type B = { next: B };
"#,
  );

  let program = Program::new(host, vec![FileKey::new("types.ts")]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics: {diagnostics:?}"
  );

  let a_def = def_by_name(&program, FileKey::new("types.ts"), "A").expect("A defined");
  let b_def = def_by_name(&program, FileKey::new("types.ts"), "B").expect("B defined");
  let a_ty = program.type_of_def_interned(a_def);
  let b_ty = program.type_of_def_interned(b_def);

  assert_eq!(
    program.type_kind(a_ty),
    program.type_kind(b_ty),
    "structurally identical cycles should map to the same shape summary"
  );
}

#[test]
fn expansion_is_deterministic_across_runs() {
  let mut host = MemoryHost::default();
  host.insert(
    FileKey::new("pair.ts"),
    r#"
type Pair<T> = { value: T; next?: Pair<T> };
type NumPair = Pair<number>;
"#,
  );

  let program = Program::new(host, vec![FileKey::new("pair.ts")]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics: {diagnostics:?}"
  );

  let num_pair =
    def_by_name(&program, FileKey::new("pair.ts"), "NumPair").expect("NumPair defined");
  let num_pair_ty = program.type_of_def_interned(num_pair);

  let first = program
    .property_type(num_pair_ty, PropertyKey::String("next".into()))
    .expect("next property present");
  let second = program
    .property_type(num_pair_ty, PropertyKey::String("next".into()))
    .expect("next property present");
  assert_eq!(
    first, second,
    "expansion results should be deterministic across calls"
  );
}
