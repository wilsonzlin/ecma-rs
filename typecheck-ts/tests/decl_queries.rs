#![cfg(feature = "serde")]

use typecheck_ts::{DefId, FileKey, MemoryHost, Program, TypeKindSummary};

fn def_by_name(program: &Program, file: FileKey, name: &str) -> DefId {
  let file_id = program.file_id(&file).unwrap();
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .expect("definition found")
}

#[test]
fn interned_types_cross_file_imports() {
  let mut host = MemoryHost::new();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(
    file_a.clone(),
    "export interface Box<T> { value: T; readonly tag?: string; }",
  );
  host.insert(
    file_b.clone(),
    "import { Box } from \"./a\";\nexport function makeBox<T>(value: T): Box<T> { return { value }; }",
  );
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b.clone()]);
  let box_def = def_by_name(&program, file_a.clone(), "Box");
  let make_box_def = def_by_name(&program, file_b.clone(), "makeBox");

  let box_ty = program.type_of_def_interned(box_def);
  let make_box_ty = program.type_of_def_interned(make_box_def);
  eprintln!("Box type {}", program.display_type(box_ty));
  eprintln!("makeBox type {}", program.display_type(make_box_ty));
  eprintln!(
    "makeBox store type {}",
    program.display_type(program.type_of_def(make_box_def))
  );
  eprintln!("makeBox kind {:?}", program.interned_type_kind(make_box_ty));
  let sigs = program.call_signatures(make_box_ty);
  for sig in sigs {
    eprintln!(
      "makeBox sig ret {}",
      program.display_type(sig.signature.ret)
    );
  }

  let box_kind = program.type_kind(box_ty);
  let make_box_kind = program.type_kind(make_box_ty);

  let box_display = program.display_type(box_ty).to_string();
  assert!(
    box_display.contains("Box"),
    "Box should display as named reference; got {box_display}"
  );

  assert!(
    !matches!(
      box_kind,
      TypeKindSummary::Unknown | TypeKindSummary::Any | TypeKindSummary::Never
    ),
    "interface Box should produce a concrete type, got {box_kind:?}"
  );
  assert!(
    matches!(make_box_kind, TypeKindSummary::Callable { .. }),
    "makeBox should type-check as callable, got {make_box_kind:?}"
  );

  let make_box_display = program.display_type(make_box_ty).to_string();
  assert!(
    make_box_display.contains("Box"),
    "makeBox return type should reference Box; got {make_box_display}"
  );

  let make_box_store_display = program
    .display_type(program.type_of_def(make_box_def))
    .to_string();
  assert!(
    make_box_store_display.contains("Box"),
    "type_of_def should preserve signature references; got {make_box_store_display}"
  );
}

#[test]
fn snapshot_preserves_interned_types() {
  let mut host = MemoryHost::new();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(
    file_a.clone(),
    "export interface Box<T> { value: T; readonly tag?: string; }",
  );
  host.insert(
    file_b.clone(),
    "import { Box } from \"./a\";\nexport function makeBox<T>(value: T): Box<T> { return { value }; }",
  );
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host.clone(), vec![file_b.clone()]);
  let _ = program.check();
  let snapshot = program.snapshot();

  let restored = Program::from_snapshot(host, snapshot);
  let box_def = def_by_name(&restored, file_a.clone(), "Box");
  let make_box_def = def_by_name(&restored, file_b.clone(), "makeBox");

  let restored_box = restored.type_of_def_interned(box_def);
  let restored_make_box = restored.type_of_def_interned(make_box_def);

  let restored_box_display = restored.display_type(restored_box).to_string();
  let restored_make_box_display = restored.display_type(restored_make_box).to_string();

  assert!(
    restored_box_display.contains("Box"),
    "snapshot should retain Box type, got {restored_box_display}"
  );
  assert!(
    restored_make_box_display.contains("Box"),
    "snapshot should retain makeBox return type, got {restored_make_box_display}"
  );
}
