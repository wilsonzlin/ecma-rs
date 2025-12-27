use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

fn def_by_name(program: &mut Program, file: FileKey, name: &str) -> typecheck_ts::DefId {
  let file_id = program.file_id(&file).unwrap();
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("definition {} not found in {:?}", name, file_id))
}

#[test]
fn typeof_class_uses_value_meaning() {
  let mut host = MemoryHost::new();
  host.insert(
    FileKey::new("main.ts"),
    Arc::from(
      r#"
class C { static x: number = 1 }
type T = typeof C;
declare const ctor: T;
const y = ctor.x;
"#,
    ),
  );
  let mut program = Program::new(host, vec![FileKey::new("main.ts")]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let class_def = def_by_name(&mut program, FileKey::new("main.ts"), "C");
  let alias_def = def_by_name(&mut program, FileKey::new("main.ts"), "T");
  let alias_ty = program.type_of_def_interned(alias_def);
  match program.interned_type_kind(alias_ty) {
    TypeKind::Ref { def, .. } => assert_ne!(
      def, class_def,
      "typeof should reference value-side def id, not the class instance def"
    ),
    other => panic!("expected typeof alias to lower to a ref, got {:?}", other),
  }

  let y_def = def_by_name(&mut program, FileKey::new("main.ts"), "y");
  let ty = program.type_of_def_interned(y_def);
  match program.interned_type_kind(ty) {
    TypeKind::Number | TypeKind::NumberLiteral(_) => {}
    other => panic!("expected number, got {:?}", other),
  }
}

#[test]
fn typeof_enum_resolves_to_enum_object() {
  let mut host = MemoryHost::new();
  host.insert(
    FileKey::new("main.ts"),
    Arc::from(
      r#"
enum E { A = 1 }
type TE = typeof E;
declare const e: TE;
const a = e.A;
"#,
    ),
  );
  let mut program = Program::new(host, vec![FileKey::new("main.ts")]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let enum_def = def_by_name(&mut program, FileKey::new("main.ts"), "E");
  let alias_def = def_by_name(&mut program, FileKey::new("main.ts"), "TE");
  let alias_ty = program.type_of_def_interned(alias_def);
  match program.interned_type_kind(alias_ty) {
    TypeKind::Ref { def, .. } => assert_ne!(
      def, enum_def,
      "typeof should reference enum object def id, not the enum type def"
    ),
    other => panic!("expected typeof alias to lower to a ref, got {:?}", other),
  }

  let a_def = def_by_name(&mut program, FileKey::new("main.ts"), "a");
  let ty = program.type_of_def_interned(a_def);
  match program.interned_type_kind(ty) {
    TypeKind::Number | TypeKind::NumberLiteral(_) => {}
    other => panic!("expected numeric enum value, got {:?}", other),
  }
}
