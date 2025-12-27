use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

fn def_by_name(program: &mut Program, file: FileKey, name: &str) -> typecheck_ts::DefId {
  let file_id = program.file_id(&file).unwrap();
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .expect("definition present")
}

#[test]
fn enums_have_distinct_type_and_value_shapes() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let text = r#"enum E { A = 1, B }
const a = E.A;
let x: E;
x = E.B;
const y = x;
"#;
  host.insert(file.clone(), Arc::from(text));
  let mut program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let file_id = program.file_id(&file).unwrap();
  let source = program.file_text(file_id).unwrap();

  let enum_def = def_by_name(&mut program, file.clone(), "E");
  let enum_ty = program.type_of_def_interned(enum_def);
  let mut literal_members: Vec<_> = match program.interned_type_kind(enum_ty) {
    TypeKind::Union(types) => types
      .iter()
      .filter_map(|ty| match program.interned_type_kind(*ty) {
        TypeKind::NumberLiteral(n) => Some(n.0),
        _ => None,
      })
      .collect(),
    TypeKind::NumberLiteral(n) => vec![n.0],
    TypeKind::Number => Vec::new(),
    other => panic!("expected numeric enum union, got {:?}", other),
  };
  literal_members.sort_by(|a, b| a.partial_cmp(b).unwrap());
  assert_eq!(literal_members, vec![1.0, 2.0]);

  let offset_a = source.find("E.A").unwrap() as u32 + 2;
  let ty_a = program.type_at(file_id, offset_a).expect("type of E.A");
  match program.interned_type_kind(ty_a) {
    TypeKind::NumberLiteral(n) => assert_eq!(n.0, 1.0),
    TypeKind::Number => {}
    other => panic!("expected literal 1 for E.A, got {:?}", other),
  }

  let offset_b = source.find("E.B").unwrap() as u32 + 2;
  let ty_b = program.type_at(file_id, offset_b).expect("type of E.B");
  match program.interned_type_kind(ty_b) {
    TypeKind::NumberLiteral(n) => assert_eq!(n.0, 2.0),
    TypeKind::Number => {}
    other => panic!("expected literal 2 for E.B, got {:?}", other),
  }

  let offset_x = source.rfind("x;").unwrap() as u32;
  let mut ty_x = program.type_at(file_id, offset_x).expect("type of x");
  let mut x_kind = program.interned_type_kind(ty_x);
  if let TypeKind::Ref { def, .. } = x_kind {
    ty_x = program.type_of_def_interned(def);
    x_kind = program.interned_type_kind(ty_x);
  }
  match x_kind {
    TypeKind::Union(types) => {
      let mut literal_values: Vec<_> = types
        .iter()
        .filter_map(|ty| match program.interned_type_kind(*ty) {
          TypeKind::NumberLiteral(n) => Some(n.0),
          _ => None,
        })
        .collect();
      literal_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
      assert_eq!(literal_values, vec![1.0, 2.0]);
    }
    TypeKind::NumberLiteral(n) => assert_eq!(n.0, 1.0),
    TypeKind::Number => {}
    other => panic!("expected enum numeric union for x, got {:?}", other),
  }
}
