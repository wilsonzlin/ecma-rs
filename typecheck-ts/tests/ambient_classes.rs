use std::sync::Arc;

use typecheck_ts::lib_support::{FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn ambient_class_members_from_libs() {
  let mut host = MemoryHost::new();
  let lib_key = FileKey::new("box.d.ts");
  host.add_lib(LibFile {
    key: lib_key.clone(),
    name: Arc::from("box.d.ts".to_string()),
    kind: FileKind::Dts,
    text: Arc::from("declare class Box { value: string }".to_string()),
  });

  let file = FileKey::new("index.ts");
  host.insert(
    file.clone(),
    Arc::from("let b: Box = { value: \"\" } as any;\nconst v = b.value;".to_string()),
  );

  let program = Program::new(host, vec![file.clone()]);
  let lib_ids = program.file_ids_for_key(&lib_key);
  assert!(
    !lib_ids.is_empty(),
    "library file should be loaded for ambient context"
  );
  let globals = program.global_bindings();
  assert!(
    globals.contains_key("Box"),
    "global bindings should include Box from libs: {:?}",
    globals.keys().collect::<Vec<_>>()
  );
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
  let file_id = program.file_id(&file).unwrap();
  let source = program.file_text(file_id).unwrap();
  let offset = source.rfind("value").expect("value offset") as u32;
  assert!(
    program.type_at(file_id, offset).is_some(),
    "type should be available for property access"
  );
}
