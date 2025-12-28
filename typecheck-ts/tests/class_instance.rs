use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn class_instance_type_from_declaration() {
  let mut host = MemoryHost::default();
  let source = r#"class Greeter { greet(): string { return "hi"; } }
let g: Greeter = new Greeter();
const s = g.greet();
"#;
  let file = FileKey::new("entry.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {:?}", diagnostics);

  let file_id = program.file_id(&file).expect("file id");
  let offset = source.find("s =").expect("offset of s") as u32;
  let ty = program.type_at(file_id, offset).expect("type at s");
  assert_eq!(program.display_type(ty).to_string(), "string");
}
