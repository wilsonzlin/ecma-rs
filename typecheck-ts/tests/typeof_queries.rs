use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn typeof_queries_in_libs_resolve_value_types() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  host.add_lib(LibFile {
    key: FileKey::new("typeof.d.ts"),
    name: Arc::from("typeof.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare const window: { document: { title: string } };
declare const title: typeof window.document.title;
"#,
    ),
  });

  let entry = FileKey::new("entry.ts");
  let source = "const t: typeof title = window.document.title;";
  host.insert(entry.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id for entry");
  let offset = source.rfind("title").expect("title property offset") as u32;
  let ty = program.type_at(file_id, offset).expect("type of window.document.title");
  assert_eq!(program.display_type(ty).to_string(), "string");
}
