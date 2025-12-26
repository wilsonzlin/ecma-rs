use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId as HirFileId;
use hir_js::lower_file_with_diagnostics;
use hir_js::FileKind as HirFileKind;
use parse_js::parse;
use semantic_js::ts::{
  bind_ts_program, from_hir_js::lower_to_ts_hir, FileId, ModuleKind, Resolver,
};
use typecheck_ts::{FileKey, MemoryHost, Program};

struct NoResolve;

impl Resolver for NoResolve {
  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

#[test]
fn declare_global_from_dts_is_available_globally() {
  let source = r#"declare global { interface Foo { bar: string; } }"#;
  let ast = parse(source).expect("parse");
  let (lowered, diags) = lower_file_with_diagnostics(HirFileId(0), HirFileKind::Dts, &ast);
  assert!(diags.is_empty());
  let hir = lower_to_ts_hir(&ast, &lowered);

  let files: HashMap<FileId, Arc<semantic_js::ts::HirFile>> =
    HashMap::from([(FileId(0), Arc::new(hir))]);

  let (semantics, diags) =
    bind_ts_program(&[FileId(0)], &NoResolve, |f| files.get(&f).unwrap().clone());

  assert!(diags.is_empty());
  assert!(
    semantics.global_symbols().contains_key("Foo"),
    "global symbol for Foo is available"
  );
  assert_eq!(
    ModuleKind::Script,
    files.get(&FileId(0)).unwrap().module_kind
  );
}

#[test]
fn interfaces_merge_members_for_interned_types() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("input.d.ts");
  host.insert(
    file.clone(),
    Arc::from("interface Foo { a: string; }\ninterface Foo { b: number; }"),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Foo"))
    .expect("Foo definition");
  let ty = program.type_of_def(def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("a: string") && rendered.contains("b: number"),
    "merged interface should expose all members, got {rendered}"
  );
}
