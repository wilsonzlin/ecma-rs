use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId as HirFileId;
use hir_js::{lower_file, DefKind as HirDefKind, FileKind as HirFileKind};
use parse_js::parse;
use semantic_js::ts::{
  bind_ts_program, Decl, DeclKind, Exported, FileId, FileKind, HirFile, ModuleKind, Resolver,
};

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
  let lowered = lower_file(HirFileId(0), HirFileKind::Dts, &ast);

  let mut hir = HirFile::script(FileId(0));
  hir.file_kind = FileKind::Dts;

  let foo_def = lowered
    .defs
    .iter()
    .find(|d| lowered.names.resolve(d.name) == Some("Foo"))
    .expect("Foo lowered from declare global");

  let decl = Decl {
    def_id: semantic_js::ts::DefId(foo_def.id.0),
    name: "Foo".to_string(),
    kind: match foo_def.path.kind {
      HirDefKind::Interface => DeclKind::Interface,
      _ => panic!("unexpected kind for Foo"),
    },
    is_ambient: foo_def.is_ambient,
    is_global: foo_def.in_global,
    exported: Exported::No,
    span: foo_def.span,
  };

  hir.decls.push(decl);

  let files: HashMap<FileId, Arc<HirFile>> = HashMap::from([(FileId(0), Arc::new(hir))]);

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
