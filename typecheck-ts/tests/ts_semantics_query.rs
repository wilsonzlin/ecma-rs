use std::collections::BTreeSet;
use std::sync::Arc;
use typecheck_ts::db::TypecheckDb;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{FileId, FileKey, FileOrigin, Host, MemoryHost, Program};

fn fk(id: u32) -> FileKey {
  FileKey::new(format!("file{id}.ts"))
}

fn canonical_exports(
  sem: &semantic_js::ts::TsProgramSemantics,
  file: FileId,
) -> Vec<(String, (Option<u64>, Option<u64>, Option<u64>))> {
  let mut entries: Vec<_> = sem
    .exports_of(semantic_js::ts::FileId(file.0))
    .iter()
    .map(|(name, group)| {
      let value = group
        .symbol_for(semantic_js::ts::Namespace::VALUE, sem.symbols())
        .map(|s| s.0);
      let ty = group
        .symbol_for(semantic_js::ts::Namespace::TYPE, sem.symbols())
        .map(|s| s.0);
      let namespace = group
        .symbol_for(semantic_js::ts::Namespace::NAMESPACE, sem.symbols())
        .map(|s| s.0);
      (name.clone(), (value, ty, namespace))
    })
    .collect();
  entries.sort_by(|a, b| a.0.cmp(&b.0));
  entries
}

fn export_names(sem: &semantic_js::ts::TsProgramSemantics, file: FileId) -> BTreeSet<String> {
  sem
    .exports_of(semantic_js::ts::FileId(file.0))
    .keys()
    .cloned()
    .collect()
}

#[test]
fn ts_semantics_matches_program_exports_and_is_deterministic() {
  let mut host = MemoryHost::new();
  let key_a = fk(0);
  let key_b = fk(1);
  let key_c = fk(2);
  host.insert(key_a.clone(), "export const foo: number = 1;");
  host.insert(key_b.clone(), "export { foo as bar } from \"./a\";");
  host.insert(key_c.clone(), "export * from \"./b\";");

  let edges = vec![
    (key_b.clone(), "./a".to_string(), key_a.clone()),
    (key_c.clone(), "./b".to_string(), key_b.clone()),
  ];
  for (from, spec, to) in edges.iter() {
    host.link(from.clone(), spec, to.clone());
  }

  let db_host = host.clone();
  let program = Program::new(host, vec![key_c.clone()]);
  let program_diags = program.check();
  assert!(
    program_diags.is_empty(),
    "program produced unexpected diagnostics: {program_diags:?}"
  );

  let file_a = program.file_id(&key_a).expect("file a id");
  let file_b = program.file_id(&key_b).expect("file b id");
  let file_c = program.file_id(&key_c).expect("file c id");

  let mut db = TypecheckDb::default();
  let roots: Arc<[FileKey]> = vec![key_c.clone()].into();
  db.set_roots(roots);
  for (key, id) in [
    (key_a.clone(), file_a),
    (key_b.clone(), file_b),
    (key_c.clone(), file_c),
  ] {
    let text = db_host.file_text(&key).expect("file text");
    db.set_file(id, key, FileKind::Ts, text, FileOrigin::Source);
  }
  for (from, spec, to) in edges.into_iter() {
    let from_id = program.file_id(&from).expect("from id");
    let to_id = program.file_id(&to).expect("to id");
    db.set_module_resolution(from_id, Arc::<str>::from(spec.as_str()), Some(to_id));
  }

  let ts_result = db.ts_semantics();
  let ts_result = ts_result.as_ref();
  let semantics = &ts_result.semantics;
  let ts_diags = &ts_result.diagnostics;
  assert!(
    ts_diags.is_empty(),
    "ts_semantics produced unexpected diagnostics: {ts_diags:?}"
  );
  assert_eq!(
    ts_diags.as_slice(),
    program_diags.as_slice(),
    "semantic-js diagnostics diverged from program output"
  );

  for file in [file_a, file_b, file_c] {
    let program_exports: BTreeSet<_> = program.exports_of(file).keys().cloned().collect();
    let ts_exports = export_names(semantics, file);
    assert_eq!(
      program_exports, ts_exports,
      "export names diverged for file {file:?}"
    );
  }

  let foo_def = program
    .exports_of(file_a)
    .get("foo")
    .and_then(|entry| entry.def)
    .expect("foo def present");
  let foo_symbol = semantics
    .resolve_export(
      semantic_js::ts::FileId(file_a.0),
      "foo",
      semantic_js::ts::Namespace::VALUE,
    )
    .expect("foo export has value symbol");
  let foo_defs: Vec<_> = semantics
    .symbol_decls(foo_symbol, semantic_js::ts::Namespace::VALUE)
    .iter()
    .map(|decl| semantics.symbols().decl(*decl).def_id)
    .collect();
  assert!(
    foo_defs.contains(&foo_def),
    "binder should point at the same def id as Program for local exports"
  );

  let baseline_exports = canonical_exports(semantics, file_c);
  let baseline_diags = ts_diags.clone();
  let snap_a = db.snapshot();
  let snap_b = db.snapshot();
  let join = |snap: TypecheckDb| {
    std::thread::spawn(move || {
      let result = snap.ts_semantics();
      let sem = &result.semantics;
      let diags = &result.diagnostics;
      (canonical_exports(sem, file_c), diags.clone())
    })
  };
  for handle in [join(snap_a), join(snap_b)] {
    let (exports, diags) = handle.join().expect("thread panicked");
    assert_eq!(exports, baseline_exports, "snapshot exports drifted");
    assert_eq!(diags, baseline_diags, "snapshot diagnostics drifted");
  }
}
