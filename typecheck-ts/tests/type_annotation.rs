use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use typecheck_ts::{FileId, Host, HostError, Program};
use types_ts_interned::TypeKind;

#[derive(Clone)]
struct FileHost {
  files: HashMap<FileId, (String, Arc<str>)>,
  ids: HashMap<String, FileId>,
}

impl FileHost {
  fn new(files: &[(String, String)]) -> FileHost {
    let mut map = HashMap::new();
    let mut ids = HashMap::new();
    for (idx, (path, text)) in files.iter().enumerate() {
      let id = FileId(idx as u32);
      ids.insert(path.clone(), id);
      map.insert(id, (path.clone(), Arc::from(text.clone())));
    }
    FileHost { files: map, ids }
  }

  fn file_id(&self, path: &str) -> FileId {
    *self
      .ids
      .get(path)
      .unwrap_or_else(|| panic!("missing file {}", path))
  }

  fn path(&self, id: FileId) -> Option<&str> {
    self.files.get(&id).map(|(p, _)| p.as_str())
  }
}

impl Host for FileHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .map(|(_, text)| text.clone())
      .ok_or_else(|| HostError::new(format!("missing file {:?}", file)))
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    let Some(from_path) = self.path(from) else {
      return None;
    };
    let mut path = PathBuf::from(from_path);
    path.pop();
    path.push(specifier);
    if path.extension().is_none() {
      path.set_extension("ts");
    }
    let normalized = normalize(&path);
    self.ids.get(&normalized).copied()
  }
}

fn normalize(path: &Path) -> String {
  use std::path::Component;

  let mut parts = Vec::new();
  for comp in path.components() {
    match comp {
      Component::CurDir => {}
      Component::ParentDir => {
        parts.pop();
      }
      Component::Normal(seg) => parts.push(seg.to_string_lossy().to_string()),
      other => parts.push(other.as_os_str().to_string_lossy().to_string()),
    }
  }
  parts.join("/")
}

fn load_fixture(name: &str) -> (FileHost, FileId) {
  let base = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("tests")
    .join("litmus")
    .join("type_annotation")
    .join(name);
  let mut files: Vec<(String, String)> = Vec::new();
  for entry in fs::read_dir(&base).expect("read fixture dir") {
    let entry = entry.expect("dir entry");
    if entry.file_type().expect("file type").is_file()
      && entry.path().extension().map(|e| e == "ts").unwrap_or(false)
    {
      let name = entry.file_name().into_string().expect("utf-8 file name");
      let text = fs::read_to_string(entry.path()).expect("read file");
      files.push((name, text));
    }
  }
  files.sort_by(|a, b| a.0.cmp(&b.0));
  let host = FileHost::new(&files);
  let main = host.file_id("main.ts");
  (host, main)
}

fn def_by_name(program: &mut Program, file: FileId, name: &str) -> typecheck_ts::DefId {
  program
    .definitions_in_file(file)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("definition {} not found in {:?}", name, file))
}

#[test]
fn qualified_type_reference_resolves() {
  let (host, main) = load_fixture("qualified_type_ref");
  let mut program = Program::new(host.clone(), vec![main]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let value_def = def_by_name(&mut program, host.file_id("main.ts"), "Value");
  let foo_def = def_by_name(&mut program, host.file_id("types.ts"), "Foo");
  let ty = program.type_of_def_interned(value_def);
  match program.interned_type_kind(ty) {
    TypeKind::Ref { def, args } => {
      assert_eq!(def, foo_def);
      assert!(args.is_empty());
    }
    other => panic!("expected ref to Foo, got {:?}", other),
  }
}

#[test]
fn import_type_resolves_to_module_export() {
  let (host, main) = load_fixture("import_type");
  let mut program = Program::new(host.clone(), vec![main]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let value_def = def_by_name(&mut program, host.file_id("main.ts"), "Value");
  let foo_def = def_by_name(&mut program, host.file_id("types.ts"), "Foo");
  let ty = program.type_of_def_interned(value_def);
  match program.interned_type_kind(ty) {
    TypeKind::Ref { def, args } => {
      assert_eq!(def, foo_def);
      assert!(args.is_empty());
    }
    other => panic!("expected ref to Foo, got {:?}", other),
  }
}

#[test]
fn typeof_query_resolves_value_definition() {
  let (host, main) = load_fixture("typeof_query");
  let mut program = Program::new(host.clone(), vec![main]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let alias_def = def_by_name(&mut program, host.file_id("main.ts"), "FooType");
  let foo_def = def_by_name(&mut program, host.file_id("main.ts"), "foo");
  let ty = program.type_of_def_interned(alias_def);
  match program.interned_type_kind(ty) {
    TypeKind::Ref { def, args } => {
      assert_eq!(def, foo_def);
      assert!(args.is_empty());
    }
    other => panic!("expected ref to foo, got {:?}", other),
  }
}

#[test]
fn type_params_shadow_type_names() {
  let (host, main) = load_fixture("type_param_shadow");
  let mut program = Program::new(host.clone(), vec![main]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let bar_def = def_by_name(&mut program, host.file_id("main.ts"), "Bar");
  let foo_def = def_by_name(&mut program, host.file_id("main.ts"), "Foo");
  let ty = program.type_of_def_interned(bar_def);
  let TypeKind::Ref { def, args } = program.interned_type_kind(ty) else {
    panic!("expected ref, got {:?}", program.interned_type_kind(ty));
  };
  assert_eq!(def, foo_def);
  assert_eq!(args.len(), 1);
  let arg_kind = program.interned_type_kind(args[0]);
  assert!(
    matches!(arg_kind, TypeKind::TypeParam(_)),
    "expected type param, got {:?}",
    arg_kind
  );
}
