use std::fs;
use std::path::Path;
use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

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

fn load_fixture(name: &str) -> (MemoryHost, Vec<FileKey>) {
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
  let mut host = MemoryHost::default();
  let mut roots = Vec::new();
  for (path, text) in files {
    let key = FileKey::new(path.clone());
    host.insert(key, Arc::from(text));
    roots.push(FileKey::new(path));
  }
  (host, roots)
}

fn def_by_name(program: &mut Program, file: FileKey, name: &str) -> typecheck_ts::DefId {
  let file_id = program.file_id(&file).unwrap();
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("definition {} not found in {:?}", name, file_id))
}

#[test]
fn qualified_type_reference_resolves() {
  let (host, roots) = load_fixture("qualified_type_ref");
  let mut program = Program::new(host.clone(), roots.clone());
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let value_def = def_by_name(&mut program, FileKey::new("main.ts"), "Value");
  let foo_def = def_by_name(&mut program, FileKey::new("types.ts"), "Foo");
  let ty = program.type_of_def_interned(value_def);
  match program.interned_type_kind(ty) {
    TypeKind::Ref { def, args } => {
      eprintln!(
        "value def {:?} name {:?}, foo def {:?} name {:?}, ref def name {:?}",
        value_def,
        program.def_name(value_def),
        foo_def,
        program.def_name(foo_def),
        program.def_name(def)
      );
      assert_eq!(def, foo_def);
      assert!(args.is_empty());
    }
    other => panic!("expected ref to Foo, got {:?}", other),
  }
}

#[test]
fn import_type_resolves_to_module_export() {
  let (host, roots) = load_fixture("import_type");
  let mut program = Program::new(host.clone(), roots.clone());
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let value_def = def_by_name(&mut program, FileKey::new("main.ts"), "Value");
  let foo_def = def_by_name(&mut program, FileKey::new("types.ts"), "Foo");
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
  let (host, roots) = load_fixture("typeof_query");
  let mut program = Program::new(host.clone(), roots.clone());
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let alias_def = def_by_name(&mut program, FileKey::new("main.ts"), "FooType");
  let foo_def = def_by_name(&mut program, FileKey::new("main.ts"), "foo");
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
  let (host, roots) = load_fixture("type_param_shadow");
  let mut program = Program::new(host.clone(), roots.clone());
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  let file_id = program.file_id(&FileKey::new("main.ts")).unwrap();
  for def in program.definitions_in_file(file_id) {
    println!("def {:?} name {:?}", def, program.def_name(def));
  }
  let foo_def = def_by_name(&mut program, FileKey::new("main.ts"), "Foo");
  let bar_def = def_by_name(&mut program, FileKey::new("main.ts"), "Bar");
  println!(
    "bar type {:?}",
    program.interned_type_kind(program.type_of_def_interned(bar_def))
  );
  println!(
    "bar expanded {:?}",
    program.type_kind(program.type_of_def_interned(bar_def))
  );
  println!(
    "foo type {:?}",
    program.interned_type_kind(program.type_of_def_interned(foo_def))
  );
  let ty = program.type_of_def_interned(bar_def);
  let TypeKind::Ref { def, args } = program.interned_type_kind(ty) else {
    panic!("expected ref, got {:?}", program.interned_type_kind(ty));
  };
  println!(
    "foo_def {:?} bar_def {:?} ty def {:?} args {:?}",
    foo_def, bar_def, def, args
  );
  println!(
    "arg kinds {:?}",
    args
      .iter()
      .map(|a| program.interned_type_kind(*a))
      .collect::<Vec<_>>()
  );
  assert_eq!(def, foo_def);
  assert_eq!(args.len(), 1);
  let arg_kind = program.interned_type_kind(args[0]);
  assert!(
    matches!(arg_kind, TypeKind::TypeParam(_)),
    "expected type param, got {:?}",
    arg_kind
  );
}
