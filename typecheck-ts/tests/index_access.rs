use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, Host, HostError, Program};

#[derive(Clone)]
struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
  libs: Vec<LibFile>,
  options: CompilerOptions,
}

impl MemoryHost {
  fn new(options: CompilerOptions) -> Self {
    let mut files = HashMap::new();
    let lib_key = FileKey::new("test-lib.d.ts");
    let lib_text: Arc<str> = Arc::from("declare const __typecheck_ts_test: any;\n".to_string());
    files.insert(lib_key.clone(), Arc::clone(&lib_text));
    let libs = vec![LibFile {
      key: lib_key,
      name: Arc::from("test-lib.d.ts"),
      kind: FileKind::Dts,
      text: lib_text,
    }];
    Self {
      files,
      libs,
      options,
    }
  }

  fn insert(&mut self, key: FileKey, source: &str) {
    self.files.insert(key, Arc::from(source.to_string()));
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    if self.libs.iter().any(|lib| lib.key == *file) {
      FileKind::Dts
    } else {
      FileKind::Ts
    }
  }
}

#[test]
fn computed_access_literal_key_uses_named_property() {
  let mut opts = CompilerOptions::default();
  opts.no_default_lib = true;

  let entry = FileKey::new("index.ts");
  let mut host = MemoryHost::new(opts);
  host.insert(
    entry.clone(),
    "const obj = { a: 1 } as const;\nexport const x = obj[\"a\"];",
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id");
  let exports = program.exports_of(file_id);
  let x_entry = exports.get("x").expect("x export");
  let def = x_entry.def.expect("x definition");
  let ty = program.type_of_def(def);
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn computed_access_uses_string_index_signature() {
  let mut opts = CompilerOptions::default();
  opts.no_default_lib = true;

  let entry = FileKey::new("index.ts");
  let mut host = MemoryHost::new(opts);
  host.insert(
    entry.clone(),
    "declare const dict: { [k: string]: number };\nexport const y = dict[\"any\"];",
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id");
  let exports = program.exports_of(file_id);
  let y_entry = exports.get("y").expect("y export");
  let def = y_entry.def.expect("y definition");
  let ty = program.type_of_def(def);
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn no_unchecked_indexed_access_adds_undefined_to_computed_access() {
  let mut opts = CompilerOptions::default();
  opts.no_default_lib = true;
  opts.no_unchecked_indexed_access = true;

  let entry = FileKey::new("index.ts");
  let mut host = MemoryHost::new(opts);
  host.insert(
    entry.clone(),
    "declare const dict: { [k: string]: number };\nexport const y = dict[\"any\"];",
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id");
  let exports = program.exports_of(file_id);
  let y_entry = exports.get("y").expect("y export");
  let def = y_entry.def.expect("y definition");
  let ty = program.type_of_def(def);
  assert_eq!(program.display_type(ty).to_string(), "undefined | number");
}
