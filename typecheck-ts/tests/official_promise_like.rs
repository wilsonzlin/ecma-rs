use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibName, ScriptTarget};
use typecheck_ts::{FileKey, Host, HostError, Program};

const ENTRY: &str = r#"
declare const x: PromiseLike<string>;
const y = x.then((v) => v);
"#;

#[derive(Default)]
struct TestHost {
  files: HashMap<FileKey, Arc<str>>,
  options: CompilerOptions,
}

impl TestHost {
  fn new(options: CompilerOptions) -> Self {
    Self {
      files: HashMap::new(),
      options,
    }
  }

  fn with_file(mut self, key: FileKey, text: &str) -> Self {
    self.files.insert(key, Arc::from(text));
    self
  }
}

impl Host for TestHost {
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

  fn file_kind(&self, file: &FileKey) -> FileKind {
    let _ = file;
    FileKind::Ts
  }
}

#[test]
fn program_check_terminates_with_recursive_promise_like() {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  options.libs = vec![
    LibName::parse("esnext").expect("esnext lib"),
    LibName::parse("esnext.disposable").expect("esnext.disposable lib"),
  ];
  options.skip_lib_check = false;

  let entry = FileKey::new("entry.ts");
  let host = TestHost::new(options).with_file(entry.clone(), ENTRY);
  let program = Program::new(host, vec![entry]);

  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
}
