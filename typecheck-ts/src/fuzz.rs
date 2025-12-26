use std::sync::Arc;

use crate::lib_support::CompilerOptions;
use crate::{FileKey, Host, HostError, Program};

struct FuzzHost {
  key: FileKey,
  source: Arc<str>,
}

impl FuzzHost {
  fn new(source: String) -> Self {
    Self {
      key: FileKey::new("fuzz.ts"),
      source: Arc::from(source),
    }
  }
}

impl Host for FuzzHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    if file == &self.key {
      Ok(self.source.clone())
    } else {
      Err(HostError::new(format!("unknown file {file:?}")))
    }
  }

  fn resolve(&self, _from: &FileKey, _spec: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions {
      include_dom: false,
      no_default_lib: true,
      ..CompilerOptions::default()
    }
  }
}

/// Fuzz entry point that parses, lowers, binds, and checks arbitrary UTF-8 input
/// (lossily converted from raw bytes) without panicking.
#[cfg(feature = "fuzzing")]
#[doc(hidden)]
pub fn fuzz_typecheck_pipeline(data: &[u8]) {
  let source = String::from_utf8_lossy(data).into_owned();
  let host = FuzzHost::new(source);
  let root = host.key.clone();
  let program = Program::new(host, vec![root.clone()]);

  let _ = program.check();
  let Some(root_id) = program.file_id(&root) else {
    return;
  };
  let _ = program.exports_of(root_id);
  for def in program.definitions_in_file(root_id) {
    let ty = program.type_of_def(def);
    let _ = program.display_type(ty).to_string();
    if let Some(body) = program.body_of_def(def) {
      let result = program.check_body(body);
      let _ = result.diagnostics();
    }
  }
}

/// Fuzz entry point that exercises type relation and evaluation on random graphs
/// using the interned type store.
#[cfg(feature = "fuzzing")]
#[doc(hidden)]
pub fn fuzz_type_graph(data: &[u8]) {
  types_ts_interned::fuzz_type_graph(data);
}
