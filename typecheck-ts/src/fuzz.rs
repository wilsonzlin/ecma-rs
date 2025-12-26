use std::sync::Arc;

use crate::lib_support::CompilerOptions;
use crate::{FileId, Host, HostError, Program};

struct FuzzHost {
  file: FileId,
  source: Arc<str>,
}

impl FuzzHost {
  fn new(source: String) -> Self {
    Self {
      file: FileId(0),
      source: Arc::from(source),
    }
  }
}

impl Host for FuzzHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    if file == self.file {
      Ok(self.source.clone())
    } else {
      Err(HostError::new(format!("unknown file {file:?}")))
    }
  }

  fn resolve(&self, _from: FileId, _spec: &str) -> Option<FileId> {
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
  let root = host.file;
  let program = Program::new(host, vec![root]);

  let _ = program.check();
  let _ = program.exports_of(root);
  for def in program.definitions_in_file(root) {
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
