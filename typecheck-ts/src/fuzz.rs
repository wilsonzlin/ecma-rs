use std::collections::BTreeMap;
use std::sync::Arc;

use crate::lib_support::CompilerOptions;
use crate::{FileKey, Host, HostError, Program};

const MAX_FILES: usize = 8;
const MAX_IMPORTS_PER_FILE: usize = 4;
const MAX_PAYLOAD_BYTES: usize = 48;

struct ByteCursor<'a> {
  data: &'a [u8],
  offset: usize,
}

impl<'a> ByteCursor<'a> {
  fn new(data: &'a [u8]) -> Self {
    Self { data, offset: 0 }
  }

  fn next_u8(&mut self) -> u8 {
    let b = self.data.get(self.offset).copied().unwrap_or(0);
    self.offset = self.offset.saturating_add(1);
    b
  }

  fn next_bool(&mut self) -> bool {
    self.next_u8() & 1 == 1
  }

  fn next_usize(&mut self, max_exclusive: usize) -> usize {
    if max_exclusive == 0 {
      return 0;
    }
    (self.next_u8() as usize) % max_exclusive
  }

  fn take_bytes(&mut self, max_len: usize) -> &'a [u8] {
    let len = self.next_usize(max_len + 1);
    let end = self.offset.saturating_add(len).min(self.data.len());
    let slice = &self.data[self.offset.min(self.data.len())..end];
    self.offset = end;
    slice
  }
}

fn escape_bytes_as_js_string(bytes: &[u8]) -> String {
  let mut out = String::new();
  for b in bytes {
    use std::fmt::Write;
    let _ = write!(&mut out, "\\x{b:02x}");
  }
  out
}

struct FuzzHost {
  files: BTreeMap<FileKey, Arc<str>>,
  edges: BTreeMap<FileKey, BTreeMap<String, FileKey>>,
}

impl FuzzHost {
  fn from_bytes(data: &[u8]) -> (Self, Vec<FileKey>, bool) {
    let mut cursor = ByteCursor::new(data);
    let file_count = cursor.next_usize(MAX_FILES.saturating_sub(1)) + 1;
    let cancel_immediately = cursor.next_bool() || data.len() > 16 * 1024;

    let keys: Vec<FileKey> = (0..file_count)
      .map(|idx| FileKey::new(format!("file{idx}.ts")))
      .collect();

    let mut roots = Vec::new();
    roots.push(keys[0].clone());
    // Add a couple more roots to exercise multiple-entry programs.
    for key in keys.iter().skip(1) {
      if cursor.next_bool() {
        roots.push(key.clone());
      }
      if roots.len() >= 3 {
        break;
      }
    }
    roots.sort_unstable_by(|a, b| a.as_str().cmp(b.as_str()));
    roots.dedup_by(|a, b| a.as_str() == b.as_str());

    let mut files = BTreeMap::new();
    let mut edges: BTreeMap<FileKey, BTreeMap<String, FileKey>> = BTreeMap::new();

    for (idx, key) in keys.iter().enumerate() {
      let import_count = if file_count <= 1 {
        0
      } else {
        cursor.next_usize(MAX_IMPORTS_PER_FILE + 1)
      };

      let mut file_edges = BTreeMap::new();
      let mut source = String::new();
      source.push_str(&format!("// fuzz module {idx}\n"));

      for import_idx in 0..import_count {
        let target = cursor.next_usize(file_count);
        let spec = if cursor.next_bool() {
          format!("./file{target}")
        } else {
          format!("./file{target}.ts")
        };
        source.push_str(&format!(
          "import {{ fun{target} as imp{idx}_{import_idx} }} from \"{spec}\";\n"
        ));
        file_edges.insert(spec, keys[target].clone());
      }

      // Keep the body parseable while still embedding raw bytes by escaping them.
      let payload = escape_bytes_as_js_string(cursor.take_bytes(MAX_PAYLOAD_BYTES));
      source.push_str(&format!("export const payload{idx} = \"{payload}\";\n"));
      source.push_str(&format!(
        "export function fun{idx}(x: number) {{ return x + {idx}; }}\n"
      ));

      for import_idx in 0..import_count {
        let arg = if cursor.next_bool() {
          format!("{idx}")
        } else {
          "\"x\" as any".to_string()
        };
        source.push_str(&format!(
          "export const call{idx}_{import_idx} = imp{idx}_{import_idx}({arg});\n"
        ));
      }

      files.insert(key.clone(), Arc::from(source));
      edges.insert(key.clone(), file_edges);
    }

    (Self { files, edges }, roots, cancel_immediately)
  }
}

impl Host for FuzzHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("unknown file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, spec: &str) -> Option<FileKey> {
    self
      .edges
      .get(from)
      .and_then(|edges| edges.get(spec))
      .cloned()
  }

  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions {
      include_dom: false,
      no_default_lib: true,
      ..CompilerOptions::default()
    }
  }
}

/// Fuzz entry point that parses, lowers, binds, and checks a synthetic multi-file
/// program derived from arbitrary bytes without panicking.
#[cfg(feature = "fuzzing")]
#[doc(hidden)]
pub fn fuzz_typecheck_pipeline(data: &[u8]) {
  let (host, roots, cancel_immediately) = FuzzHost::from_bytes(data);
  if roots.is_empty() {
    return;
  }
  let program = Program::new(host, roots);
  if cancel_immediately {
    program.cancel();
  }

  let _ = program.check();

  for file in program.reachable_files().into_iter().take(MAX_FILES) {
    let _ = program.exports_of(file);
    for def in program.definitions_in_file(file) {
      let ty = program.type_of_def(def);
      let _ = program.display_type(ty).to_string();
      if let Some(body) = program.body_of_def(def) {
        let result = program.check_body(body);
        let _ = result.diagnostics();
      }
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
