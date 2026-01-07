use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{FileId, FileKey, MemoryHost, Program, ProgramSnapshot};

fn file_key_map(snapshot: &ProgramSnapshot) -> HashMap<FileId, FileKey> {
  snapshot
    .files
    .iter()
    .map(|file| (file.file, file.key.clone()))
    .collect()
}

#[test]
fn snapshot_does_not_include_stale_module_resolution_edges() {
  let mut host = MemoryHost::new();
  let index = FileKey::new("index.ts");
  let a = FileKey::new("a.ts");

  host.insert(
    index.clone(),
    Arc::from("import { value } from \"./a\";\nexport const x = value;\n"),
  );
  host.insert(a.clone(), Arc::from("export const value = 1;\n"));
  host.link(index.clone(), "./a", a.clone());

  let mut program = Program::new(host.clone(), vec![index.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let snapshot = program.snapshot();
  let keys = file_key_map(&snapshot);
  assert!(
    snapshot.module_resolutions.iter().any(|resolution| {
      keys
        .get(&resolution.from)
        .is_some_and(|key| key.as_str() == index.as_str())
        && resolution.specifier == "./a"
    }),
    "expected snapshot to include module resolution edge index.ts -> ./a, got {:?}",
    snapshot.module_resolutions
  );

  let index_id = program.file_id(&index).expect("index id");
  program.set_file_text(index_id, Arc::from("export const x = 1;\n"));
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let snapshot = program.snapshot();
  let keys = file_key_map(&snapshot);
  assert!(
    !snapshot.module_resolutions.iter().any(|resolution| {
      keys
        .get(&resolution.from)
        .is_some_and(|key| key.as_str() == index.as_str())
        && resolution.specifier == "./a"
    }),
    "stale module resolution edge index.ts -> ./a leaked into snapshot: {:?}",
    snapshot.module_resolutions
  );

  let restored = Program::from_snapshot(host, snapshot);
  let reachable = restored.reachable_files();
  let reachable_keys: Vec<_> = reachable
    .iter()
    .filter_map(|file| restored.file_key(*file))
    .map(|key| key.to_string())
    .collect();
  assert!(
    !reachable_keys.iter().any(|key| key == a.as_str()),
    "restored snapshot should not reach a.ts, got reachable files {reachable_keys:?}",
  );
}
