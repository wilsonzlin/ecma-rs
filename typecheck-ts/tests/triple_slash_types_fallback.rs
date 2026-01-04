use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn triple_slash_types_resolves_via_at_types_fallback() {
  let mut host = MemoryHost::new();
  let entry = FileKey::new("entry.ts");
  let types = FileKey::new("@types/node/index.d.ts");

  host.insert(
    entry.clone(),
    Arc::from("/// <reference types=\"node\" />\nconst value = process;"),
  );
  host.insert(types.clone(), Arc::from("declare const process: number;"));
  // Simulate a host that only knows about the explicit `@types/*` package path.
  host.link(entry.clone(), "@types/node", types);

  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected triple-slash type reference to resolve via @types fallback, got {diagnostics:?}"
  );
}

