use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{lower_call_count, reset_lower_call_count, FileKey, MemoryHost, Program};

#[test]
fn lower_query_uses_cache_across_program_checks() {
  // Keep this test lightweight by disabling the bundled lib set and supplying a
  // single minimal `.d.ts` lib so the program does not emit `NO_LIBS_LOADED`.
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.include_dom = false;

  let mut host = MemoryHost::with_options(options);
  host.add_lib(LibFile {
    key: FileKey::new("lib:custom.d.ts"),
    name: Arc::from("custom.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("declare const __dummy: number;"),
  });

  let entry = FileKey::new("index.ts");
  let dep = FileKey::new("dep.ts");
  host.insert(
    entry.clone(),
    "import { value } from \"./dep\";\nexport const total = value;",
  );
  host.insert(dep.clone(), "export const value = 1;");

  let program = Program::new(host, vec![entry]);

  reset_lower_call_count();

  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let after_first = lower_call_count();
  assert!(
    after_first > 0,
    "initial `Program::check()` should perform at least one lowering"
  );

  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics after cached run, got {diagnostics:?}"
  );

  assert_eq!(
    after_first,
    lower_call_count(),
    "second `Program::check()` should reuse cached salsa lowering results"
  );
}
