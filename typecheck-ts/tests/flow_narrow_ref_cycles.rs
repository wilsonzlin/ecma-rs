use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn in_check_narrowing_is_cycle_safe() {
  let source = r#"
    type Loop = Loop;

    const x = null as any as Loop;
    if ("value" in x) {
      // no-op
    }
  "#;

  let mut host = MemoryHost::default();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), Arc::from(source));

  let program = Program::new(host, vec![key]);
  let mut first = program.check();
  let mut second = program.check();
  codes::normalize_diagnostics(&mut first);
  codes::normalize_diagnostics(&mut second);
  assert_eq!(first, second);
}
