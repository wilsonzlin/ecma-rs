use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::time::Instant;

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn cancel_check_returns_quickly() {
  let mut host = MemoryHost::new();
  let mut source = String::new();
  source.push_str("export function main() { return 0; }\n");
  for idx in 0..500 {
    source.push_str(&format!(
      "export function f{idx}(value: number) {{ let x = value + {idx}; return x * {idx}; }}\n"
    ));
  }
  let file = FileKey::new("file0.ts");
  host.insert(file.clone(), Arc::from(source));

  let program = Arc::new(Program::new(host, vec![file.clone()]));
  let runner = Arc::clone(&program);
  let (tx, rx) = mpsc::channel();
  thread::spawn(move || {
    let diags = runner.check();
    let _ = tx.send(diags);
  });

  thread::sleep(Duration::from_millis(10));
  let cancelled_at = Instant::now();
  program.cancel();

  let diagnostics = rx
    .recv_timeout(Duration::from_millis(500))
    .expect("checker thread should observe cancellation quickly");
  assert!(
    cancelled_at.elapsed() < Duration::from_millis(500),
    "cancellation should complete quickly"
  );
  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::CANCELLED.id),
    "expected cancellation diagnostic"
  );

  program.clear_cancellation();
  let post_cancel_diags = program.check();
  assert!(
    post_cancel_diags
      .iter()
      .all(|diag| diag.code.as_str() != codes::CANCELLED.id),
    "cancellation should not poison subsequent checks"
  );
}
