use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::time::Instant;

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn cancel_check_returns_quickly() {
  const CANCEL_TIMEOUT: Duration = Duration::from_millis(500);

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
  let handle = thread::spawn(move || runner.check());

  thread::sleep(Duration::from_millis(10));
  let cancelled_at = Instant::now();
  program.cancel();

  let deadline = cancelled_at + CANCEL_TIMEOUT;
  while Instant::now() < deadline {
    if handle.is_finished() {
      break;
    }
    thread::sleep(Duration::from_millis(5));
  }
  if !handle.is_finished() {
    // Avoid leaving a runaway checker thread around: a leaked `JoinHandle` keeps
    // the test process alive and can hang CI indefinitely.
    eprintln!(
      "checker thread did not observe cancellation within {:?}; exiting to avoid hanging tests",
      CANCEL_TIMEOUT
    );
    std::process::exit(1);
  }

  let diagnostics = handle.join().expect("checker thread panicked");
  assert!(
    cancelled_at.elapsed() < CANCEL_TIMEOUT,
    "cancellation should complete quickly (within {:?})",
    CANCEL_TIMEOUT
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
