use std::sync::{Arc, Barrier};

use typecheck_ts::codes;
use typecheck_ts::{FatalError, FileKey, Host, HostError, Program, Severity};

struct PanickingHost;

impl Host for PanickingHost {
  fn file_text(&self, _file: &FileKey) -> Result<Arc<str>, HostError> {
    panic!("forced invariant failure");
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }
}

#[test]
fn internal_failure_surfaces_as_ice() {
  let program = Program::new(PanickingHost, vec![FileKey::new("input.ts")]);
  match program.check_fallible() {
    Err(FatalError::Ice(_)) => {}
    other => panic!("expected fatal ICE, got {other:?}"),
  }

  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1);
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::INTERNAL_COMPILER_ERROR.as_str());
  assert_eq!(diag.severity, Severity::Error);
  assert!(
    diag
      .notes
      .iter()
      .any(|note| note.contains("please file an issue")),
    "ICE diagnostics should include a help note"
  );
}

struct ParallelPanickingHost;

impl Host for ParallelPanickingHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    if file == &FileKey::new("panic.ts") {
      panic!("panic during parallel check");
    }
    if file == &FileKey::new("main.ts") {
      return Ok("import './panic.ts'; export const value = 1;".into());
    }
    Err(HostError::new("unexpected file"))
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    if from == &FileKey::new("main.ts") && specifier == "./panic.ts" {
      Some(FileKey::new("panic.ts"))
    } else {
      None
    }
  }
}

#[test]
fn panic_during_parallel_check_is_caught() {
  let program = Arc::new(Program::new(
    ParallelPanickingHost,
    vec![FileKey::new("main.ts")],
  ));
  std::thread::scope(|scope| {
    let barrier = Arc::new(Barrier::new(2));
    let program_a = Arc::clone(&program);
    let program_b = Arc::clone(&program);
    let barrier_a = Arc::clone(&barrier);
    let barrier_b = Arc::clone(&barrier);
    let first = scope.spawn(move || {
      barrier_a.wait();
      program_a.check_fallible()
    });
    let second = scope.spawn(move || {
      barrier_b.wait();
      program_b.check_fallible()
    });
    let res1 = first.join().unwrap();
    let res2 = second.join().unwrap();
    assert!(
      matches!(res1, Err(FatalError::Ice(_))) || matches!(res2, Err(FatalError::Ice(_))),
      "panic should surface as ICE"
    );
    for res in [res1, res2] {
      if let Err(fatal) = res {
        assert!(
          matches!(fatal, FatalError::Ice(_) | FatalError::Cancelled),
          "expected ICE or cancellation after panic, got {fatal:?}"
        );
      }
    }
  });
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::INTERNAL_COMPILER_ERROR.as_str()
  );
}
