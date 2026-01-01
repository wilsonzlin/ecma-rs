use std::sync::Arc;

use typecheck_ts::db::{set_parallel_tracker, ParallelTracker};
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn program_check_runs_bodies_in_parallel() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..Default::default()
  });
  let file = FileKey::new("entry.ts");
  let mut source = String::new();
  source.push_str("export const seed: number = 0;\n");
  for idx in 0..64 {
    source.push_str(&format!(
      "export function f{idx}(value: number): number {{ let x = value + {idx}; return x * {idx}; }}\n"
    ));
  }
  host.insert(file.clone(), Arc::<str>::from(source));

  let program = Program::new(host, vec![file]);
  let tracker = Arc::new(ParallelTracker::new());
  set_parallel_tracker(Some(Arc::clone(&tracker)));
  struct Reset;
  impl Drop for Reset {
    fn drop(&mut self) {
      set_parallel_tracker(None);
    }
  }
  let _reset = Reset;

  let pool = rayon::ThreadPoolBuilder::new()
    .num_threads(4)
    .build()
    .expect("build rayon pool");
  let _ = pool.install(|| program.check());

  assert!(
    tracker.max_active() > 1,
    "expected parallel body checking (max_active = {})",
    tracker.max_active()
  );
}
