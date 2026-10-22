//! TS2318 "Cannot find global type" fires once per missing required global
//! (tsc `checkRequiredGlobalTypes`): 8 distinct diagnostics at the same
//! file-level span. Regression for the program-diagnostic dedupe collapsing
//! them to one (`triple_slash_no_default_lib` difftsc fixture).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn missing_core_globals_emit_one_ts2318_per_name() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let mut host = MemoryHost::with_options(options);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), "export const x = 1;\n");
  let program = Program::new(host, vec![file]);
  let ts2318: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2318")
    .collect();
  assert_eq!(
    ts2318.len(),
    8,
    "expected 8 TS2318 diagnostics (Array/Boolean/Function/IArguments/Number/Object/RegExp/String): {ts2318:?}"
  );
  // Distinct messages, one per required global name.
  let mut messages: Vec<_> = ts2318.iter().map(|d| d.message.clone()).collect();
  messages.sort();
  messages.dedup();
  assert_eq!(messages.len(), 8, "messages must be distinct: {messages:?}");
}
