use std::path::PathBuf;
use std::time::Duration;

use typecheck_ts::lib_support::{LibName, ModuleKind, ScriptTarget};
use typecheck_ts_harness::runner::EngineStatus;
use typecheck_ts_harness::{run_conformance, CompareMode, ConformanceOptions};

fn conformance_options(compare: CompareMode) -> ConformanceOptions {
  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let mut options = ConformanceOptions::new(root);
  options.compare = compare;
  // Parsing and binding the bundled standard library can be relatively expensive
  // in debug builds. Keep the harness timeout high enough that the option
  // plumbing tests are robust on slower CI runners.
  options.timeout = Duration::from_secs(15);
  options.allow_mismatches = true;
  options
}

#[test]
#[cfg(feature = "with-node")]
fn strict_null_checks_directive_reaches_tsc() {
  let options = conformance_options(CompareMode::Tsc);
  let report = run_conformance(options).expect("run conformance");
  let enabled = report
    .results
    .iter()
    .find(|r| r.id.ends_with("strict_null_checks_enabled.ts"))
    .expect("enabled strictNullChecks fixture");
  let disabled = report
    .results
    .iter()
    .find(|r| r.id.ends_with("strict_null_checks_disabled.ts"))
    .expect("disabled strictNullChecks fixture");

  if enabled.tsc.status != EngineStatus::Ok || disabled.tsc.status != EngineStatus::Ok {
    eprintln!("skipping strict null checks test: tsc unavailable");
    return;
  }

  assert!(
    !enabled.tsc.diagnostics.is_empty(),
    "expected diagnostics when strictNullChecks is enabled"
  );
  assert!(
    disabled.tsc.diagnostics.is_empty(),
    "expected no diagnostics when strictNullChecks is disabled"
  );
}

#[test]
#[cfg(not(feature = "with-node"))]
fn strict_null_checks_directive_reaches_tsc() {
  eprintln!("skipping strict null checks test: built without node");
}

#[test]
fn strict_null_checks_directive_reaches_rust_checker() {
  let options = conformance_options(CompareMode::None);
  let report = run_conformance(options).expect("run conformance");

  let enabled = report
    .results
    .iter()
    .find(|r| r.id.ends_with("strict_null_checks_enabled.ts"))
    .expect("enabled strictNullChecks fixture");
  let disabled = report
    .results
    .iter()
    .find(|r| r.id.ends_with("strict_null_checks_disabled.ts"))
    .expect("disabled strictNullChecks fixture");

  assert_eq!(enabled.rust.status, EngineStatus::Ok);
  assert_eq!(disabled.rust.status, EngineStatus::Ok);
  assert!(
    !enabled.rust.diagnostics.is_empty(),
    "expected diagnostics when strictNullChecks is enabled for Rust checker"
  );
  assert!(
    disabled.rust.diagnostics.is_empty(),
    "expected no diagnostics when strictNullChecks is disabled for Rust checker"
  );
}

#[test]
fn exposes_applied_options_for_multi_file_fixture() {
  let options = conformance_options(CompareMode::None);
  let report = run_conformance(options).expect("run conformance");

  let result = report
    .results
    .iter()
    .find(|r| r.id.ends_with("options_passthrough.ts"))
    .expect("options_passthrough fixture");

  assert_eq!(result.options.harness.no_lib, Some(true));
  assert_eq!(result.options.harness.lib, vec!["es2020"]);
  assert_eq!(result.options.harness.types, vec!["example"]);
  assert_eq!(
    result.options.harness.module_resolution.as_deref(),
    Some("node16")
  );
  assert_eq!(
    result.options.harness.use_define_for_class_fields,
    Some(false)
  );
  assert_eq!(
    result.options.harness.no_unchecked_indexed_access,
    Some(true)
  );
  assert_eq!(result.options.harness.declaration, Some(true));

  assert!(result.options.rust.no_default_lib);
  assert_eq!(
    result.options.rust.libs,
    vec![LibName::parse("es2020").expect("es2020 lib")]
  );
  assert_eq!(
    result.options.rust.module_resolution.as_deref(),
    Some("node16")
  );
  assert_eq!(result.options.rust.types, vec!["example".to_string()]);
  assert_eq!(
    result.options.rust.module,
    Some(ModuleKind::NodeNext),
    "module directive should apply program-wide"
  );
  assert_eq!(result.options.rust.target, ScriptTarget::Es2020);
  assert!(!result.options.rust.use_define_for_class_fields);
  assert!(result.options.rust.no_unchecked_indexed_access);
  assert_eq!(
    result
      .options
      .tsc
      .get("moduleResolution")
      .and_then(|v| v.as_str()),
    Some("node16")
  );
  assert_eq!(
    result.options.tsc.get("noLib").and_then(|v| v.as_bool()),
    Some(true)
  );
}

#[test]
fn exposes_applied_lib_list_with_dotted_names() {
  let options = conformance_options(CompareMode::None);
  let report = run_conformance(options).expect("run conformance");

  let result = report
    .results
    .iter()
    .find(|r| r.id.ends_with("lib_names_dotted.ts"))
    .expect("lib_names_dotted fixture");

  assert_eq!(result.options.harness.lib, vec!["DOM.Iterable", "es2015.promise"]);
  assert!(!result.options.rust.no_default_lib);
  assert_eq!(
    result.options.rust.libs,
    vec![
      LibName::parse("dom.iterable").expect("dom.iterable lib"),
      LibName::parse("es2015.promise").expect("es2015.promise lib"),
    ],
  );
}
