use std::fs;
use std::time::Duration;
use tempfile::tempdir;
use typecheck_ts_harness::{run_conformance, CompareMode, ConformanceOptions, FailOn};

#[test]
fn conformance_reports_xpass_and_fail_on_new_fails() {
  let dir = tempdir().expect("tempdir");
  let root = dir.path();

  fs::write(
    root.join("a.ts"),
    "// @noLib: true\nexport const a = 1;\n",
  )
  .expect("write fixture");

  let manifest_path = root.join("manifest.toml");
  fs::write(
    &manifest_path,
    r#"
[[expectations]]
id = "a.ts"
status = "xfail"
"#,
  )
  .expect("write manifest");

  let mut options = ConformanceOptions::new(root.to_path_buf());
  options.compare = CompareMode::None;
  options.timeout = Duration::from_secs(5);
  options.jobs = 1;
  options.manifest = Some(manifest_path);

  // `fail_on=none` should succeed but still report XPASS in JSON.
  let mut allow_report_options = options.clone();
  allow_report_options.fail_on = FailOn::None;
  let report = run_conformance(allow_report_options).expect("run_conformance");
  assert_eq!(report.summary.outcomes.mismatches(), 0);
  assert_eq!(
    report
      .summary
      .mismatches
      .as_ref()
      .map(|m| m.xpass)
      .unwrap_or_default(),
    1
  );

  let json = serde_json::to_value(&report).expect("serialize report");
  assert_eq!(
    json
      .get("summary")
      .and_then(|s| s.get("mismatches"))
      .and_then(|m| m.get("xpass"))
      .and_then(|v| v.as_u64()),
    Some(1)
  );

  // `fail_on=new` should fail the run when XPASS is present.
  let mut fail_options = options;
  fail_options.fail_on = FailOn::New;
  assert!(run_conformance(fail_options).is_err());
}

