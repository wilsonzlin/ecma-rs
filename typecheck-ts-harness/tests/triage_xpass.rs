use typecheck_ts_harness::triage;

#[test]
fn triage_counts_conformance_xpass() {
  let report = triage::analyze_report_json_str(
    r#"
{
  "compare_mode": "none",
  "results": [
    {
      "id": "a.ts",
      "outcome": "match",
      "rust": { "status": "ok", "diagnostics": [] },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "xfail", "expected": false, "from_manifest": true }
    }
  ]
}
"#,
    10,
  )
  .expect("analyze report");

  assert_eq!(report.mismatches, 0);
  assert_eq!(report.xpass, 1);
  assert!(
    report
      .suggestions
      .iter()
      .any(|s| s.id.as_deref() == Some("a.ts") && s.status == "pass"),
    "expected a pass suggestion for the xpass case; suggestions={:?}",
    report.suggestions
  );
}

#[test]
fn triage_counts_difftsc_xpass() {
  let report = triage::analyze_report_json_str(
    r#"
{
  "suite": "difftsc",
  "results": [
    {
      "name": "a",
      "status": "matched",
      "expectation": { "expectation": "flaky", "expected": false, "from_manifest": true }
    }
  ]
}
"#,
    10,
  )
  .expect("analyze report");

  assert_eq!(report.mismatches, 0);
  assert_eq!(report.xpass, 1);
  assert!(
    report
      .suggestions
      .iter()
      .any(|s| s.id.as_deref() == Some("difftsc/a") && s.status == "pass"),
    "expected a pass suggestion for the difftsc xpass case; suggestions={:?}",
    report.suggestions
  );
}

