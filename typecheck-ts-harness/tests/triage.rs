use assert_cmd::Command;
use std::fs;
use std::time::Duration;
use tempfile::tempdir;

const CLI_TIMEOUT: Duration = Duration::from_secs(30);

const CONFORMANCE_REPORT: &str = r#"
{
  "compare_mode": "tsc",
  "results": [
    {
      "id": "compiler/a.ts",
      "outcome": "rust_missing_diagnostics",
      "rust": { "status": "ok", "diagnostics": [] },
      "tsc": {
        "status": "ok",
        "diagnostics": [
          { "engine": "tsc", "code": 1111, "file": "/a.ts", "start": 0, "end": 1 }
        ]
      },
      "detail": {
        "message": "missing diagnostic",
        "tsc": { "engine": "tsc", "code": 1111, "file": "/a.ts", "start": 0, "end": 1 }
      },
      "expectation": { "expectation": "pass", "expected": false }
    },
    {
      "id": "compiler/b.ts",
      "outcome": "code_mismatch",
      "rust": {
        "status": "ok",
        "diagnostics": [
          { "engine": "rust", "code": "TS9999", "file": "/b.ts", "start": 0, "end": 1 }
        ]
      },
      "tsc": {
        "status": "ok",
        "diagnostics": [
          { "engine": "tsc", "code": 2345, "file": "/b.ts", "start": 0, "end": 1 }
        ]
      },
      "detail": {
        "message": "code mismatch",
        "rust": { "engine": "rust", "code": "TS9999", "file": "/b.ts", "start": 0, "end": 1 },
        "tsc": { "engine": "tsc", "code": 2345, "file": "/b.ts", "start": 0, "end": 1 }
      },
      "expectation": { "expectation": "xfail", "expected": true, "from_manifest": true }
    },
    {
      "id": "checker/c.ts",
      "outcome": "rust_extra_diagnostics",
      "rust": {
        "status": "ok",
        "diagnostics": [
          { "engine": "rust", "code": "TS1111", "file": "/c.ts", "start": 0, "end": 1 }
        ]
      },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": false }
    },
    {
      "id": "checker/d.ts",
      "outcome": "rust_extra_diagnostics",
      "rust": {
        "status": "ok",
        "diagnostics": [
          { "engine": "rust", "code": "TS9999", "file": "/d.ts", "start": 0, "end": 1 }
        ]
      },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": false }
    },
    {
      "id": "ok/e.ts",
      "outcome": "match",
      "rust": { "status": "ok", "diagnostics": [] },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": true }
    }
  ]
}
"#;

const CONFORMANCE_BASELINE_REPORT: &str = r#"
{
  "compare_mode": "tsc",
  "results": [
    {
      "id": "compiler/a.ts",
      "outcome": "match",
      "rust": { "status": "ok", "diagnostics": [] },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": true }
    },
    {
      "id": "compiler/b.ts",
      "outcome": "code_mismatch",
      "rust": {
        "status": "ok",
        "diagnostics": [
          { "engine": "rust", "code": "TS9999", "file": "/b.ts", "start": 0, "end": 1 }
        ]
      },
      "tsc": {
        "status": "ok",
        "diagnostics": [
          { "engine": "tsc", "code": 2345, "file": "/b.ts", "start": 0, "end": 1 }
        ]
      },
      "expectation": { "expectation": "xfail", "expected": true, "from_manifest": true }
    },
    {
      "id": "checker/c.ts",
      "outcome": "rust_extra_diagnostics",
      "rust": {
        "status": "ok",
        "diagnostics": [
          { "engine": "rust", "code": "TS1111", "file": "/c.ts", "start": 0, "end": 1 }
        ]
      },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": false }
    },
    {
      "id": "checker/d.ts",
      "outcome": "match",
      "rust": { "status": "ok", "diagnostics": [] },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": true }
    },
    {
      "id": "ok/e.ts",
      "outcome": "match",
      "rust": { "status": "ok", "diagnostics": [] },
      "tsc": { "status": "ok", "diagnostics": [] },
      "expectation": { "expectation": "pass", "expected": true }
    }
  ]
}
"#;

const EXPECTED_CONFORMANCE_TRIAGE: &str = r#"{
  "kind": "conformance",
  "top": 5,
  "total": 5,
  "mismatches": 4,
  "unexpected_mismatches": 3,
  "mismatches_without_code": 0,
  "top_outcomes": [
    {
      "key": "rust_extra_diagnostics",
      "count": 2
    },
    {
      "key": "code_mismatch",
      "count": 1
    },
    {
      "key": "rust_missing_diagnostics",
      "count": 1
    }
  ],
  "top_codes": [
    {
      "key": "TS1111",
      "count": 2
    },
    {
      "key": "TS2345",
      "count": 1
    },
    {
      "key": "TS9999",
      "count": 1
    }
  ],
  "top_prefixes": [
    {
      "key": "checker",
      "count": 2
    },
    {
      "key": "compiler",
      "count": 2
    }
  ],
  "regressions": [
    {
      "id": "checker/c.ts",
      "outcome": "rust_extra_diagnostics",
      "code": "TS1111",
      "prefix": "checker"
    },
    {
      "id": "checker/d.ts",
      "outcome": "rust_extra_diagnostics",
      "code": "TS9999",
      "prefix": "checker"
    },
    {
      "id": "compiler/a.ts",
      "outcome": "rust_missing_diagnostics",
      "code": "TS1111",
      "prefix": "compiler"
    }
  ],
  "suggestions": [
    {
      "id": "checker/c.ts",
      "status": "xfail",
      "reason": "triage: rust_extra_diagnostics TS1111"
    },
    {
      "id": "checker/d.ts",
      "status": "xfail",
      "reason": "triage: rust_extra_diagnostics TS9999"
    },
    {
      "id": "compiler/a.ts",
      "status": "xfail",
      "reason": "triage: rust_missing_diagnostics TS1111"
    }
  ]
}
"#;

const EXPECTED_CONFORMANCE_TRIAGE_WITH_BASELINE: &str = r#"{
  "kind": "conformance",
  "top": 5,
  "total": 5,
  "mismatches": 4,
  "unexpected_mismatches": 3,
  "mismatches_without_code": 0,
  "top_outcomes": [
    {
      "key": "rust_extra_diagnostics",
      "count": 2
    },
    {
      "key": "code_mismatch",
      "count": 1
    },
    {
      "key": "rust_missing_diagnostics",
      "count": 1
    }
  ],
  "top_codes": [
    {
      "key": "TS1111",
      "count": 2
    },
    {
      "key": "TS2345",
      "count": 1
    },
    {
      "key": "TS9999",
      "count": 1
    }
  ],
  "top_prefixes": [
    {
      "key": "checker",
      "count": 2
    },
    {
      "key": "compiler",
      "count": 2
    }
  ],
  "regressions": [
    {
      "id": "checker/c.ts",
      "outcome": "rust_extra_diagnostics",
      "code": "TS1111",
      "prefix": "checker"
    },
    {
      "id": "checker/d.ts",
      "outcome": "rust_extra_diagnostics",
      "code": "TS9999",
      "prefix": "checker"
    },
    {
      "id": "compiler/a.ts",
      "outcome": "rust_missing_diagnostics",
      "code": "TS1111",
      "prefix": "compiler"
    }
  ],
  "suggestions": [
    {
      "id": "checker/c.ts",
      "status": "xfail",
      "reason": "triage: rust_extra_diagnostics TS1111"
    },
    {
      "id": "checker/d.ts",
      "status": "xfail",
      "reason": "triage: rust_extra_diagnostics TS9999"
    },
    {
      "id": "compiler/a.ts",
      "status": "xfail",
      "reason": "triage: rust_missing_diagnostics TS1111"
    }
  ],
  "baseline": {
    "baseline_total": 5,
    "baseline_mismatches": 2,
    "new_cases": 0,
    "missing_cases": 0,
    "regressed": 2,
    "fixed": 0,
    "regressions": [
      {
        "id": "checker/d.ts",
        "outcome": "rust_extra_diagnostics",
        "code": "TS9999",
        "prefix": "checker"
      },
      {
        "id": "compiler/a.ts",
        "outcome": "rust_missing_diagnostics",
        "code": "TS1111",
        "prefix": "compiler"
      }
    ],
    "fixes": []
  }
}
"#;

const DIFFTSC_REPORT: &str = r#"
{
  "suite": "difftsc",
  "results": [
    {
      "name": "a",
      "status": "mismatch",
      "diff": {
        "missing": [
          { "engine": "tsc", "code": 1111, "file": "/a.ts", "start": 0, "end": 1 }
        ],
        "span": [
          {
            "expected": { "engine": "tsc", "code": 1111, "file": "/a.ts", "start": 0, "end": 1 },
            "actual": { "engine": "rust", "code": "TS1111", "file": "/a.ts", "start": 0, "end": 1 }
          }
        ]
      }
    },
    {
      "name": "b",
      "status": "mismatch",
      "diff": {
        "unexpected": [
          { "engine": "rust", "code": "TS2222", "file": "/b.ts", "start": 0, "end": 1 }
        ]
      }
    },
    { "name": "c", "status": "baseline_missing", "notes": ["missing baseline"] }
  ]
}
"#;

const EXPECTED_DIFFTSC_TRIAGE: &str = r#"{
  "kind": "difftsc",
  "top": 10,
  "total": 3,
  "mismatches": 3,
  "mismatches_without_code": 1,
  "top_outcomes": [
    {
      "key": "baseline_missing",
      "count": 1
    },
    {
      "key": "rust_extra_diagnostics",
      "count": 1
    },
    {
      "key": "rust_missing_diagnostics",
      "count": 1
    },
    {
      "key": "span_mismatch",
      "count": 1
    }
  ],
  "top_codes": [
    {
      "key": "TS1111",
      "count": 1
    },
    {
      "key": "TS2222",
      "count": 1
    }
  ],
  "top_prefixes": [
    {
      "key": "a",
      "count": 1
    },
    {
      "key": "b",
      "count": 1
    },
    {
      "key": "c",
      "count": 1
    }
  ],
  "regressions": [
    {
      "id": "a",
      "outcome": "mismatch",
      "code": "TS1111",
      "prefix": "a"
    },
    {
      "id": "b",
      "outcome": "mismatch",
      "code": "TS2222",
      "prefix": "b"
    },
    {
      "id": "c",
      "outcome": "baseline_missing",
      "prefix": "c"
    }
  ],
  "suggestions": [
    {
      "id": "difftsc/c",
      "status": "skip",
      "reason": "triage: baseline_missing"
    },
    {
      "id": "difftsc/a",
      "status": "xfail",
      "reason": "triage: mismatch TS1111"
    },
    {
      "id": "difftsc/b",
      "status": "xfail",
      "reason": "triage: mismatch TS2222"
    }
  ]
}
"#;

const DIFFTSC_REPORT_FOR_BASELINE: &str = r#"
{
  "suite": "difftsc",
  "results": [
    {
      "name": "a",
      "status": "mismatch",
      "diff": {
        "unexpected": [
          { "engine": "rust", "code": "TS1111", "file": "/a.ts", "start": 0, "end": 1 }
        ]
      }
    },
    { "name": "b", "status": "matched" },
    { "name": "c", "status": "baseline_missing", "notes": ["missing baseline"] }
  ]
}
"#;

const DIFFTSC_BASELINE_REPORT: &str = r#"
{
  "suite": "difftsc",
  "results": [
    { "name": "a", "status": "matched" },
    {
      "name": "b",
      "status": "mismatch",
      "diff": {
        "unexpected": [
          { "engine": "rust", "code": "TS2222", "file": "/b.ts", "start": 0, "end": 1 }
        ]
      }
    },
    { "name": "c", "status": "baseline_missing", "notes": ["missing baseline"] }
  ]
}
"#;

const EXPECTED_DIFFTSC_TRIAGE_WITH_BASELINE: &str = r#"{
  "kind": "difftsc",
  "top": 10,
  "total": 3,
  "mismatches": 2,
  "mismatches_without_code": 1,
  "top_outcomes": [
    {
      "key": "baseline_missing",
      "count": 1
    },
    {
      "key": "rust_extra_diagnostics",
      "count": 1
    }
  ],
  "top_codes": [
    {
      "key": "TS1111",
      "count": 1
    }
  ],
  "top_prefixes": [
    {
      "key": "a",
      "count": 1
    },
    {
      "key": "c",
      "count": 1
    }
  ],
  "regressions": [
    {
      "id": "a",
      "outcome": "mismatch",
      "code": "TS1111",
      "prefix": "a"
    },
    {
      "id": "c",
      "outcome": "baseline_missing",
      "prefix": "c"
    }
  ],
  "suggestions": [
    {
      "id": "difftsc/c",
      "status": "skip",
      "reason": "triage: baseline_missing"
    },
    {
      "id": "difftsc/a",
      "status": "xfail",
      "reason": "triage: mismatch TS1111"
    }
  ],
  "baseline": {
    "baseline_total": 3,
    "baseline_mismatches": 2,
    "new_cases": 0,
    "missing_cases": 0,
    "regressed": 1,
    "fixed": 1,
    "regressions": [
      {
        "id": "a",
        "outcome": "mismatch",
        "code": "TS1111",
        "prefix": "a"
      }
    ],
    "fixes": [
      "b"
    ]
  }
}
"#;

#[test]
fn triage_conformance_json_output_is_stable() {
  let dir = tempdir().expect("tempdir");
  let path = dir.path().join("report.json");
  fs::write(&path, CONFORMANCE_REPORT).expect("write report");

  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("triage")
    .arg("--input")
    .arg(&path)
    .arg("--top")
    .arg("5")
    .arg("--json");

  let assert = cmd.assert().success();
  let output = assert.get_output();
  assert!(
    !output.stderr.is_empty(),
    "expected human summary on stderr"
  );
  let stdout = String::from_utf8_lossy(&output.stdout);
  assert_eq!(stdout, EXPECTED_CONFORMANCE_TRIAGE);
}

#[test]
fn triage_conformance_baseline_diff_json_output_is_stable() {
  let dir = tempdir().expect("tempdir");
  let path = dir.path().join("report.json");
  let baseline = dir.path().join("baseline.json");
  fs::write(&path, CONFORMANCE_REPORT).expect("write report");
  fs::write(&baseline, CONFORMANCE_BASELINE_REPORT).expect("write baseline");

  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("triage")
    .arg("--input")
    .arg(&path)
    .arg("--baseline")
    .arg(&baseline)
    .arg("--top")
    .arg("5")
    .arg("--json");

  let assert = cmd.assert().success();
  let output = assert.get_output();
  assert!(
    !output.stderr.is_empty(),
    "expected human summary on stderr"
  );
  let stdout = String::from_utf8_lossy(&output.stdout);
  assert_eq!(stdout, EXPECTED_CONFORMANCE_TRIAGE_WITH_BASELINE);
}

#[test]
fn triage_difftsc_json_output_is_stable() {
  let dir = tempdir().expect("tempdir");
  let path = dir.path().join("report.json");
  fs::write(&path, DIFFTSC_REPORT).expect("write report");

  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("triage")
    .arg("--input")
    .arg(&path)
    .arg("--top")
    .arg("10")
    .arg("--json");

  let assert = cmd.assert().success();
  let output = assert.get_output();
  assert!(
    !output.stderr.is_empty(),
    "expected human summary on stderr"
  );
  let stdout = String::from_utf8_lossy(&output.stdout);
  assert_eq!(stdout, EXPECTED_DIFFTSC_TRIAGE);
}

#[test]
fn triage_difftsc_baseline_diff_json_output_is_stable() {
  let dir = tempdir().expect("tempdir");
  let path = dir.path().join("report.json");
  let baseline = dir.path().join("baseline.json");
  fs::write(&path, DIFFTSC_REPORT_FOR_BASELINE).expect("write report");
  fs::write(&baseline, DIFFTSC_BASELINE_REPORT).expect("write baseline");

  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("triage")
    .arg("--input")
    .arg(&path)
    .arg("--baseline")
    .arg(&baseline)
    .arg("--top")
    .arg("10")
    .arg("--json");

  let assert = cmd.assert().success();
  let output = assert.get_output();
  assert!(
    !output.stderr.is_empty(),
    "expected human summary on stderr"
  );
  let stdout = String::from_utf8_lossy(&output.stdout);
  assert_eq!(stdout, EXPECTED_DIFFTSC_TRIAGE_WITH_BASELINE);
}
