// TypeScript Conformance Test Runner
// Runs all TypeScript conformance tests and reports pass/fail statistics

use parse_js;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct TestResult {
    path: PathBuf,
    passed: bool,
    error: Option<String>,
}

fn discover_tests(dir: &Path) -> Vec<PathBuf> {
    let mut tests = Vec::new();

    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                tests.extend(discover_tests(&path));
            } else if let Some(ext) = path.extension() {
                if ext == "ts" || ext == "tsx" {
                    tests.push(path);
                }
            }
        }
    }

    tests
}

fn run_test(path: &Path) -> TestResult {
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return TestResult {
                path: path.to_path_buf(),
                passed: false,
                error: Some(format!("Failed to read file: {}", e)),
            };
        }
    };

    // Catch panics to prevent test runner from crashing
    let result = std::panic::catch_unwind(|| {
        parse_js::parse(&source)
    });

    match result {
        Ok(Ok(_)) => TestResult {
            path: path.to_path_buf(),
            passed: true,
            error: None,
        },
        Ok(Err(e)) => TestResult {
            path: path.to_path_buf(),
            passed: false,
            error: Some(format!("{:?}", e)),
        },
        Err(panic_err) => TestResult {
            path: path.to_path_buf(),
            passed: false,
            error: Some(format!("PANIC: {:?}", panic_err)),
        },
    }
}

fn main() {
    let test_dir = Path::new("tests/TypeScript/tests/cases/conformance");

    println!("🔍 Discovering TypeScript conformance tests...");
    let tests = discover_tests(test_dir);
    println!("📊 Found {} test files\n", tests.len());

    println!("🚀 Running tests...");
    let passed = Arc::new(AtomicUsize::new(0));
    let failed = Arc::new(AtomicUsize::new(0));

    let mut results = Vec::new();
    let mut failures_by_category: HashMap<String, Vec<TestResult>> = HashMap::new();

    for (idx, test_path) in tests.iter().enumerate() {
        if idx % 100 == 0 {
            println!("Progress: {}/{}", idx, tests.len());
        }
        if idx % 10 == 0 {
            eprintln!("[TEST {}] {}", idx, test_path.display());
        }

        let result = run_test(test_path);

        if result.passed {
            passed.fetch_add(1, Ordering::Relaxed);
        } else {
            failed.fetch_add(1, Ordering::Relaxed);

            // Categorize failure by directory
            if let Some(parent) = test_path.parent() {
                let category = parent
                    .strip_prefix(test_dir)
                    .unwrap_or(parent)
                    .to_string_lossy()
                    .to_string();
                failures_by_category
                    .entry(category)
                    .or_insert_with(Vec::new)
                    .push(result.clone());
            }
        }

        results.push(result);
    }

    let passed_count = passed.load(Ordering::Relaxed);
    let failed_count = failed.load(Ordering::Relaxed);
    let total = tests.len();
    let pass_rate = (passed_count as f64 / total as f64) * 100.0;

    let separator = "=".repeat(80);
    println!("\n{}", separator);
    println!("📈 TEST RESULTS SUMMARY");
    println!("{}", separator);
    println!("Total tests:  {}", total);
    println!("✅ Passed:     {} ({:.2}%)", passed_count, pass_rate);
    println!("❌ Failed:     {} ({:.2}%)", failed_count, 100.0 - pass_rate);
    println!("{}", separator);

    if !failures_by_category.is_empty() {
        println!("\n📋 FAILURES BY CATEGORY:");
        println!("{}", separator);

        let mut categories: Vec<_> = failures_by_category.iter().collect();
        categories.sort_by_key(|(_, failures)| std::cmp::Reverse(failures.len()));

        for (category, failures) in categories.iter().take(20) {
            println!("{}: {} failures", category, failures.len());
        }

        println!("\n🔍 SAMPLE FAILURES (first 50):");
        println!("{}", separator);

        let failed_results: Vec<_> = results.iter().filter(|r| !r.passed).take(50).collect();
        for (idx, result) in failed_results.iter().enumerate() {
            println!("\n{}. {}", idx + 1, result.path.display());
            if let Some(err) = &result.error {
                let err_str = err.lines().take(3).collect::<Vec<_>>().join("\n");
                println!("   Error: {}", err_str);
            }
        }
    }

    // Write detailed failure report
    if failed_count > 0 {
        let report_path = "typescript_conformance_failures.txt";
        let mut report = String::new();
        report.push_str(&format!("TypeScript Conformance Test Failures Report\n\n"));
        report.push_str(&format!("Total: {}, Passed: {}, Failed: {}\n", total, passed_count, failed_count));
        report.push_str(&format!("Pass Rate: {:.2}%\n\n", pass_rate));
        report.push_str("=".repeat(80).as_str());
        report.push_str("\n\nFAILURES:\n\n");

        for result in results.iter().filter(|r| !r.passed) {
            report.push_str(&format!("\n{}\n", "=".repeat(80)));
            report.push_str(&format!("File: {}\n", result.path.display()));
            if let Some(err) = &result.error {
                report.push_str(&format!("Error: {}\n", err));
            }
        }

        fs::write(report_path, report).ok();
        println!("\n📝 Detailed failure report written to: {}", report_path);
    }

    println!("\n");

    if failed_count > 0 {
        std::process::exit(1);
    }
}
