// TypeScript Conformance Test Runner
// Runs all TypeScript conformance tests in parallel with timeouts

use parse_js;
use rayon::prelude::*;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use std::sync::Mutex;

#[derive(Debug, Clone)]
struct TestResult {
    path: PathBuf,
    passed: bool,
    error: Option<String>,
    duration: Duration,
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

fn run_test_with_timeout(path: &Path, timeout_secs: u64) -> TestResult {
    let start = Instant::now();
    let path = path.to_path_buf();

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            return TestResult {
                path,
                passed: false,
                error: Some(format!("Failed to read file: {}", e)),
                duration: start.elapsed(),
            };
        }
    };

    // Run with timeout using a channel
    let (tx, rx) = std::sync::mpsc::channel();
    let source_clone = source.clone();

    std::thread::spawn(move || {
        let result = std::panic::catch_unwind(|| {
            parse_js::parse(&source_clone)
        });
        let _ = tx.send(result);
    });

    // Wait for result with timeout
    match rx.recv_timeout(Duration::from_secs(timeout_secs)) {
        Ok(result) => {
            match result {
                Ok(Ok(_)) => TestResult {
                    path,
                    passed: true,
                    error: None,
                    duration: start.elapsed(),
                },
                Ok(Err(e)) => TestResult {
                    path,
                    passed: false,
                    error: Some(format!("{:?}", e)),
                    duration: start.elapsed(),
                },
                Err(panic_err) => TestResult {
                    path,
                    passed: false,
                    error: Some(format!("PANIC: {:?}", panic_err)),
                    duration: start.elapsed(),
                },
            }
        }
        Err(_) => TestResult {
            path,
            passed: false,
            error: Some(format!("TIMEOUT after {} seconds", timeout_secs)),
            duration: Duration::from_secs(timeout_secs),
        },
    }
}

fn main() {
    let test_dir = Path::new("tests/TypeScript/tests/cases/conformance");

    println!("🔍 Discovering TypeScript conformance tests...");
    let mut tests = discover_tests(test_dir);
    tests.sort(); // Sort for reproducible ordering
    println!("📊 Found {} test files\n", tests.len());

    println!("🚀 Running tests in parallel...");
    let passed = Arc::new(AtomicUsize::new(0));
    let failed = Arc::new(AtomicUsize::new(0));
    let processed = Arc::new(AtomicUsize::new(0));
    let total = tests.len();

    // Progress reporter thread
    let processed_clone = Arc::clone(&processed);
    let progress_handle = std::thread::spawn(move || {
        loop {
            std::thread::sleep(Duration::from_secs(5));
            let current = processed_clone.load(Ordering::Relaxed);
            if current >= total {
                break;
            }
            eprintln!("Progress: {}/{} ({:.1}%)", current, total, (current as f64 / total as f64) * 100.0);
        }
    });

    // Run tests in parallel
    let results: Vec<TestResult> = tests.par_iter()
        .map(|test_path| {
            let result = run_test_with_timeout(test_path, 10); // 10 second timeout per test

            let current = processed.fetch_add(1, Ordering::Relaxed) + 1;
            if current % 100 == 0 {
                eprintln!("[{}/{}] {}", current, total, test_path.display());
            }

            if result.passed {
                passed.fetch_add(1, Ordering::Relaxed);
            } else {
                failed.fetch_add(1, Ordering::Relaxed);
                if result.error.as_ref().map(|e| e.contains("TIMEOUT")).unwrap_or(false) {
                    eprintln!("⏱️  TIMEOUT: {}", test_path.display());
                }
            }

            result
        })
        .collect();

    progress_handle.join().ok();

    let passed_count = passed.load(Ordering::Relaxed);
    let failed_count = failed.load(Ordering::Relaxed);
    let pass_rate = (passed_count as f64 / total as f64) * 100.0;

    // Categorize failures
    let mut failures_by_category: HashMap<String, Vec<TestResult>> = HashMap::new();
    for result in &results {
        if !result.passed {
            if let Some(parent) = result.path.parent() {
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
    }

    let separator = "=".repeat(80);
    println!("\n{}", separator);
    println!("📈 TEST RESULTS SUMMARY");
    println!("{}", separator);
    println!("Total tests:  {}", total);
    println!("✅ Passed:     {} ({:.2}%)", passed_count, pass_rate);
    println!("❌ Failed:     {} ({:.2}%)", failed_count, 100.0 - pass_rate);
    println!("{}", separator);

    // Show timeout count
    let timeout_count = results.iter().filter(|r| r.error.as_ref().map(|e| e.contains("TIMEOUT")).unwrap_or(false)).count();
    if timeout_count > 0 {
        println!("⏱️  Timeouts:   {}", timeout_count);
    }

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
            println!("\n{}. {} ({:?})", idx + 1, result.path.display(), result.duration);
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
            report.push_str(&format!("Duration: {:?}\n", result.duration));
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
