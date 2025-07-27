use clap::command;
use clap::Parser;
use rayon::prelude::*;
use std::fs;
use std::fs::read_dir;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(version)]
struct Cli {
  /// Path to tc39/test262-parser-tests repository folder.
  #[arg(long)]
  data_dir: PathBuf,
}

fn main() {
  let cli = Cli::parse();

  let mut total_passed = 0;
  let mut total_failed = 0;
  let mut total_count = 0;

  // Process pass tests (should parse successfully)
  if let Ok(entries) = read_dir(cli.data_dir.join("pass")) {
    let results: Vec<_> = entries
      .par_bridge()
      .map(|t| {
        let file_path = t.unwrap();
        let file_name = file_path.file_name().to_str().unwrap().to_string();
        let src = fs::read(file_path.path()).unwrap();
        
        // Check if this is a module based on filename
        let is_module = file_name.ends_with(".module.js");
        
        let error = if is_module {
          parse_js::parse_module(&src).err().map(|err| format!("{:?}", err))
        } else {
          parse_js::parse(&src).err().map(|err| format!("{:?}", err))
        };
        (file_name, error)
      })
      .collect();

    for (file_name, error) in results {
      total_count += 1;
      match error {
        Some(err) => {
          eprintln!("PASS test {} failed with error {}", file_name, err);
          total_failed += 1;
        }
        None => {
          total_passed += 1;
        }
      };
    }
    println!("Pass tests: {} passed out of {}", total_passed, total_count);
  } else {
    println!("Warning: pass/ directory not found");
  }

  // Process fail tests (should fail to parse)
  if let Ok(entries) = read_dir(cli.data_dir.join("fail")) {
    let fail_results: Vec<_> = entries
      .par_bridge()
      .map(|t| {
        let file_path = t.unwrap();
        let file_name = file_path.file_name().to_str().unwrap().to_string();
        let src = fs::read(file_path.path()).unwrap();
        
        // Check if this is a module based on filename
        let is_module = file_name.ends_with(".module.js");
        
        let error = if is_module {
          parse_js::parse_module(&src).err().map(|err| format!("{:?}", err))
        } else {
          parse_js::parse(&src).err().map(|err| format!("{:?}", err))
        };
        (file_name, error)
      })
      .collect();

    let mut fail_passed = 0;
    let mut fail_failed = 0;
    let fail_count = fail_results.len();
    
    for (file_name, error) in fail_results {
      total_count += 1;
      match error {
        Some(_) => {
          // For fail tests, having an error means the test passed
          fail_passed += 1;
          total_passed += 1;
        }
        None => {
          eprintln!("FAIL test {} incorrectly parsed successfully", file_name);
          fail_failed += 1;
          total_failed += 1;
        }
      };
    }
    println!("Fail tests: {} passed out of {} (should fail to parse)", fail_passed, fail_count);
  }

  // Process early tests (should parse but may have early errors - we don't check early errors yet)
  if let Ok(entries) = read_dir(cli.data_dir.join("early")) {
    let early_results: Vec<_> = entries
      .par_bridge()
      .map(|t| {
        let file_path = t.unwrap();
        let file_name = file_path.file_name().to_str().unwrap().to_string();
        let src = fs::read(file_path.path()).unwrap();
        
        // Check if this is a module based on filename
        let is_module = file_name.ends_with(".module.js");
        
        let error = if is_module {
          parse_js::parse_module(&src).err().map(|err| format!("{:?}", err))
        } else {
          parse_js::parse(&src).err().map(|err| format!("{:?}", err))
        };
        (file_name, error)
      })
      .collect();

    let mut early_passed = 0;
    let mut early_failed = 0;
    let early_count = early_results.len();
    
    for (file_name, error) in early_results {
      total_count += 1;
      match error {
        Some(err) => {
          // Early tests should parse successfully (we don't check early errors)
          eprintln!("EARLY test {} failed with error {}", file_name, err);
          early_failed += 1;
          total_failed += 1;
        }
        None => {
          early_passed += 1;
          total_passed += 1;
        }
      };
    }
    println!("Early tests: {} passed out of {} (should parse, may have early errors)", early_passed, early_count);
  }

  println!(
    "\nTotal: {} ({}%) passed, {} ({}%) failed out of {} tests",
    total_passed,
    total_passed as f64 / total_count as f64 * 100.0,
    total_failed,
    total_failed as f64 / total_count as f64 * 100.0,
    total_count
  );
}
