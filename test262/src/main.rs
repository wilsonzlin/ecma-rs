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

  let results = read_dir(cli.data_dir.join("pass"))
    .unwrap()
    .par_bridge()
    .map(|t| {
      let file_path = t.unwrap();
      let file_name = file_path.file_name().to_str().unwrap().to_string();
      let src = fs::read(file_path.path()).unwrap();
      let src_str = std::str::from_utf8(&src).unwrap();
      let error = parse_js::parse(src_str)
        .err()
        .map(|err| format!("{:?}", err));
      (file_name, error)
    })
    .collect::<Vec<_>>();

  let mut passed_count = 0;
  let mut failed_count = 0;
  let total_count = results.len();
  for (file_name, error) in results {
    match error {
      Some(err) => {
        eprintln!("Test {} failed with error {}", file_name, err);
        failed_count += 1;
      }
      None => {
        passed_count += 1;
      }
    };
  }
  println!(
    "{} ({}%) passed, {} ({}%) failed",
    passed_count,
    passed_count as f64 / total_count as f64 * 100.0,
    failed_count,
    failed_count as f64 / total_count as f64 * 100.0
  );
}
