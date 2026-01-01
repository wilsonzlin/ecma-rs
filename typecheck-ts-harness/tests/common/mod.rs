use std::path::PathBuf;
use typecheck_ts_harness::tsc::{node_available, typescript_available, TscRunner};

pub fn node_path_or_skip(context: &str) -> Option<PathBuf> {
  let node_path = PathBuf::from("node");

  if !node_available(&node_path) {
    eprintln!("skipping {context}: node not available");
    return None;
  }

  if !typescript_available(&node_path) {
    eprintln!(
      "skipping {context}: typescript not available (run `cd typecheck-ts-harness && npm ci`)"
    );
    return None;
  }

  Some(node_path)
}

#[allow(dead_code)]
pub fn runner_or_skip(context: &str) -> Option<TscRunner> {
  let node_path = node_path_or_skip(context)?;

  match TscRunner::new(node_path) {
    Ok(runner) => Some(runner),
    Err(err) => {
      eprintln!("skipping {context}: {err}");
      None
    }
  }
}
