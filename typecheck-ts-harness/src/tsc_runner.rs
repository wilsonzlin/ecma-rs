use anyhow::{anyhow, Context, Result};
use crate::tsc::TSC_BASELINE_SCHEMA_VERSION;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug, Clone)]
pub struct TscRunner {
  node_path: PathBuf,
  wrapper: PathBuf,
}

impl TscRunner {
  pub fn new(node_path: PathBuf) -> Self {
    let wrapper = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("scripts")
      .join("tsc_wrapper.js");
    Self { node_path, wrapper }
  }

  pub fn available(&self) -> bool {
    match Command::new(&self.node_path).arg("--version").output() {
      Ok(output) => output.status.success(),
      Err(_) => false,
    }
  }

  pub fn run(&self, cwd: &Path, files: &[PathBuf]) -> Result<TscDiagnostics> {
    if !self.wrapper.exists() {
      return Err(anyhow!("missing tsc wrapper at {}", self.wrapper.display()));
    }

    let mut cmd = Command::new(&self.node_path);
    cmd.current_dir(cwd);
    cmd.arg(&self.wrapper);
    for file in files {
      cmd.arg(file);
    }

    let output = cmd
      .output()
      .with_context(|| format!("spawn node at {}", self.node_path.display()))?;

    if !output.status.success() {
      return Err(anyhow!(
        "tsc wrapper exited with status {}: stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
      ));
    }

    let mut parsed: TscDiagnostics =
      serde_json::from_slice(&output.stdout).context("parse tsc JSON output")?;
    if parsed.schema_version.is_none() {
      parsed.schema_version = Some(TSC_BASELINE_SCHEMA_VERSION);
    }

    Ok(parsed)
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TscDiagnostics {
  #[serde(default)]
  pub schema_version: Option<u32>,
  #[serde(default)]
  pub metadata: TscMetadata,
  pub diagnostics: Vec<TscDiagnostic>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TscMetadata {
  #[serde(default)]
  pub typescript_version: Option<String>,
  #[serde(default)]
  pub options: Map<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TscDiagnostic {
  pub code: u32,
  pub file: Option<String>,
  pub start: u32,
  pub end: u32,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub category: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub message: Option<String>,
}
