use std::error::Error;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use tracing::info;
use typecheck_ts_trace23::InputFile;
use typecheck_ts_trace23::Profile;
use typecheck_ts_trace23::Profiler;
use typecheck_ts_trace23::Typechecker;

#[derive(Debug, Clone)]
pub struct HarnessConfig {
  pub trace: bool,
  pub profile: Option<PathBuf>,
  pub filter: Option<String>,
}

pub fn run_conformance(config: HarnessConfig) -> Result<Option<Profile>, Box<dyn Error>> {
  let fixtures = load_fixtures(config.filter.as_deref())?;
  if fixtures.is_empty() {
    return Err("no fixtures matched filter".into());
  }

  let mut checker = Typechecker::new();
  let mut profiler = Profiler::new();
  checker.check_files(&fixtures, &mut profiler);
  let profile = checker.into_profile(profiler);

  if let Some(path) = config.profile {
    write_profile(&path, &profile)?;
    info!(target: "typecheck_ts::harness", path = %path.display(), "wrote profile JSON");
  }

  Ok(Some(profile))
}

fn fixtures_dir() -> PathBuf {
  PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures")
}

fn write_profile(path: &Path, profile: &Profile) -> Result<(), Box<dyn Error>> {
  if let Some(parent) = path.parent() {
    if !parent.as_os_str().is_empty() {
      fs::create_dir_all(parent)?;
    }
  }
  let file = fs::File::create(path)?;
  serde_json::to_writer_pretty(file, profile)?;
  Ok(())
}

pub fn load_fixtures(filter: Option<&str>) -> Result<Vec<InputFile>, Box<dyn Error>> {
  let mut inputs = Vec::new();
  for entry in fs::read_dir(fixtures_dir())? {
    let entry = entry?;
    if !entry.file_type()?.is_file() {
      continue;
    }

    let path = entry.path();
    if path.extension().and_then(|s| s.to_str()) != Some("ts") {
      continue;
    }

    let name = path
      .file_name()
      .and_then(|s| s.to_str())
      .unwrap_or_default();
    if let Some(filter) = filter {
      if !name.contains(filter) {
        continue;
      }
    }

    let text = fs::read_to_string(&path)?;
    inputs.push(InputFile {
      path: path.display().to_string(),
      text,
    });
  }

  Ok(inputs)
}
