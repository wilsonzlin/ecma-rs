use crate::discover::Filter;
use crate::runner::Summary;
use crate::{ConformanceOptions, HarnessError, TestOutcome, TestResult};
use serde::Serialize;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use typecheck_ts::QueryStats;

#[derive(Debug, Serialize)]
pub struct ProfileReport {
  pub metadata: RunMetadata,
  pub tests: Vec<TestEntry>,
  pub summary: ProfileSummary,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub query_stats: Option<QueryStats>,
}

#[derive(Debug, Serialize, Clone)]
pub struct RunMetadata {
  pub mode: &'static str,
  pub timestamp_ms: u128,
  pub git_sha: Option<String>,
  pub args: Vec<String>,
  pub options: ProfileOptions,
}

#[derive(Debug, Serialize, Clone)]
pub struct ProfileOptions {
  pub root: String,
  pub filter: String,
  pub shard: Option<String>,
  pub json: bool,
  pub update_snapshots: bool,
  pub timeout_secs: u64,
  pub trace: bool,
  pub profile: bool,
  pub profile_out: String,
  pub jobs: usize,
}

#[derive(Debug, Serialize)]
pub struct ProfileSummary {
  pub total: usize,
  pub passed: usize,
  pub failed: usize,
  pub timed_out: usize,
  pub wall_time_ms: u128,
  pub percentiles_ms: Percentiles,
}

#[derive(Debug, Serialize, Default)]
pub struct Percentiles {
  pub p50: f64,
  pub p90: f64,
  pub p99: f64,
}

#[derive(Debug, Serialize)]
pub struct TestEntry {
  pub id: String,
  pub status: TestOutcome,
  pub durations: TestDurations,
}

#[derive(Debug, Serialize, Clone, Copy)]
pub struct TestDurations {
  pub rust_ms: Option<u128>,
  pub tsc_ms: Option<u128>,
  pub diff_ms: Option<u128>,
  pub total_ms: u128,
}

pub struct ProfileBuilder {
  metadata: RunMetadata,
  tests: Vec<TestEntry>,
  query_stats: QueryStats,
}

impl ProfileBuilder {
  pub fn new(opts: &ConformanceOptions) -> Self {
    Self {
      metadata: RunMetadata {
        mode: "conformance",
        timestamp_ms: timestamp_ms(),
        git_sha: git_sha(),
        args: std::env::args().collect(),
        options: ProfileOptions::from_options(opts),
      },
      tests: Vec::new(),
      query_stats: QueryStats::default(),
    }
  }

  pub fn record_test(&mut self, result: &TestResult) {
    if let Some(stats) = &result.query_stats {
      self.query_stats.merge(stats);
    }
    self.tests.push(TestEntry {
      id: result.id.clone(),
      status: result.outcome,
      durations: TestDurations {
        rust_ms: Some(result.duration_ms),
        tsc_ms: None,
        diff_ms: None,
        total_ms: result.duration_ms,
      },
    });
  }

  pub fn write(
    mut self,
    summary: &Summary,
    wall_time: Duration,
    path: &Path,
  ) -> Result<(), HarnessError> {
    let report = self.finish(summary, wall_time);
    let json =
      serde_json::to_string_pretty(&report).map_err(|err| HarnessError::Output(err.to_string()))?;

    if let Some(parent) = path.parent() {
      if !parent.as_os_str().is_empty() {
        fs::create_dir_all(parent)
          .map_err(|err| HarnessError::Output(format!("create profile directory: {err}")))?;
      }
    }

    fs::write(path, format!("{json}\n"))
      .map_err(|err| HarnessError::Output(format!("write profile: {err}")))?;

    Ok(())
  }

  fn finish(&mut self, summary: &Summary, wall_time: Duration) -> ProfileReport {
    let mut samples: Vec<_> = self.tests.iter().map(|t| t.durations.total_ms).collect();
    samples.sort_unstable();

    let percentiles_ms = Percentiles::from_samples(&samples);

    ProfileReport {
      metadata: RunMetadata {
        mode: self.metadata.mode,
        timestamp_ms: self.metadata.timestamp_ms,
        git_sha: self.metadata.git_sha.clone(),
        args: self.metadata.args.clone(),
        options: self.metadata.options.clone(),
      },
      tests: std::mem::take(&mut self.tests),
      summary: ProfileSummary {
        total: summary.total,
        passed: summary.outcomes.match_,
        failed: summary
          .total
          .saturating_sub(summary.outcomes.match_ + summary.outcomes.timeout),
        timed_out: summary.outcomes.timeout,
        wall_time_ms: wall_time.as_millis(),
        percentiles_ms,
      },
      query_stats: (!self.query_stats.is_empty()).then(|| self.query_stats.clone()),
    }
  }
}

impl ProfileOptions {
  fn from_options(opts: &ConformanceOptions) -> Self {
    let shard = opts
      .shard
      .as_ref()
      .map(|shard| format!("{}/{}", shard.index, shard.total));
    let filter = opts
      .filter_pattern
      .clone()
      .unwrap_or_else(|| describe_filter(&opts.filter));

    ProfileOptions {
      root: opts.root.display().to_string(),
      filter,
      shard,
      json: opts.json,
      update_snapshots: opts.update_snapshots,
      timeout_secs: opts.timeout.as_secs(),
      trace: opts.trace,
      profile: opts.profile,
      profile_out: opts.profile_out.display().to_string(),
      jobs: opts.jobs,
    }
  }
}

impl Percentiles {
  fn from_samples(samples: &[u128]) -> Self {
    if samples.is_empty() {
      return Percentiles::default();
    }

    Percentiles {
      p50: percentile(samples, 0.5),
      p90: percentile(samples, 0.9),
      p99: percentile(samples, 0.99),
    }
  }
}

fn percentile(samples: &[u128], fraction: f64) -> f64 {
  if samples.is_empty() {
    return 0.0;
  }

  let max_index = samples.len() - 1;
  let rank = fraction * max_index as f64;
  let lower = rank.floor() as usize;
  let upper = rank.ceil() as usize;

  if lower == upper {
    return samples[lower] as f64;
  }

  let lower_v = samples[lower] as f64;
  let upper_v = samples[upper] as f64;
  lower_v + (upper_v - lower_v) * (rank - lower as f64)
}

fn timestamp_ms() -> u128 {
  SystemTime::now()
    .duration_since(UNIX_EPOCH)
    .map(|d| d.as_millis())
    .unwrap_or_default()
}

fn git_sha() -> Option<String> {
  let output = Command::new("git")
    .args(["rev-parse", "HEAD"])
    .output()
    .ok()?;

  if !output.status.success() {
    return None;
  }

  let sha = String::from_utf8_lossy(&output.stdout).trim().to_string();
  if sha.is_empty() {
    None
  } else {
    Some(sha)
  }
}

fn describe_filter(filter: &Filter) -> String {
  match filter {
    Filter::All => "all".to_string(),
    Filter::Glob(_) => "glob".to_string(),
    Filter::Regex(_) => "regex".to_string(),
  }
}
