//! Shared utilities for writing deterministic conformance test runners.
//!
//! This crate is intentionally VM-agnostic and focuses on the "harness"
//! infrastructure shared by many test suites:
//! - expectation manifests (`pass|skip|xfail|flaky`) with deterministic
//!   precedence rules
//! - deterministic sharding
//! - cooperative timeouts via a cancellation token
//! - pretty JSON report writing helpers

mod expectations;
mod fail_on;
mod report;
mod shard;
mod timeout;

pub use expectations::{AppliedExpectation, Expectation, ExpectationKind, Expectations};
pub use fail_on::FailOn;
pub use report::{
  to_json_pretty_stable, write_json_report, write_json_report_to_stdout, write_json_report_to_writer,
  ReportRef,
};
pub use shard::{apply_shard, Shard};
pub use timeout::{CancellationToken, TimeoutGuard, TimeoutManager};
