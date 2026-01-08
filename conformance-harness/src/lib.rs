//! Shared utilities for writing deterministic conformance test runners.
//!
//! This crate is intentionally small and dependency-light so harness binaries
//! across the workspace can share behavior without copy/pasting.

mod expectations;
mod fail_on;
mod shard;
mod timeout;

pub use expectations::{AppliedExpectation, Expectation, ExpectationKind, Expectations};
pub use fail_on::FailOn;
pub use shard::Shard;
pub use timeout::{TimeoutGuard, TimeoutManager};
