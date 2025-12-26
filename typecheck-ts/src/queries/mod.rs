//! Query implementations for the checker.
//!
//! These are early, coarse-grained queries that will evolve alongside the
//! incremental engine. Parsing is centralized here so callers share the same
//! deterministic options regardless of where a parse is triggered.

pub mod parse;
