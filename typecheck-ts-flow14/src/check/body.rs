use crate::flow::cfg::build_cfg;
use crate::flow::narrow::solve_flow;
use crate::flow::narrow::FlowResult;
use crate::hir::Body;

pub type CheckResult = FlowResult;

/// Run control-flow-based narrowing for the provided body. This is a
/// lightweight entry point that currently focuses on producing per-expression
/// types useful for tests and diagnostics.
pub fn check_body(body: &Body) -> CheckResult {
  let cfg = build_cfg(body);
  solve_flow(body, &cfg)
}
