use optimize_js::{compile_source as compile_hir, TopLevelMode};

/// Compile using the HIR pipeline used by the optimizer.
pub fn compile_source(source: &str, mode: TopLevelMode, debug: bool) -> optimize_js::Program {
  compile_hir(source, mode, debug).expect("compile source")
}
