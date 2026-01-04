use optimize_js::{compile_source as compile_hir, TopLevelMode};
#[cfg(feature = "typed")]
use optimize_js::compile_source_typed as compile_hir_typed;

/// Compile using the HIR pipeline used by the optimizer.
pub fn compile_source(source: &str, mode: TopLevelMode, debug: bool) -> optimize_js::Program {
  compile_hir(source, mode, debug).expect("compile source")
}

#[cfg(feature = "typed")]
#[allow(dead_code)]
pub fn compile_source_typed(source: &str, mode: TopLevelMode, debug: bool) -> optimize_js::Program {
  compile_hir_typed(source, mode, debug).expect("compile typed source")
}
