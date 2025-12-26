use emit_js::EmitOptions;
use optimize_js::il::inst::Inst;
use optimize_js::{compile_source as compile_hir, program_to_js, DecompileOptions, TopLevelMode};

#[cfg(feature = "legacy-ast-lowering")]
use optimize_js::compile_source_ast;

/// Compile using the HIR pipeline and, when the legacy lowering feature is
/// enabled, assert that the legacy AST pipeline produces identical output.
pub fn compile_source(source: &str, mode: TopLevelMode, debug: bool) -> optimize_js::Program {
  let program = compile_hir(source, mode, debug).expect("compile source");
  assert_legacy_parity(source, mode, debug, &program);
  program
}

pub fn assert_legacy_parity(
  source: &str,
  mode: TopLevelMode,
  debug: bool,
  hir: &optimize_js::Program,
) {
  #[cfg(feature = "legacy-ast-lowering")]
  {
    let legacy = compile_source_ast(source, mode, debug).expect("legacy compile");
    let opts = DecompileOptions::default();
    let emit_opts = EmitOptions::minified();
    let hir_js = program_to_js(hir, &opts, emit_opts.clone());
    let legacy_js = program_to_js(&legacy, &opts, emit_opts);
    match (hir_js, legacy_js) {
      (Ok(hir_js), Ok(legacy_js)) => assert_eq!(
        hir_js, legacy_js,
        "hir and legacy outputs differ for source: {source}"
      ),
      _ => {
        let hir_insts = collect_all_insts(hir);
        let legacy_insts = collect_all_insts(&legacy);
        assert_eq!(
          hir_insts, legacy_insts,
          "hir and legacy IL differ for source: {source}"
        );
      }
    }
  }
}

fn collect_insts(cfg: &optimize_js::cfg::cfg::Cfg) -> Vec<Inst> {
  let mut blocks: Vec<_> = cfg.bblocks.all().collect();
  blocks.sort_by_key(|(label, _)| *label);
  blocks
    .into_iter()
    .flat_map(|(_, block)| block.iter().cloned())
    .collect()
}

fn collect_all_insts(program: &optimize_js::Program) -> Vec<Inst> {
  let mut insts = collect_insts(&program.top_level.body);
  for func in &program.functions {
    insts.extend(collect_insts(&func.body));
  }
  insts
}
