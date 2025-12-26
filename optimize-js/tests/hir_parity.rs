#![cfg(feature = "legacy-ast-lowering")]

use emit_js::EmitOptions;
use optimize_js::decompile::DecompileOptions;
use optimize_js::{compile_source, compile_source_ast, program_to_js, TopLevelMode};

#[test]
fn hir_matches_legacy_js_output() {
  let samples = [
    "let a = 0; a += 1; const b = a + 2; b;",
    "let {a: b = 1} = foo; b += 2; b;",
    "let f; let xs; f?.(...xs);",
  ];

  for source in samples {
    let hir = compile_source(source, TopLevelMode::Module, false).expect("hir compile");
    let legacy = compile_source_ast(source, TopLevelMode::Module, false).expect("legacy compile");
    let opts = DecompileOptions::default();
    let hir_js = program_to_js(&hir, &opts, EmitOptions::minified()).expect("hir js");
    let legacy_js = program_to_js(&legacy, &opts, EmitOptions::minified()).expect("legacy js");
    assert_eq!(hir_js, legacy_js, "source: {source}");
  }
}
