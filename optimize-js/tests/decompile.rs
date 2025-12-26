#[path = "common/mod.rs"]
mod common;
use common::compile_source;
use optimize_js::decompile::{temp_decls_for_top_level, DecompileOptions, TempDeclStyle};
use optimize_js::TopLevelMode;

#[test]
fn global_top_level_temps_use_let_with_void_default() {
  let program = compile_source("var a = 1; var b = a + 2;", TopLevelMode::Global, false);
  let decls = temp_decls_for_top_level(&program, &DecompileOptions::default()).expect("temp decls");

  assert!(
    decls.starts_with("let "),
    "global scripts should avoid introducing global vars: {decls}"
  );
  assert!(
    decls.contains("void 0"),
    "global scripts should initialize temps to avoid TDZ: {decls}"
  );
}

#[test]
fn module_top_level_temps_default_to_var() {
  let program = compile_source(
    "const a = 1; const b = a + 2; console.log(b);",
    TopLevelMode::Module,
    false,
  );
  let decls = temp_decls_for_top_level(&program, &DecompileOptions::default()).expect("temp decls");

  assert!(
    decls.starts_with("var "),
    "modules can safely use var-scoped temporaries: {decls}"
  );
  assert!(
    !decls.contains("void 0"),
    "module defaults should not force void initialization: {decls}"
  );
}

#[test]
fn temp_decl_style_can_be_overridden() {
  let program = compile_source("var a = 1; a += 1;", TopLevelMode::Global, false);
  let opts = DecompileOptions {
    temp_decl_style: TempDeclStyle::Var,
    ..DecompileOptions::default()
  };
  let decls = temp_decls_for_top_level(&program, &opts).expect("temp decls");

  assert!(decls.starts_with("var "));
  assert!(!decls.contains("void 0"));
}
