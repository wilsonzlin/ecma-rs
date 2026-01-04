#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::il::inst::{Arg, InstTyp};
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn import_meta_is_supported() {
  let src = "console.log(import.meta);";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    js.contains("import.meta"),
    "expected `import.meta` in output: {js}"
  );
}

#[test]
fn new_target_is_supported() {
  let src = "(() => { console.log(new.target); })();";
  let program = compile_source(src, TopLevelMode::Module, false);

  let found = program.functions.iter().any(|func| {
    func.body.bblocks.all().any(|(_, block)| {
      block.iter().any(|inst| {
        inst.t == InstTyp::Call
          && inst
            .as_call()
            .3
            .iter()
            .any(|arg| matches!(arg, Arg::Builtin(path) if path == "new.target"))
      })
    })
  });

  assert!(
    found,
    "expected `new.target` to be lowered in function body"
  );
}
