#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::il::inst::{BinOp, InstTyp};
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn switch_statements_are_supported() {
  let src = r#"
    const x = foo();
    switch (x) {
      case 1:
        bar();
        break;
      default:
        baz();
    }
  "#;
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  parse_js::parse(js).expect("emitted JS should parse");
}

#[test]
fn switch_cases_use_strict_equality() {
  let src = r#"
    const x = foo();
    switch (x) {
      case 1:
        sideEffect();
        break;
    }
  "#;
  let program = compile_source(src, TopLevelMode::Module, false);

  let mut saw_strict_eq = false;
  let mut saw_cond_goto = false;
  for (_, insts) in program.top_level.body.bblocks.all() {
    for inst in insts {
      match inst.t {
        InstTyp::Bin => {
          let (_, _, op, _) = inst.as_bin();
          if op == BinOp::StrictEq {
            saw_strict_eq = true;
          }
        }
        InstTyp::CondGoto => saw_cond_goto = true,
        _ => {}
      }
    }
  }

  assert!(saw_strict_eq, "expected StrictEq compare for switch case");
  assert!(saw_cond_goto, "expected CondGoto branch for switch case");
}
