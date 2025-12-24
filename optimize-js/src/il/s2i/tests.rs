use super::super::inst::InstTyp;
use crate::Program;
use crate::ProgramFunction;
use parse_js::parse;
use symbol_js::compute_symbols;
use symbol_js::TopLevelMode;

fn compile(source: &str) -> Program {
  let mut top_level = parse(source).expect("parse input");
  compute_symbols(&mut top_level, TopLevelMode::Module);
  Program::compile(top_level, false).expect("compile input")
}

fn inst_types(func: &ProgramFunction) -> Vec<InstTyp> {
  func
    .body
    .bblocks
    .all()
    .flat_map(|(_, b)| b.iter().map(|inst| inst.t.clone()))
    .collect()
}

#[test]
fn destructuring_assignment_to_captured_var_is_foreign() {
  let source = r#"
      let a = 0;
      const make = (obj) => {
        ({ a } = obj);
        a += 1;
        const inner = () => { a += 1; };
        inner;
      };
    "#;

  let program = compile(source);

  assert!(program.functions.len() >= 2);
  let make_insts = inst_types(&program.functions[0]);
  assert!(
    make_insts
      .iter()
      .any(|t| matches!(t, InstTyp::ForeignStore)),
    "expected destructuring assignment to use foreign store, got {:?}",
    make_insts
  );

  let other_insts: Vec<(usize, Vec<InstTyp>)> = program.functions[1..]
    .iter()
    .enumerate()
    .map(|(i, f)| (i + 1, inst_types(f)))
    .collect();
  let has_foreign_load = other_insts
    .iter()
    .flat_map(|(_, ts)| ts.iter())
    .any(|t| matches!(t, InstTyp::ForeignLoad));
  assert!(
    has_foreign_load,
    "captured read should be a foreign load: {:?}",
    other_insts
  );
}

#[test]
fn destructuring_decl_shadowing_binds_local_symbol() {
  let program = compile(
    r#"
      const a = 0;
      const make = (obj) => {
        let { a } = obj;
        a += 1;
        const inner = () => { a += 1; };
        inner;
      };
    "#,
  );

  assert!(program.functions.len() >= 2);
  let make_insts = inst_types(&program.functions[0]);
  let make_unknowns: Vec<_> = program.functions[0]
    .body
    .bblocks
    .all()
    .flat_map(|(_, b)| b.iter())
    .filter(|inst| matches!(inst.t, InstTyp::UnknownLoad | InstTyp::UnknownStore))
    .map(|inst| inst.unknown.as_str())
    .collect();
  assert!(
    !make_unknowns.iter().any(|n| *n == "a"),
    "expected destructured `a` to resolve to a local symbol, got unknowns: {make_unknowns:?}"
  );
  assert!(
    make_insts.iter().any(|t| matches!(t, InstTyp::ForeignStore)),
    "captured local should use foreign stores: {:?}",
    make_insts
  );

  let has_foreign_load = program.functions[1..]
    .iter()
    .flat_map(inst_types)
    .any(|t| matches!(t, InstTyp::ForeignLoad));
  assert!(has_foreign_load, "captured read should be a foreign load");
}
