use super::super::inst::InstTyp;
use crate::compile_source;
use crate::Program;
use crate::ProgramFunction;
use crate::TopLevelMode;

fn compile(source: &str) -> Program {
  compile_source(source, TopLevelMode::Module, false).expect("compile input")
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

  let lowered = hir_js::lower_from_source(
    r#"
      const a = 0;
      const make = (obj) => {
        let { a } = obj;
        a += 1;
        const inner = () => { a += 1; };
        inner;
      };
    "#,
  )
  .unwrap();
  dbg!(lowered.defs.len());
  dbg!(lowered
    .defs
    .iter()
    .map(|d| {
      (
        format!("{:?}", d.path.kind),
        lowered
          .names
          .resolve(d.name)
          .unwrap_or_default()
          .to_string(),
      )
    })
    .collect::<Vec<_>>());
  dbg!(lowered
    .defs
    .iter()
    .map(|d| (d.id, d.path.kind, d.body))
    .collect::<Vec<_>>());

  for def in lowered.defs.iter() {
    if let Some(body_id) = def.body {
      let body = lowered.body(body_id).unwrap();
      dbg!(def.path.kind, lowered.names.resolve(def.name), body.kind);
      dbg!(body.root_stmts.len());
      for stmt_id in body.root_stmts.iter() {
        let stmt = &body.stmts[stmt_id.0 as usize];
        dbg!(stmt.kind.clone());
      }
    }
  }

  dbg!(lowered
    .bodies
    .iter()
    .map(|b| (b.owner, b.kind, b.root_stmts.len(), b.stmts.len()))
    .collect::<Vec<_>>());

  dbg!(program.functions.len());
  for (idx, func) in program.functions.iter().enumerate() {
    dbg!(idx, inst_types(func));
  }

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
    make_insts
      .iter()
      .any(|t| matches!(t, InstTyp::ForeignStore)),
    "captured local should use foreign stores: {:?}",
    make_insts
  );

  let has_foreign_load = program.functions[1..]
    .iter()
    .flat_map(inst_types)
    .any(|t| matches!(t, InstTyp::ForeignLoad));
  assert!(has_foreign_load, "captured read should be a foreign load");
}

#[test]
fn direct_eval_is_unsupported() {
  let source = r#"const f = () => { let x = 1; eval("x"); };"#;
  let err = compile_source(source, TopLevelMode::Module, false)
    .expect_err("direct eval should be rejected");

  assert!(
    err
      .iter()
      .any(|diag| diag.code == "OPT0002" && diag.message.contains("direct eval")),
    "expected OPT0002 diagnostic mentioning direct eval, got {err:?}"
  );
}

#[test]
fn shadowed_eval_is_allowed() {
  let source = r#"const f = (eval) => { let x = 1; eval("x"); };"#;
  compile_source(source, TopLevelMode::Global, false).expect("shadowed eval should compile");
}

#[test]
fn with_statement_is_rejected() {
  let source = r#"with (obj) { answer = 42; }"#;
  let err = compile_source(source, TopLevelMode::Global, false)
    .expect_err("with statements are unsupported");
  assert!(
    err
      .iter()
      .any(|diag| diag.code == "OPT0002" && diag.message.contains("with statements")),
    "expected OPT0002 about with statement, got {err:?}"
  );
}

#[test]
fn spread_call_indices_include_callee_and_this() {
  let program = compile(
    r#"
      let f;
      let obj;
      let xs;
      let ys;
      f(...xs);
      obj.m(...ys);
    "#,
  );

  let spread_calls: Vec<_> = program
    .top_level
    .body
    .bblocks
    .all()
    .flat_map(|(_, b)| b.iter())
    .filter(|inst| matches!(inst.t, InstTyp::Call) && !inst.spreads.is_empty())
    .map(|inst| (inst.spreads.clone(), inst.args.len()))
    .collect();

  assert_eq!(
    spread_calls.len(),
    2,
    "expected spread calls for both statements, got {spread_calls:?}"
  );
  for (spreads, args_len) in spread_calls {
    assert_eq!(
      spreads,
      vec![2],
      "spread indices should account for callee and this prefix"
    );
    assert!(
      spreads.iter().all(|&i| i < args_len),
      "spread indices must be in bounds of args (len={args_len})"
    );
  }
}
