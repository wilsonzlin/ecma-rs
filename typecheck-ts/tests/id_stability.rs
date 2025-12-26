use std::collections::BTreeSet;

use typecheck_ts::{BodyId, ExprId, FileKey, MemoryHost, PatId, Program, Span};

fn collect_exprs(program: &Program, body: BodyId) -> BTreeSet<(ExprId, Span)> {
  program
    .exprs_in_body(body)
    .into_iter()
    .filter_map(|id| program.expr_span(body, id).map(|span| (id, span)))
    .collect()
}

fn collect_pats(program: &Program, body: BodyId) -> BTreeSet<(PatId, Span)> {
  program
    .pats_in_body(body)
    .into_iter()
    .filter_map(|id| program.pat_span(body, id).map(|span| (id, span)))
    .collect()
}

#[test]
fn hir_ids_are_stable_across_runs() {
  let file = FileKey::new("file.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "function foo(x: number) { return x + 1; }\nconst value = foo(2);\n",
  );

  let program_a = Program::new(host.clone(), vec![file.clone()]);
  let program_b = Program::new(host, vec![file.clone()]);

  program_a.check();
  program_b.check();

  let file_id_a = program_a.file_id(&file).expect("file id");
  let file_id_b = program_b.file_id(&file).expect("file id");
  assert_eq!(file_id_a, file_id_b, "file ids should be stable");

  let defs_a: BTreeSet<_> = program_a
    .definitions_in_file(file_id_a)
    .into_iter()
    .collect();
  let defs_b: BTreeSet<_> = program_b
    .definitions_in_file(file_id_b)
    .into_iter()
    .collect();
  assert_eq!(defs_a, defs_b);

  for def in defs_a.iter() {
    assert_eq!(program_a.def_span(*def), program_b.def_span(*def));
  }

  let bodies_a: BTreeSet<BodyId> = program_a.bodies_in_file(file_id_a).into_iter().collect();
  let bodies_b: BTreeSet<BodyId> = program_b.bodies_in_file(file_id_b).into_iter().collect();
  assert_eq!(bodies_a, bodies_b);

  for body in bodies_a {
    assert_eq!(
      collect_exprs(&program_a, body),
      collect_exprs(&program_b, body),
      "exprs differed for body {:?}",
      body
    );
    assert_eq!(
      collect_pats(&program_a, body),
      collect_pats(&program_b, body),
      "pats differed for body {:?}",
      body
    );
  }
}

#[test]
fn body_ids_are_unique_per_file() {
  let first = FileKey::new("first.ts");
  let second = FileKey::new("second.ts");
  let mut host = MemoryHost::default();
  host.insert(first.clone(), "function first() { return 1; }\n");
  host.insert(
    second.clone(),
    "function second(x: number) { return x; }\nconst value = second(2);\n",
  );

  let program_a = Program::new(host.clone(), vec![first.clone(), second.clone()]);
  let program_b = Program::new(host, vec![first.clone(), second.clone()]);

  program_a.check();
  program_b.check();

  let first_id_a = program_a.file_id(&first).expect("first file id");
  let first_id_b = program_b.file_id(&first).expect("first file id");
  let second_id_a = program_a.file_id(&second).expect("second file id");
  let second_id_b = program_b.file_id(&second).expect("second file id");

  assert_eq!(first_id_a, first_id_b);
  assert_eq!(second_id_a, second_id_b);

  let defs_a_first: BTreeSet<_> = program_a
    .definitions_in_file(first_id_a)
    .into_iter()
    .collect();
  let defs_b_first: BTreeSet<_> = program_b
    .definitions_in_file(first_id_b)
    .into_iter()
    .collect();
  assert_eq!(defs_a_first, defs_b_first);

  let defs_a_second: BTreeSet<_> = program_a
    .definitions_in_file(second_id_a)
    .into_iter()
    .collect();
  let defs_b_second: BTreeSet<_> = program_b
    .definitions_in_file(second_id_b)
    .into_iter()
    .collect();
  assert_eq!(defs_a_second, defs_b_second);

  let bodies_first_a: BTreeSet<_> = program_a.bodies_in_file(first_id_a).into_iter().collect();
  let bodies_second_a: BTreeSet<_> = program_a.bodies_in_file(second_id_a).into_iter().collect();
  assert!(
    bodies_first_a.is_disjoint(&bodies_second_a),
    "body ids should not collide across files"
  );

  let bodies_first_b: BTreeSet<_> = program_b.bodies_in_file(first_id_b).into_iter().collect();
  let bodies_second_b: BTreeSet<_> = program_b.bodies_in_file(second_id_b).into_iter().collect();

  assert_eq!(bodies_first_a, bodies_first_b);
  assert_eq!(bodies_second_a, bodies_second_b);

  for body in bodies_first_a.iter().chain(bodies_second_a.iter()) {
    assert_eq!(
      collect_exprs(&program_a, *body),
      collect_exprs(&program_b, *body),
      "exprs differed for body {:?}",
      body
    );
    assert_eq!(
      collect_pats(&program_a, *body),
      collect_pats(&program_b, *body),
      "pats differed for body {:?}",
      body
    );
  }
}

#[test]
fn ids_remain_stable_on_recheck() {
  let file = FileKey::new("file.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "function foo(x: number) { return x + 1; }\nconst value = foo(2);\n",
  );

  let program = Program::new(host, vec![file.clone()]);
  program.check();

  let file_id = program.file_id(&file).expect("file id");

  let defs_first: BTreeSet<_> = program.definitions_in_file(file_id).into_iter().collect();
  let bodies_first: BTreeSet<_> = program.bodies_in_file(file_id).into_iter().collect();

  let exprs_first: BTreeSet<_> = bodies_first
    .iter()
    .flat_map(|body| collect_exprs(&program, *body))
    .collect();
  let pats_first: BTreeSet<_> = bodies_first
    .iter()
    .flat_map(|body| collect_pats(&program, *body))
    .collect();

  // Trigger a second round of checking to ensure no IDs are reallocated.
  program.check();

  let defs_second: BTreeSet<_> = program.definitions_in_file(file_id).into_iter().collect();
  let bodies_second: BTreeSet<_> = program.bodies_in_file(file_id).into_iter().collect();

  let exprs_second: BTreeSet<_> = bodies_second
    .iter()
    .flat_map(|body| collect_exprs(&program, *body))
    .collect();
  let pats_second: BTreeSet<_> = bodies_second
    .iter()
    .flat_map(|body| collect_pats(&program, *body))
    .collect();

  assert_eq!(defs_first, defs_second);
  assert_eq!(bodies_first, bodies_second);
  assert_eq!(exprs_first, exprs_second);
  assert_eq!(pats_first, pats_second);
}

#[test]
fn expr_at_remains_stable_across_runs() {
  let file = FileKey::new("expr.ts");
  let source = "const value = (1 + 2) * 3;";
  let mut host = MemoryHost::default();
  host.insert(file.clone(), source);

  let program_a = Program::new(host.clone(), vec![file.clone()]);
  let program_b = Program::new(host, vec![file.clone()]);

  program_a.check();
  program_b.check();

  let file_id_a = program_a.file_id(&file).expect("file id");
  let file_id_b = program_b.file_id(&file).expect("file id");

  let offset = source.find("1 + 2").expect("offset") as u32 + 2;

  let expr_a = program_a.expr_at(file_id_a, offset).expect("expr a");
  let expr_b = program_b.expr_at(file_id_b, offset).expect("expr b");

  assert_eq!(expr_a, expr_b);
  assert_eq!(
    program_a.expr_span(expr_a.0, expr_a.1),
    program_b.expr_span(expr_b.0, expr_b.1)
  );
}

#[test]
fn repeated_check_preserves_id_sets_across_files() {
  let first = FileKey::new("first.ts");
  let second = FileKey::new("second.ts");
  let mut host = MemoryHost::default();
  host.insert(
    first.clone(),
    "export function alpha(value: number) { return value * 2; }",
  );
  host.insert(
    second.clone(),
    "import { alpha } from \"./first\";\nexport const beta = alpha(3);\n",
  );
  host.link(second.clone(), "./first", first.clone());

  let program = Program::new(host, vec![second.clone()]);
  program.check();

  let first_id = program.file_id(&first).expect("first file id");
  let second_id = program.file_id(&second).expect("second file id");

  let collect_ids = |program: &Program| {
    let mut defs = BTreeSet::new();
    let mut bodies = BTreeSet::new();
    let mut exprs = BTreeSet::new();
    for file in [first_id, second_id] {
      defs.extend(program.definitions_in_file(file));
      for body in program.bodies_in_file(file) {
        bodies.insert(body);
        exprs.extend(program.exprs_in_body(body));
      }
    }
    (defs, bodies, exprs)
  };

  let first_run = collect_ids(&program);

  // Re-run checking and ensure no IDs are reallocated.
  program.check();
  let second_run = collect_ids(&program);

  assert_eq!(first_run, second_run);
}
