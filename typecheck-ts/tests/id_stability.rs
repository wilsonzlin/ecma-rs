use std::collections::{BTreeMap, BTreeSet};

use typecheck_ts::{BodyId, DefId, ExprId, FileId, FileKey, MemoryHost, PatId, Program, Span};

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

fn collect_id_sets(
  program: &Program,
  file: FileId,
) -> (BTreeSet<DefId>, BTreeSet<BodyId>, BTreeSet<ExprId>) {
  let defs = program.definitions_in_file(file).into_iter().collect();
  let mut bodies: BTreeSet<_> = program.bodies_in_file(file).into_iter().collect();
  if let Some(root) = program.file_body(file) {
    bodies.insert(root);
  }
  let mut exprs = BTreeSet::new();
  for body in bodies.iter() {
    exprs.extend(program.exprs_in_body(*body));
  }
  (defs, bodies, exprs)
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
fn checking_same_source_twice_returns_same_id_sets() {
  let file = FileKey::new("repeat-check.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "export function repeat(value: number) { return value + 1; }\nexport const doubled = repeat(2);\n",
  );

  let program = Program::new(host, vec![file.clone()]);
  program.check();

  let file_id = program.file_id(&file).expect("file id");
  let first = collect_id_sets(&program, file_id);

  program.check();
  let second = collect_id_sets(&program, file_id);

  assert_eq!(
    first, second,
    "DefId, BodyId, and ExprId sets should remain stable across repeated checks"
  );
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

#[test]
fn ids_are_stable_for_default_export_expressions() {
  let file = FileKey::new("default.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
const seed = 1;
const wrap = (input: number) => {
  const inner = (offset: number) => input + offset;
  return inner(seed);
};
export default wrap(seed + 2);
"#,
  );

  let program_a = Program::new(host.clone(), vec![file.clone()]);
  let program_b = Program::new(host, vec![file.clone()]);

  program_a.check();
  program_b.check();

  let file_id_a = program_a.file_id(&file).expect("file id");
  let file_id_b = program_b.file_id(&file).expect("file id");

  assert_eq!(file_id_a, file_id_b);

  let snapshot = |program: &Program, file_id: FileId| {
    let mut defs = program.definitions_in_file(file_id);
    defs.sort_by_key(|d| d.0);

    let mut bodies: Vec<_> = program
      .bodies_in_file(file_id)
      .into_iter()
      .chain(program.file_body(file_id))
      .collect();
    bodies.sort_by_key(|b| b.0);
    bodies.dedup();

    let def_bodies: BTreeMap<_, _> = defs
      .iter()
      .map(|def| (*def, program.body_of_def(*def)))
      .collect();
    let exprs: BTreeMap<_, _> = bodies
      .iter()
      .map(|body| {
        let mut ids = program.exprs_in_body(*body);
        ids.sort_by_key(|id| id.0);
        (*body, ids)
      })
      .collect();

    (defs, bodies, def_bodies, exprs)
  };

  let snap_a = snapshot(&program_a, file_id_a);
  let snap_b = snapshot(&program_b, file_id_b);

  assert_eq!(snap_a, snap_b);
}

#[test]
fn ids_remain_stable_when_diagnostics_are_emitted() {
  let file = FileKey::new("excess.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), "let x: { foo: number } = { foo: 1, bar: 2 };");

  let program_a = Program::new(host.clone(), vec![file.clone()]);
  let program_b = Program::new(host, vec![file.clone()]);

  let diags_a = program_a.check();
  let diags_b = program_b.check();

  assert_eq!(diags_a.len(), 1, "expected one excess property diagnostic");
  assert_eq!(diags_a.len(), diags_b.len(), "diagnostics should be stable");

  let file_id_a = program_a.file_id(&file).expect("file id a");
  let file_id_b = program_b.file_id(&file).expect("file id b");

  assert_eq!(
    collect_id_sets(&program_a, file_id_a),
    collect_id_sets(&program_b, file_id_b),
    "id sets should remain stable even when diagnostics are produced",
  );
}

#[test]
fn repeated_checks_keep_id_sets_stable() {
  let file = FileKey::new("repeat.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "export function compute(value: number) { const inner = (input: number) => value + input; return inner(value); }\nexport const result = compute(4);\n",
  );

  let program = Program::new(host, vec![file.clone()]);
  program.check();

  let file_id = program.file_id(&file).expect("file id");
  let first = collect_id_sets(&program, file_id);

  program.check();
  let second = collect_id_sets(&program, file_id);

  assert_eq!(first, second, "id sets should remain stable across checks");
}

#[test]
fn top_level_bodies_remain_stable_across_programs() {
  let file = FileKey::new("root.ts");
  let source = "const seed = 1;\nexport default seed + 2;";
  let mut host = MemoryHost::default();
  host.insert(file.clone(), source);

  let program_a = Program::new(host.clone(), vec![file.clone()]);
  let program_b = Program::new(host, vec![file.clone()]);

  program_a.check();
  program_b.check();

  let file_id_a = program_a.file_id(&file).expect("file id a");
  let file_id_b = program_b.file_id(&file).expect("file id b");

  let defs_a: BTreeSet<_> = program_a
    .definitions_in_file(file_id_a)
    .into_iter()
    .collect();
  let defs_b: BTreeSet<_> = program_b
    .definitions_in_file(file_id_b)
    .into_iter()
    .collect();
  assert_eq!(
    defs_a, defs_b,
    "definition sets should match across programs"
  );

  let root_body_a = program_a.file_body(file_id_a).expect("root body a");
  let root_body_b = program_b.file_body(file_id_b).expect("root body b");
  assert_eq!(root_body_a, root_body_b, "root body ids should match");

  let exprs_a: BTreeSet<_> = program_a.exprs_in_body(root_body_a).into_iter().collect();
  let exprs_b: BTreeSet<_> = program_b.exprs_in_body(root_body_b).into_iter().collect();
  assert_eq!(exprs_a, exprs_b, "expr id sets should match for root body");
}

#[test]
fn checking_same_source_twice_produces_identical_id_sets() {
  let file = FileKey::new("repeat.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "export function compute(value: number) { return value * 2; }\nexport const doubled = compute(3);\n",
  );

  let program_first = Program::new(host.clone(), vec![file.clone()]);
  let program_second = Program::new(host, vec![file.clone()]);

  program_first.check();
  program_second.check();

  let file_id_first = program_first.file_id(&file).expect("first file id");
  let file_id_second = program_second.file_id(&file).expect("second file id");

  let ids_first = collect_id_sets(&program_first, file_id_first);
  let ids_second = collect_id_sets(&program_second, file_id_second);

  assert_eq!(ids_first, ids_second, "id sets must match across checks");
}
