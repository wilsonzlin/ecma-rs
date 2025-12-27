use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use hir_js::{lower_file_with_diagnostics, FileKind as HirFileKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::{BodyId, DefId, ExprId, FileId, FileKey, MemoryHost, PatId, Program, Span};

fn collect_ids(
  program: &Program,
  file: &FileKey,
) -> (Vec<DefId>, Vec<BodyId>, BTreeMap<BodyId, Vec<ExprId>>) {
  let file_id = program.file_id(file).expect("file id");

  let mut defs = program.definitions_in_file(file_id);
  defs.sort_by_key(|d| d.0);

  let mut bodies = program.bodies_in_file(file_id);
  bodies.sort_by_key(|b| b.0);

  let mut exprs = BTreeMap::new();
  for body in bodies.iter() {
    let mut ids = program.exprs_in_body(*body);
    ids.sort_by_key(|e| e.0);
    exprs.insert(*body, ids);
  }

  (defs, bodies, exprs)
}

fn collect_id_sets(
  program: &Program,
  file: FileId,
) -> (
  BTreeSet<DefId>,
  BTreeSet<BodyId>,
  BTreeSet<(BodyId, ExprId)>,
) {
  let mut bodies: BTreeSet<_> = program.bodies_in_file(file).into_iter().collect();
  if let Some(root) = program.file_body(file) {
    bodies.insert(root);
  }
  let defs = program.definitions_in_file(file).into_iter().collect();
  let mut exprs = BTreeSet::new();
  for body in bodies.iter() {
    for expr in program.exprs_in_body(*body) {
      exprs.insert((*body, expr));
    }
  }
  (defs, bodies, exprs)
}

#[test]
fn program_ids_match_hir_lowering() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let source: Arc<str> = Arc::from(
    r#"
      const a = 1;
      function add(x: number, y: number) { return x + y; }
      const doubled = (value: number) => add(value, value);
      export default doubled(a);
    "#,
  );
  host.insert(file.clone(), source.clone());

  let program = Program::new(host, vec![file.clone()]);
  program.check();

  let file_id = program.file_id(&file).expect("file id");
  let ast = parse_with_options(
    &source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let (lowered, _) = lower_file_with_diagnostics(file_id, HirFileKind::Ts, &ast);

  let program_defs: BTreeSet<_> = program.definitions_in_file(file_id).into_iter().collect();
  let lowered_defs: BTreeSet<_> = lowered.defs.iter().map(|def| def.id).collect();
  assert_eq!(program_defs, lowered_defs);
  for def in lowered.defs.iter() {
    assert_eq!(
      program.def_span(def.id),
      Some(Span::new(file_id, def.span)),
      "program def span should match lowered span"
    );
    assert_eq!(
      program.body_of_def(def.id),
      def.body,
      "program body_of_def should use lowered body"
    );
  }

  let program_bodies: BTreeSet<_> = program
    .bodies_in_file(file_id)
    .into_iter()
    .chain(program.file_body(file_id))
    .collect();
  let mut lowered_bodies: BTreeSet<_> = lowered.hir.bodies.iter().copied().collect();
  lowered_bodies.insert(lowered.root_body());
  assert_eq!(program_bodies, lowered_bodies);

  for body in lowered_bodies {
    let hir_body = lowered.body(body).expect("lowered body");
    let mut exprs = program.exprs_in_body(body);
    exprs.sort_by_key(|id| id.0);
    let expected_exprs: Vec<_> = (0..hir_body.exprs.len() as u32).map(ExprId).collect();
    assert_eq!(exprs, expected_exprs, "expr ids for body {:?}", body);

    let mut pats = program.pats_in_body(body);
    pats.sort_by_key(|id| id.0);
    let expected_pats: Vec<_> = (0..hir_body.pats.len() as u32).map(PatId).collect();
    assert_eq!(pats, expected_pats, "pat ids for body {:?}", body);

    for (idx, expr) in hir_body.exprs.iter().enumerate() {
      let span = program
        .expr_span(body, ExprId(idx as u32))
        .expect("expr span from program");
      assert_eq!(span, Span::new(file_id, expr.span));
    }

    for (idx, pat) in hir_body.pats.iter().enumerate() {
      let span = program
        .pat_span(body, PatId(idx as u32))
        .expect("pat span from program");
      assert_eq!(span, Span::new(file_id, pat.span));
    }
  }

  let first_ids = collect_ids(&program, &file);
  program.check();
  let second_ids = collect_ids(&program, &file);
  assert_eq!(
    first_ids, second_ids,
    "ID sets should remain unchanged across repeated checks"
  );
}

#[test]
fn repeated_checks_match_lowering_sets() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("stable.ts");
  let source: Arc<str> = Arc::from(
    r#"
      export function add(a: number, b: number) { return a + b; }
      export const doubled = add(2, 2);
    "#,
  );
  host.insert(file.clone(), source.clone());

  let program = Program::new(host, vec![file.clone()]);
  program.check();

  let file_id = program.file_id(&file).expect("file id");
  let ast = parse_with_options(
    &source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let (lowered, _) = lower_file_with_diagnostics(file_id, HirFileKind::Ts, &ast);

  let mut expected_bodies: BTreeSet<_> = lowered.hir.bodies.iter().copied().collect();
  expected_bodies.insert(lowered.root_body());
  let expected_defs: BTreeSet<_> = lowered.defs.iter().map(|def| def.id).collect();
  let mut expected_exprs: BTreeSet<(BodyId, ExprId)> = BTreeSet::new();
  for body in expected_bodies.iter() {
    if let Some(body_data) = lowered.body(*body) {
      for (idx, _) in body_data.exprs.iter().enumerate() {
        expected_exprs.insert((*body, ExprId(idx as u32)));
      }
    }
  }

  let first_sets = collect_id_sets(&program, file_id);
  assert_eq!(first_sets.0, expected_defs);
  assert_eq!(first_sets.1, expected_bodies);
  assert_eq!(first_sets.2, expected_exprs);

  program.check();
  let second_sets = collect_id_sets(&program, file_id);

  assert_eq!(first_sets, second_sets);
  assert_eq!(second_sets.0, expected_defs);
  assert_eq!(second_sets.1, expected_bodies);
  assert_eq!(second_sets.2, expected_exprs);
}

#[test]
fn hir_ids_remain_stable_across_checks() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let source = Arc::from(
    r#"
      const a = 1;
      function add(x: number, y: number) {
        return x + y;
      }
      const doubled = (value: number) => add(value, value);
      add(a, 3);
    "#,
  );
  host.insert(file.clone(), source);

  let program_a = Program::new(host.clone(), vec![file.clone()]);
  let _ = program_a.check();
  let ids_a = collect_ids(&program_a, &file);

  // Re-running analysis on a fresh program should produce the same stable IDs.
  let program_b = Program::new(host, vec![file.clone()]);
  let _ = program_b.check();
  let ids_b = collect_ids(&program_b, &file);

  assert_eq!(ids_a, ids_b);
}

#[test]
fn repeated_check_reuses_hir_ids() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("repeat.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
      export function value(input: number) { return input * 2; }
      export const doubled = value(3);
    "#,
    ),
  );

  let program = Program::new(host, vec![file.clone()]);
  program.check();
  let first = collect_ids(&program, &file);

  program.check();
  let second = collect_ids(&program, &file);

  assert_eq!(first, second);
}

#[test]
fn repeated_check_with_imports_preserves_ids() {
  let mut host = MemoryHost::default();
  let entry = FileKey::new("entry.ts");
  let util = FileKey::new("util.ts");
  host.insert(
    entry.clone(),
    Arc::from(
      r#"
      import { value, square } from "./util";
      export const result = square(value);
    "#,
    ),
  );
  host.insert(
    util.clone(),
    Arc::from(
      r#"
      export const value = 4;
      export function square(input: number) {
        return input * input;
      }
    "#,
    ),
  );
  host.link(entry.clone(), "./util", util.clone());

  let program = Program::new(host, vec![entry.clone()]);
  program.check();

  let collect = |program: &Program| {
    let entry_id = program.file_id(&entry).expect("entry id");
    let util_id = program.file_id(&util).expect("util id");
    let mut defs = BTreeSet::new();
    let mut bodies = BTreeSet::new();
    let mut exprs = BTreeSet::new();

    for file in [entry_id, util_id] {
      defs.extend(program.definitions_in_file(file));
      for body in program.bodies_in_file(file) {
        bodies.insert(body);
        exprs.extend(
          program
            .exprs_in_body(body)
            .into_iter()
            .map(|expr| (body, expr)),
        );
      }
    }

    (defs, bodies, exprs)
  };

  let first = collect(&program);
  program.check();
  let second = collect(&program);

  assert_eq!(first, second);
}

#[test]
fn id_sets_match_across_identical_programs() {
  let first = FileKey::new("alpha.ts");
  let second = FileKey::new("beta.ts");
  let mut host = MemoryHost::default();
  host.insert(
    first.clone(),
    "export function alpha(value: number) { return value + 1; }",
  );
  host.insert(
    second.clone(),
    "import { alpha } from \"./alpha\"; export const beta = alpha(2);",
  );
  host.link(second.clone(), "./alpha", first.clone());

  let program_a = Program::new(host.clone(), vec![second.clone()]);
  let program_b = Program::new(host, vec![second.clone()]);

  program_a.check();
  program_b.check();

  let collect_sets = |program: &Program| {
    let first_id = program.file_id(&first).expect("first file id");
    let second_id = program.file_id(&second).expect("second file id");
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

  assert_eq!(collect_sets(&program_a), collect_sets(&program_b));
}

#[test]
fn def_names_and_exports_cover_hir_only_defs() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("class.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
        export class Greeter { greet() { return "hi"; } }
        export default class Defaulted {}
      "#,
    ),
  );

  let program = Program::new(host, vec![file.clone()]);
  program.check();

  let file_id = program.file_id(&file).expect("file id");
  let defs = program.definitions_in_file(file_id);
  assert!(
    !defs.is_empty(),
    "expected class definitions to be discovered from HIR"
  );

  for def in defs.iter() {
    assert!(
      program.def_name(*def).is_some(),
      "def {:?} should have a name from HIR",
      def
    );
  }

  let exports = program.exports_of(file_id);
  assert!(
    exports.contains_key("Greeter"),
    "export map should include named class"
  );
  assert!(
    exports.contains_key("default"),
    "export map should include default class"
  );
}
