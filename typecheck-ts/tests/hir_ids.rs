use std::collections::BTreeMap;
use std::sync::Arc;

use typecheck_ts::{BodyId, DefId, ExprId, FileKey, MemoryHost, Program};

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
