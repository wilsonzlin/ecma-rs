use diagnostics::TextRange;
use std::sync::Arc;

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn empty_object_type_accepts_primitives_but_rejects_nullish() {
  let mut host = MemoryHost::default();
  // Use a deterministic file name (`file0.ts` -> `FileId(0)`) so we can assert
  // diagnostics against a stable file id.
  let file = FileKey::new("file0.ts");
  let source = r#"
let ok: {} = 1;
let bad_object: object = 1;
let bad_null: {} = null;
"#;
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();

  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert_eq!(mismatches.len(), 2, "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id for a.ts");
  // TypeScript anchors `TS2322`-style assignability diagnostics on the binding
  // name within the variable declaration.
  let bad_object_start = u32::try_from(source.find("bad_object").expect("bad object binding"))
    .expect("offset fits in u32");
  let bad_object_end = bad_object_start + "bad_object".len() as u32;
  let bad_null_start =
    u32::try_from(source.find("bad_null").expect("bad null binding")).expect("offset fits in u32");
  let bad_null_end = bad_null_start + "bad_null".len() as u32;

  assert!(
    mismatches.iter().any(|diag| diag.primary.file == file_id
      && diag.primary.range == TextRange::new(bad_object_start, bad_object_end)),
    "expected mismatch span on `bad_object`; got {mismatches:?}",
  );
  assert!(
    mismatches.iter().any(|diag| diag.primary.file == file_id
      && diag.primary.range == TextRange::new(bad_null_start, bad_null_end)),
    "expected mismatch span on `bad_null`; got {mismatches:?}",
  );
}

#[test]
fn empty_object_literal_infers_empty_object_type() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file0.ts");
  let source = r#"
let x = {};
x = 1;
x = null;
"#;
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();

  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert_eq!(mismatches.len(), 1, "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id for file0.ts");
  let null_offset = u32::try_from(source.find("= null").expect("bad null assignment"))
    .expect("offset fits in u32")
    + "= ".len() as u32;
  assert!(
    mismatches.iter().any(|diag| {
      diag.primary.file == file_id
        && diag.primary.range.start <= null_offset
        && diag.primary.range.end >= null_offset + 1
    }),
    "expected mismatch span to cover `null`; got {mismatches:?}",
  );
}
