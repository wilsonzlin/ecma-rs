use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn computed_member_rejects_symbol_for_string_like_intersection_indexer() {
  let mut host = MemoryHost::default();
  let source = "declare const sym: symbol;\n\
                declare const obj: { [k: (string | symbol) & string]: boolean };\n\
                const value = obj[sym];\n\
                value;";
  let file = FileKey::new("input.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");

  // Ensure the declared index signature preserved the intersection key type.
  let obj_offset = source
    .find("obj[sym]")
    .expect("obj use site")
    .try_into()
    .expect("offset fits u32");
  let obj_ty = program.type_at(file_id, obj_offset).expect("type of obj");
  let indexers = program.indexers(obj_ty);
  assert_eq!(indexers.len(), 1);
  assert!(
    matches!(program.interned_type_kind(indexers[0].key_type), TypeKind::Intersection(_)),
    "expected an intersection key type, got {:?}",
    program.interned_type_kind(indexers[0].key_type)
  );

  let sym_offset = source
    .find("[sym]")
    .expect("computed member")
    .saturating_add(1)
    .try_into()
    .expect("offset fits u32");
  let sym_ty = program.type_at(file_id, sym_offset).expect("type of sym");
  assert_eq!(program.display_type(sym_ty).to_string(), "symbol");

  // Pick the '[' token so we select the computed-member expression span, not the inner identifiers.
  let offset = source
    .find("[sym]")
    .expect("computed member")
    .try_into()
    .expect("offset fits u32");
  let (body, expr) = program.expr_at(file_id, offset).expect("expr at offset");
  let span = program.span_of_expr(body, expr).expect("span of expr");
  let snippet = &source[span.range.start as usize..span.range.end as usize];
  assert!(
    snippet.contains("obj") && snippet.contains("sym"),
    "expected computed member expr span, got {snippet:?}"
  );
  let ty = program.type_at(file_id, offset).expect("type at offset");

  assert_eq!(program.display_type(ty).to_string(), "unknown");
}

#[test]
fn number_indexer_does_not_satisfy_named_string_properties() {
  let mut host = MemoryHost::default();
  let source = "declare const obj: { [n: number]: boolean };\n\
                const value = obj.foo;\n\
                value;";
  let file = FileKey::new("input.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");

  // Pick the '.' token so we select the member-expression span, not `obj` or `foo`.
  let offset = source
    .find(".foo")
    .expect("member access")
    .try_into()
    .expect("offset fits u32");
  let ty = program.type_at(file_id, offset).expect("type at offset");

  assert_eq!(program.display_type(ty).to_string(), "unknown");
}
