use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn export_const_object_literal_is_typed_in_virtual_paths() {
  let mut host = MemoryHost::new();

  let m_key = FileKey::new("/m.ts");
  host.insert(
    m_key.clone(),
    "export interface Foo {\n  x: number;\n}\n\nexport const v = { x: 1 };\n",
  );

  let a_key = FileKey::new("/a.ts");
  host.insert(
    a_key.clone(),
    "import type { Foo } from \"./m\";\nimport { v } from \"./m\";\n\nlet y: Foo = v;\n",
  );

  let b_key = FileKey::new("/b.ts");
  host.insert(
    b_key.clone(),
    "import { v } from \"./m\";\n\ntype T = typeof v;\n",
  );

  let c_key = FileKey::new("/c.ts");
  host.insert(c_key.clone(), "type U = import(\"./m\").Foo;\n");

  let program = Program::new(host, vec![a_key.clone(), b_key, c_key, m_key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let m_id = program.file_id(&m_key).expect("m.ts file id");
  let text = program.file_text(m_id).expect("m.ts text");

  let exports = program.exports_of(m_id);
  let v_entry = exports.get("v").expect("v export entry");
  let v_def = v_entry.def.expect("v export should point at a local def");

  let defs = program.definitions_in_file(m_id);
  assert!(
    defs.contains(&v_def),
    "v definition should be listed in m.ts definitions"
  );

  let init = program
    .var_initializer(v_def)
    .expect("v variable definition should have initializer metadata");

  let span = program.def_span(v_def).expect("v definition span");
  assert_eq!(span.file, m_id);
  let start = span.range.start as usize;
  let end = span.range.end as usize;
  let slice = text.get(start..end).unwrap_or_default();
  assert!(
    slice.starts_with('v'),
    "expected def span to start at `v`, got {slice:?}"
  );

  let init_ty = program.type_of_expr(init.body, init.expr);
  let init_ty_str = program.display_type(init_ty).to_string();
  assert_eq!(
    init_ty_str, "{ x: number }",
    "initializer type should be inferred"
  );

  let export_ty = v_entry.type_id.expect("type for v export");
  let export_ty_str = program.display_type(export_ty).to_string();
  assert_eq!(export_ty_str, "{ x: number }");
}
