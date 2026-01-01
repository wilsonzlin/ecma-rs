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
  host.insert(b_key.clone(), "import { v } from \"./m\";\n\ntype T = typeof v;\n");

  let c_key = FileKey::new("/c.ts");
  host.insert(c_key.clone(), "type U = import(\"./m\").Foo;\n");

  let program = Program::new(host, vec![a_key.clone(), b_key, c_key, m_key.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "unexpected diagnostics: {diagnostics:?}");

  let m_id = program.file_id(&m_key).expect("m.ts file id");
  let text = program.file_text(m_id).expect("m.ts text");

  let defs = program.definitions_in_file(m_id);
  let (v_def, init) = defs
    .iter()
    .copied()
    .filter(|def| program.def_name(*def).as_deref() == Some("v"))
    .filter_map(|def| program.var_initializer(def).map(|init| (def, init)))
    .find(|(def, _)| {
      let Some(span) = program.def_span(*def) else {
        return false;
      };
      if span.file != m_id {
        return false;
      }
      let start = span.range.start as usize;
      let end = span.range.end as usize;
      text
        .get(start..end)
        .map(|slice| slice == "v")
        .unwrap_or(false)
    })
    .expect("v variable definition with initializer should be present in m.ts");

  let init_ty = program.type_of_expr(init.body, init.expr);
  let init_ty_str = program.display_type(init_ty).to_string();
  assert_eq!(init_ty_str, "{ x: number }", "initializer type should be inferred");

  let exports = program.exports_of(m_id);
  let v_entry = exports.get("v").expect("v export entry");
  assert_eq!(v_entry.def, Some(v_def), "export should point at v definition");
  let export_ty = v_entry.type_id.expect("type for v export");
  let export_ty_str = program.display_type(export_ty).to_string();
  assert_eq!(export_ty_str, "{ x: number }");
}
