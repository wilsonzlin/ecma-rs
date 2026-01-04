use typecheck_ts::{FileKey, MemoryHost, Program};

fn render_tree(program: &Program, tree: &typecheck_ts::ExplainTree) -> String {
  fn write_node(
    program: &Program,
    node: &typecheck_ts::ExplainTree,
    indent: usize,
    out: &mut String,
  ) {
    use std::fmt::Write;

    for _ in 0..indent {
      out.push_str("  ");
    }
    let relation = format!("{:?}", node.relation);
    let outcome = if node.outcome { "ok" } else { "fail" };
    let src = program.display_type(node.src);
    let dst = program.display_type(node.dst);
    let _ = write!(out, "{relation} ({outcome}): {src} -> {dst}");
    if let Some(note) = node.note.as_deref() {
      let _ = write!(out, " [{note}]");
    }
    out.push('\n');
    for child in &node.children {
      write_node(program, child, indent + 1, out);
    }
  }

  let mut out = String::new();
  write_node(program, tree, 0, &mut out);
  out
}

#[test]
fn explain_assignability_output_is_stable_for_a_known_mismatch() {
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  let source = "const value: number | string = true;";
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id available");

  let src_offset = source.find("true").expect("expected 'true' in source") as u32;
  let dst_offset = source.find("value").expect("expected 'value' in source") as u32;

  let src_ty = program.type_at(file_id, src_offset).expect("type at src");
  let dst_ty = program.type_at(file_id, dst_offset).expect("type at dst");

  let first = program
    .explain_assignability(src_ty, dst_ty)
    .expect("expected mismatch explanation");
  let second = program
    .explain_assignability(src_ty, dst_ty)
    .expect("expected mismatch explanation");

  let rendered = render_tree(&program, &first);
  assert_eq!(rendered, render_tree(&program, &second));

  let expected = concat!(
    "Assignable (fail): true -> number | string [union target]\n",
    "  Assignable (fail): true -> number [structural]\n",
    "  Assignable (fail): true -> string [structural]\n",
  );
  assert_eq!(rendered, expected);
}
