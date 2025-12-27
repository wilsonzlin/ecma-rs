use std::sync::Arc;

use hir_js::{lower_file_with_diagnostics, FileKind as HirFileKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn debug_narrowing() {
  let path = [
    env!("CARGO_MANIFEST_DIR"),
    "tests/litmus/narrowing_patterns/main.ts",
  ]
  .join("/");
  let source = std::fs::read_to_string(path).expect("read fixture");
  let mut host = MemoryHost::default();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), Arc::from(source));
  let program = Program::new(host, vec![key.clone()]);
  program.check();
  let file_id = program.file_id(&key).expect("file id");
  for def in program.definitions_in_file(file_id) {
    if let Some(name) = program.def_name(def) {
      if name == "assertNumber" || name == "useAssert" {
        let ty = program.type_of_def(def);
        println!("DEBUG def {} => {}", name, program.display_type(ty));
      }
    }
  }
  let snap = program.snapshot();
  for entry in snap.def_data.iter() {
    if entry.data.file == file_id
      && (entry.data.name == "assertNumber" || entry.data.name == "useAssert")
    {
      println!(
        "DEBUG snapshot def {:?} kind {:?}",
        entry.def, entry.data.kind
      );
    }
  }
  let ast = parse_with_options(
    program.file_text(file_id).as_deref().expect("text"),
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let (lowered, _) = lower_file_with_diagnostics(file_id, HirFileKind::Ts, &ast);
  let offset = 775u32;
  println!("program expr_at: {:?}", program.expr_at(file_id, offset));
  println!(
    "span_map expr_at: {:?}",
    lowered.hir.span_map.expr_span_at_offset(offset)
  );
  let mut nearest: Option<(u32, hir_js::ExprId, diagnostics::TextRange, hir_js::BodyId)> = None;
  for body_id in lowered
    .hir
    .bodies
    .iter()
    .copied()
    .chain(std::iter::once(lowered.root_body()))
  {
    if let Some(body) = lowered.body(body_id) {
      for (idx, expr) in body.exprs.iter().enumerate() {
        let distance = if offset < expr.span.start {
          expr.span.start - offset
        } else if offset > expr.span.end {
          offset - expr.span.end
        } else {
          0
        };
        nearest = match nearest.take() {
          None => Some((distance, hir_js::ExprId(idx as u32), expr.span, body_id)),
          Some(current) if distance < current.0 => {
            Some((distance, hir_js::ExprId(idx as u32), expr.span, body_id))
          }
          Some(current) => Some(current),
        };
      }
    }
  }
  if let Some((dist, expr_id, span, body)) = nearest {
    let res = program.check_body(body);
    let ty = res.expr_type(expr_id).unwrap();
    println!(
      "nearest expr span {:?} dist {dist} type {}",
      span,
      program.display_type(ty)
    );
  }
  if let Some((body, expr)) = program.expr_at(file_id, offset) {
    let res = program.check_body(body);
    println!("expr span {:?}", res.expr_span(expr));
    if let Some(ty) = res.expr_type(expr) {
      println!("expr type {}", program.display_type(ty));
    }
  }
}
