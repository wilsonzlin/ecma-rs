use hir_js::{lower_from_source_with_kind, FileKind};

const SOURCE: &str = r#"export function add(a: number, b: number) {
  return a + b;
}

export const total = add(1, 2);
"#;

fn main() {
  let lowered = lower_from_source_with_kind(FileKind::Ts, SOURCE).expect("lowering succeeds");
  let hir = lowered.hir.as_ref();

  println!("file_kind: {:?}", hir.file_kind);
  println!("defs: {}", lowered.defs.len());
  println!("bodies: {}", lowered.bodies.len());

  // `SpanMap` provides deterministic byte-offset lookups for the innermost
  // expression/definition spans.
  let call_offset = SOURCE.find("add(1, 2)").expect("call site exists") as u32;
  if let Some(hit) = hir.span_map.expr_span_at_offset(call_offset) {
    let (body, expr) = hit.id;
    println!(
      "expr_at_offset({call_offset}): body={body:?} expr={expr:?} span={:?}",
      hit.range
    );
    let snippet = &SOURCE[hit.range.start as usize..hit.range.end as usize];
    println!("  snippet: {snippet:?}");
  }

  let total_offset = SOURCE.find("total").expect("total exists") as u32;
  if let Some(hit) = hir.span_map.def_span_at_offset(total_offset) {
    println!("def_at_offset({total_offset}): def={:?} span={:?}", hit.id, hit.range);
  }
}

