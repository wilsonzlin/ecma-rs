use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};
use parse_js::parse;
use serde_json::Value;

mod util;

fn syntax_value(source: &str) -> Value {
  let ast = parse(source).expect("parse source");
  util::serialize_without_locs(&ast)
}

fn assert_roundtrip(source: &str, expected: &str) {
  let lowered = lower_from_source_with_kind(FileKind::Ts, source).expect("lower source");
  let emitted =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit lowered program");
  assert_eq!(emitted, expected);

  let original = syntax_value(source);
  let reparsed = syntax_value(&emitted);
  assert_eq!(
    original, reparsed,
    "roundtrip via HIR changed syntax\nsource: {source}\nemitted: {emitted}"
  );

  let lowered = lower_from_source_with_kind(FileKind::Ts, &emitted).expect("lower emitted output");
  let reemitted =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("re-emit lowered program");
  assert_eq!(reemitted, expected);
}

#[test]
fn parenthesizes_object_literal_bodies() {
  assert_roundtrip(
    "function f(){return x=>({a:1});}",
    "function f(){return(x)=>({a:1});}",
  );
}

#[test]
fn parenthesizes_comma_bodies() {
  assert_roundtrip(
    "function f(){return x=>(a,b);}",
    "function f(){return(x)=>(a,b);}",
  );
}

#[test]
fn parenthesizes_arrow_in_member_chain() {
  assert_roundtrip(
    "function f(){return (x=>({a:1})).prop;}",
    "function f(){return((x)=>({a:1})).prop;}",
  );
}
