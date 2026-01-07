use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

#[test]
fn object_literal_async_modifier_must_not_cross_line_terminator() {
  assert!(parse_with_options("({ async\nfoo(){} })", js_script_opts()).is_err());
}

#[test]
fn object_literal_get_modifier_must_not_cross_line_terminator() {
  assert!(parse_with_options("({ get\nfoo(){} })", js_script_opts()).is_err());
}
