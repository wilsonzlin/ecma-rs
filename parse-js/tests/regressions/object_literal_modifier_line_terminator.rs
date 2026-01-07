use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

#[test]
fn object_literal_async_modifier_must_not_cross_line_terminator() {
  assert!(parse_with_options("({ async\nfoo(){} })", ecma_script_opts()).is_err());
}

#[test]
fn object_literal_get_modifier_must_not_cross_line_terminator() {
  assert!(parse_with_options("({ get\nfoo(){} })", ecma_script_opts()).is_err());
}

#[test]
fn object_literal_set_modifier_must_not_cross_line_terminator() {
  assert!(parse_with_options("({ set\nfoo(v){} })", ecma_script_opts()).is_err());
}
