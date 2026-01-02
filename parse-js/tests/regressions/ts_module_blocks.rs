use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ts_module_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  }
}

#[test]
fn export_const_enum_is_parsed() {
  parse_with_options("export const enum E { A, B }", ts_module_opts()).unwrap();
}

#[test]
fn declare_global_allows_export_lists() {
  parse_with_options(
    "declare global { export { globalThis as global } }",
    ts_module_opts(),
  )
  .unwrap();
}

