use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode};
use parse_js::{parse_with_options, ParseOptions, SourceType};

fn minify_ts_module(src: &str) -> String {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(TopLevelMode::Module).with_dialect(Dialect::Ts),
    src,
    &mut out,
  )
  .expect("minify should succeed");
  let code = String::from_utf8(out).expect("minifier output must be UTF-8");
  parse_with_options(
    &code,
    ParseOptions {
      dialect: Dialect::Js,
      source_type: SourceType::Module,
    },
  )
  .expect("output should parse as JavaScript");
  code
}

fn assert_instantiation_type_args_erased(src: &str) {
  let code = minify_ts_module(src);
  assert!(
    !code.contains('<') && !code.contains('>'),
    "expected instantiation type arguments to be erased, got: {code}"
  );
}

#[test]
fn erases_instantiation_type_arguments_in_common_positions() {
  assert_instantiation_type_args_erased("function f<T>(x:T){return x}; f<string>(1);");
  assert_instantiation_type_args_erased("function f<T>(x:T){return x}; const g=f<string>; g(1);");
}

#[test]
fn erases_instantiation_type_arguments_in_tagged_templates_and_optional_calls() {
  assert_instantiation_type_args_erased("tag<string>`tmpl`;");
  assert_instantiation_type_args_erased("fn?.<string>(x);");
}
