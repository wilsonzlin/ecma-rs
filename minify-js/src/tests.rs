use crate::minify;
use parse_js::parse;
use symbol_js::TopLevelMode;

fn minified(mode: TopLevelMode, src: &str) -> String {
  let mut out = Vec::new();
  minify(mode, src, &mut out).unwrap();
  String::from_utf8(out).unwrap()
}

#[test]
fn test_shadow_safety() {
  let result = minified(
    TopLevelMode::Global,
    "let x=1;(()=>{let y=x;let x=2;return y})();",
  );
  assert_eq!(result, "let x=1;(()=>{let a=b;let b=2;return a})();");
}

#[test]
fn test_unknown_globals_not_shadowed() {
  let result = minified(
    TopLevelMode::Global,
    "console.log(x);(()=>{let console=1;})();",
  );
  assert_eq!(result, "console.log(x);(()=>{let a=1;})();");
}

#[test]
fn test_module_export_bindings_preserved() {
  let result = minified(TopLevelMode::Module, "export const x=1; const y=2;");
  assert_eq!(result, "export const x=1; const a=2;");
}

#[test]
fn test_export_function_inner_locals_renamed() {
  let result = minified(TopLevelMode::Module, "export function foo(){let bar=1;return bar;}");
  assert_eq!(result, "export function foo(){let a=1;return a;}");
}

#[test]
fn readme_example_is_parseable() {
  let code = "const main = () => { let my_first_variable = 1; };";
  let result = minified(TopLevelMode::Global, code);
  parse(&result).expect("minified output should be parseable JavaScript");
}
