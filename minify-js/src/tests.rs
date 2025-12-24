use crate::minify;
use crate::{FileId, Severity, TopLevelMode};
use parse_js::parse;

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
fn returns_diagnostics_on_parse_error() {
  let mut output = Vec::new();
  let diagnostics = minify(TopLevelMode::Global, "let =", &mut output).unwrap_err();
  assert_eq!(diagnostics.len(), 1);
  let diagnostic = &diagnostics[0];
  assert!(diagnostic.code.as_str().starts_with("PS"));
  assert_eq!(diagnostic.primary.file, FileId(0));
  assert_eq!(diagnostic.severity, Severity::Error);
}

#[test]
fn test_export_function_inner_locals_renamed() {
  let result = minified(
    TopLevelMode::Module,
    "export function foo(){let bar=1;return bar;}",
  );
  assert_eq!(result, "export function foo(){let a=1;return a;}");
}

#[test]
fn test_minify_determinism() {
  let src =
    "const foo=1; const qux=2; function bar(){ let baz=foo+qux; return baz; } export { bar };";
  let first = minified(TopLevelMode::Module, src);
  let second = minified(TopLevelMode::Module, src);
  assert_eq!(first, second);
}

#[test]
fn readme_example_is_parseable() {
  let code = "const main = () => { let my_first_variable = 1; };";
  let result = minified(TopLevelMode::Global, code);
  parse(&result).expect("minified output should be parseable JavaScript");
}

#[test]
fn test_with_statement_disables_renaming() {
  let src = "with ({x:2}){x}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, src);
}

#[test]
fn test_direct_eval_disables_renaming() {
  let src = "function f(){let x;eval(\"x\");}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, src);
}

#[test]
fn test_shadowed_eval_allows_renaming() {
  let result = minified(TopLevelMode::Global, "function f(eval){let x;eval(\"x\");}");
  assert_eq!(result, "function f(a){let b;a(\"x\");}");
}
