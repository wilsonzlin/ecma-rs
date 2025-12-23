use crate::minify;
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

