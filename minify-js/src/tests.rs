use crate::minify;
use symbol_js::TopLevelMode;

#[test]
fn test_minify() {
  let mut out = Vec::new();
  minify(
    TopLevelMode::Global,
    r##"

  let myvar = 1;

  "##
      ,
    &mut out,
  )
  .unwrap();
}
