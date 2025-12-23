use crate::minify;
use crate::Session;
use symbol_js::TopLevelMode;

#[test]
fn test_minify() {
  let mut out = Vec::new();
  let session = Session::new();
  minify(
    &session,
    TopLevelMode::Global,
    r##"

  let myvar = 1;

  "##
      .as_bytes(),
    &mut out,
  )
  .unwrap();
}
