use parse_js::error::SyntaxErrorType;
use parse_js::token::TT;
use parse_js::{parse_with_options_detailed, Dialect, ParseOptions, SourceType};

fn ts_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

#[test]
fn computed_key_paren_comma_arrow_parses() {
  // Nested arrow in a default-like assignment inside `(…, "_")` must not
  // sticky-commit outer arrow speculation (privateNameComputedPropertyName2).
  let src = r#"
let getX: (a: A) => number;
class A {
    #x = 100;
    [(getX = (a: A) => a.#x, "_")]() {}
}
console.log(getX(new A));
"#;
  let result = parse_with_options_detailed(src, ts_script()).expect("parse");
  assert!(result.ast.stx.body.len() >= 3);
  assert!(
    result.soft_errors.is_empty(),
    "unexpected soft errors: {:?}",
    result.soft_errors
  );
}

#[test]
fn indexed_access_private_soft_expects_bracket_close() {
  // `C[#bar]` is not indexed access; soft `]` expected and keep parsing.
  let src = r##"
class C {
    #bar = 3;
    constructor () {
        const badForNow: C[#bar] = 3;
        const badAlways: C["#bar"] = 3;
    }
}
"##;
  let result = parse_with_options_detailed(src, ts_script()).expect("parse");
  assert!(
    result
      .soft_errors
      .iter()
      .any(|e| e.typ == SyntaxErrorType::RequiredTokenNotFound(TT::BracketClose)),
    "expected soft ']' expected, got {:?}",
    result.soft_errors
  );
}
