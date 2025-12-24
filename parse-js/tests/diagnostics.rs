#![cfg(feature = "diagnostics")]

use diagnostics::{FileId, TextRange};
use parse_js::error::{SyntaxError, SyntaxErrorType};
use parse_js::loc::Loc;
use parse_js::token::TT;

#[test]
fn converts_syntax_error_to_diagnostic() {
  let error = SyntaxError::new(
    SyntaxErrorType::ExpectedSyntax("identifier"),
    Loc(2, 5),
    Some(TT::LiteralNumber),
  );
  let diagnostic = error.to_diagnostic(FileId(1));

  assert_eq!(diagnostic.code, "PS0002");
  assert_eq!(diagnostic.primary.file, FileId(1));
  assert_eq!(diagnostic.primary.range, TextRange::new(2, 5));
  assert!(diagnostic
    .notes
    .iter()
    .any(|note| note.contains("expected identifier")));
  assert!(diagnostic
    .notes
    .iter()
    .any(|note| note.contains("found token: LiteralNumber")));
}

#[test]
fn records_overflow_note_from_loc() {
  let loc = Loc(usize::MAX - 1, usize::MAX);
  let err = SyntaxError::new(SyntaxErrorType::ExpectedNotFound, loc, None);
  let diagnostic = err.to_diagnostic(FileId(0));
  assert_eq!(diagnostic.primary.range.start, u32::MAX);
  assert_eq!(diagnostic.primary.range.end, u32::MAX);
  assert!(diagnostic
    .notes
    .iter()
    .any(|note| note.contains("truncated")));
}

#[test]
fn loc_conversion_is_lossless_when_fitting() {
  let loc = Loc(10, 20);
  let range: TextRange = loc.into();
  assert_eq!(range, TextRange::new(10, 20));
}
