use diagnostics::{FileId, Label, Span, TextRange};
use typecheck_ts::codes;

#[test]
fn normalize_sorts_diagnostics_and_labels() {
  let mut later =
    codes::TYPE_MISMATCH.error("later span", Span::new(FileId(1), TextRange::new(5, 6)));
  later.push_label(Label::secondary(
    Span::new(FileId(1), TextRange::new(0, 1)),
    "secondary",
  ));
  later.push_label(Label::primary(
    Span::new(FileId(1), TextRange::new(5, 6)),
    "primary",
  ));

  let mut earlier =
    codes::UNKNOWN_IDENTIFIER.error("earlier span", Span::new(FileId(0), TextRange::new(10, 11)));
  earlier.push_label(Label::secondary(
    Span::new(FileId(0), TextRange::new(2, 3)),
    "later secondary",
  ));
  earlier.push_label(Label::secondary(
    Span::new(FileId(0), TextRange::new(0, 1)),
    "earlier secondary",
  ));

  let mut diagnostics = vec![later, earlier];
  codes::normalize_diagnostics(&mut diagnostics);

  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::UNKNOWN_IDENTIFIER.as_str()
  );
  assert_eq!(diagnostics[1].code.as_str(), codes::TYPE_MISMATCH.as_str());

  let first_labels = &diagnostics[0].labels;
  assert_eq!(first_labels.len(), 2);
  assert_eq!(first_labels[0].span.range.start, 0);
  assert_eq!(first_labels[1].span.range.start, 2);

  let second_labels = &diagnostics[1].labels;
  assert!(!second_labels.is_empty());
  assert!(second_labels[0].is_primary);
}
