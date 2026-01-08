use std::sync::Arc;
use vm_js::format_stack_trace;
use vm_js::SourceText;
use vm_js::StackFrame;

#[test]
fn source_text_line_col_handles_newlines_tabs_and_utf8() {
  let text = "a\té\nb🙂c\n";
  let source = SourceText::new("<inline>", text);

  // Byte offsets are used as the input; reported columns are Unicode scalar
  // values (tab counts as 1).
  let offset_e = text.find('é').unwrap() as u32;
  assert_eq!(source.line_col(offset_e), (1, 3));

  let offset_b = text.find('b').unwrap() as u32;
  assert_eq!(source.line_col(offset_b), (2, 1));

  let offset_c = text.find('c').unwrap() as u32;
  assert_eq!(source.line_col(offset_c), (2, 3));

  // Clamp offsets that point inside a UTF-8 sequence.
  let offset_emoji = text.find('🙂').unwrap();
  assert_eq!(source.line_col((offset_emoji + 1) as u32), (2, 2));
}

#[test]
fn stack_trace_formatting_is_stable() {
  let frames = vec![
    StackFrame {
      function: Some(Arc::<str>::from("foo")),
      source: Arc::<str>::from("script.js"),
      line: 1,
      col: 5,
    },
    StackFrame {
      function: None,
      source: Arc::<str>::from("script.js"),
      line: 2,
      col: 1,
    },
  ];

  let rendered = format_stack_trace(&frames);
  let expected = "at foo (script.js:1:5)\nat script.js:2:1";
  assert_eq!(rendered, expected);
}

