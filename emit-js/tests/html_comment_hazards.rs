use emit_js::{EmitOptions, Emitter};

fn text(emitter: Emitter) -> String {
  String::from_utf8(emitter.into_bytes()).expect("emitter output should be UTF-8")
}

#[test]
fn avoids_open_html_comment_after_newline() {
  let mut emitter = Emitter::new(EmitOptions::canonical());
  emitter.write_identifier("foo");
  emitter.write_byte(b'\n');
  emitter.write_punct("<");
  emitter.write_punct("!");
  emitter.write_punct("--");
  emitter.write_identifier("bar");
  emitter.write_punct(";");

  let output = text(emitter);
  assert!(
    !output.contains("\n<!--"),
    "output should not start a line with <!--: {output}"
  );
  parse_js::parse(&output).expect("emitted code should parse");
}

#[test]
fn avoids_close_html_comment_after_newline() {
  let mut emitter = Emitter::new(EmitOptions::canonical());
  emitter.write_str("/*");
  emitter.write_byte(b'\n');
  emitter.write_punct("--");
  emitter.write_punct(">");
  emitter.write_identifier("comment");
  emitter.write_byte(b'\n');
  emitter.write_str("*/");
  emitter.write_byte(b'\n');
  emitter.write_number("0");
  emitter.write_punct(";");

  let output = text(emitter);
  assert!(
    !output.contains("\n-->"),
    "output should not start a line with -->: {output}"
  );
  parse_js::parse(&output).expect("emitted code should parse");
}
