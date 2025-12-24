use emit_js::EmitMode;
use emit_js::EmitOptions;
use emit_js::Emitter;

fn text(emitter: &Emitter) -> String {
  String::from_utf8(emitter.as_bytes().to_vec()).unwrap()
}

#[test]
fn separates_keyword_and_identifier() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_keyword("return");
  emitter.write_identifier("value");
  assert_eq!(text(&emitter), "return value");
}

#[test]
fn separates_identifiers() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_identifier("foo");
  emitter.write_identifier("bar");
  assert_eq!(text(&emitter), "foo bar");
}

#[test]
fn separates_numbers_and_identifiers() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_number("123");
  emitter.write_identifier("abc");
  assert_eq!(text(&emitter), "123 abc");
}

#[test]
fn disambiguates_adjacent_plus_tokens() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_identifier("a");
  emitter.write_punct("+");
  emitter.write_punct("+");
  emitter.write_identifier("b");
  assert_eq!(text(&emitter), "a+ +b");
}

#[test]
fn disambiguates_plusplus_followed_by_plusplus() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_punct("++");
  emitter.write_punct("++");
  emitter.write_identifier("a");
  assert_eq!(text(&emitter), "++ ++a");
}

#[test]
fn disambiguates_plusplus_followed_by_plus() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_punct("++");
  emitter.write_punct("+");
  emitter.write_identifier("a");
  assert_eq!(text(&emitter), "++ +a");
}

#[test]
fn disambiguates_adjacent_minus_tokens() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_identifier("a");
  emitter.write_punct("-");
  emitter.write_punct("-");
  emitter.write_identifier("b");
  assert_eq!(text(&emitter), "a- -b");
}

#[test]
fn disambiguates_minusminus_followed_by_minusminus() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_punct("--");
  emitter.write_punct("--");
  emitter.write_identifier("a");
  assert_eq!(text(&emitter), "-- --a");
}

#[test]
fn disambiguates_minusminus_followed_by_minus() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_punct("--");
  emitter.write_punct("-");
  emitter.write_identifier("a");
  assert_eq!(text(&emitter), "-- -a");
}

#[test]
fn auto_classifies_raw_str_fragments() {
  let mut emitter = Emitter::new(EmitOptions {
    mode: EmitMode::Minified,
  });
  emitter.write_keyword("return");
  emitter.write_str("result");
  assert_eq!(text(&emitter), "return result");
}

#[test]
fn write_byte_tracks_boundaries() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_keyword("return");
  emitter.write_byte(b'x');
  assert_eq!(text(&emitter), "return x");
}

#[test]
fn canonical_mode_still_inserts_required_spaces() {
  let mut emitter = Emitter::new(EmitOptions {
    mode: EmitMode::Canonical,
  });
  emitter.write_keyword("return");
  emitter.write_identifier("value");
  assert_eq!(text(&emitter), "return value");
}

#[test]
fn separates_identifiers_from_numbers() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_identifier("foo");
  emitter.write_number("123");
  assert_eq!(text(&emitter), "foo 123");
}

#[test]
fn separates_numbers_from_numbers() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_number("1");
  emitter.write_number("2");
  assert_eq!(text(&emitter), "1 2");
}

#[test]
fn emits_punctuated_lists() {
  let mut emitter = Emitter::new(EmitOptions::default());
  let values = [1, 2, 3];
  emitter.emit_punctuated_list(&values, ",", false, |em, value| {
    em.write_number(value.to_string().as_str());
  });
  assert_eq!(text(&emitter), "1,2,3");

  emitter.clear();
  emitter.emit_punctuated_list(&values, ";", true, |em, value| {
    em.write_number(value.to_string().as_str());
  });
  assert_eq!(text(&emitter), "1;2;3;");
}

#[test]
fn avoids_forming_block_comment_after_division() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_identifier("a");
  emitter.write_punct("/");
  emitter.write_punct("*");
  emitter.write_identifier("b");
  let output = text(&emitter);
  assert!(!output.contains("/*"));
  assert_eq!(output, "a/ *b");
}

#[test]
fn avoids_forming_line_comment_from_adjacent_slashes() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_identifier("a");
  emitter.write_str("/");
  emitter.write_punct("/");
  emitter.write_identifier("b");
  let output = text(&emitter);
  assert!(!output.contains("//"));
  assert_eq!(output, "a/ /b");
}

#[test]
fn separates_regex_literal_from_following_division() {
  let mut emitter = Emitter::new(EmitOptions::default());
  emitter.write_str("/a/");
  emitter.write_punct("/");
  emitter.write_identifier("b");
  let output = text(&emitter);
  assert!(!output.contains("//"));
  assert_eq!(output, "/a/ /b");
}
