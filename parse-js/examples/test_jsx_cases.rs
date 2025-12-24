fn main() {
  let cases = vec![
    ("<div></div>", "empty"),
    ("<div> </div>", "whitespace"),
    ("<div>text</div>", "text"),
    ("<div>x</div>", "single char"),
    ("<Comp>text</Comp>", "uppercase component with text"),
    ("<div><span>nested</span></div>", "nested"),
    ("<div>text1<span>text2</span>text3</div>", "mixed"),
  ];

  let mut passed = 0;
  let mut failed = 0;

  for (code, desc) in cases {
    match parse_js::parse_with_options(
      code,
      parse_js::ParseOptions {
        dialect: parse_js::Dialect::Jsx,
        source_type: parse_js::SourceType::Module,
      },
    ) {
      Ok(_) => {
        println!("✓ {}", desc);
        passed += 1;
      }
      Err(e) => {
        println!("✗ {}: {:?}", desc, e);
        failed += 1;
      }
    }
  }

  println!("\n{} passed, {} failed", passed, failed);
}
