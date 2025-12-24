fn main() {
  let code = "<div>text</div>";
  eprintln!("Parsing: {}", code);
  match parse_js::parse_with_options(
    code,
    parse_js::ParseOptions {
      dialect: parse_js::Dialect::Jsx,
      source_type: parse_js::SourceType::Module,
    },
  ) {
    Ok(_) => eprintln!("SUCCESS"),
    Err(e) => eprintln!("ERROR: {:?}", e),
  }
}
