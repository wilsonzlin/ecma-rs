fn main() {
    let code = "<div>text</div>";
    eprintln!("Parsing: {}", code);
    match parse_js::parse(code) {
        Ok(_) => eprintln!("SUCCESS"),
        Err(e) => eprintln!("ERROR: {:?}", e),
    }
}
