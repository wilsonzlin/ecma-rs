use emit_js::{emit_top_level_stmt, EmitOptions, Emitter};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn roundtrip(src: &str, opts: ParseOptions) {
  let ast = parse_with_options(src, opts).expect("parse input");
  let mut emitter = Emitter::new(EmitOptions::minified());
  emit_top_level_stmt(&mut emitter, ast.stx.as_ref()).expect("emit minified output");
  let output = String::from_utf8(emitter.into_bytes()).expect("emitter output is UTF-8");
  parse_with_options(&output, opts).expect("minified output should parse");
}

#[test]
fn minify_roundtrip_matrix() {
  let default_opts = ParseOptions::default();
  let jsx_opts = ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Module,
  };

  let cases = [
    (
      default_opts,
      "const combo=(a??b)&&c||d; const chain=a?.b?.[key]?.(next?.());",
    ),
    (
      default_opts,
      "const built=new (Ctor?.factory)(tag`chunk${value?.inner}`);",
    ),
    (default_opts, "const tpl=`line1\n${a?.b}`;"),
    (
      jsx_opts,
      "export default <div>{items?.[0] ?? <span data-tag={tag`x${label}`}>{label ?? \"\"}</span>}</div>;",
    ),
    (default_opts, "const tagged=tag`a${fnRef?.()}`;"),
  ];

  for (opts, src) in cases {
    roundtrip(src, opts);
  }
}
