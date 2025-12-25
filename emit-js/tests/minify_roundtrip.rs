use emit_js::{emit_top_level_stmt, EmitOptions, Emitter};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn roundtrip(src: &str, opts: ParseOptions) {
  let ast =
    parse_with_options(src, opts).unwrap_or_else(|err| panic!("parse input {src:?}: {err:?}"));
  let mut emitter = Emitter::new(EmitOptions::minified());
  emit_top_level_stmt(&mut emitter, ast.stx.as_ref()).expect("emit minified output");
  let output = String::from_utf8(emitter.into_bytes()).expect("emitter output is UTF-8");
  parse_with_options(&output, opts)
    .unwrap_or_else(|err| panic!("minified output {output:?}: {err:?}"));
}

#[test]
fn minify_roundtrip_matrix() {
  let default_opts = ParseOptions::default();
  let module_opts = ParseOptions {
    source_type: SourceType::Module,
    ..ParseOptions::default()
  };
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
      "const built=tag`chunk${value}x`;",
    ),
    (default_opts, "const tpl=`chunk`;"),
    (
      module_opts,
      "export const chain=(a ?? b?.c) && d?.[key]?.(next ?? (()=>value))?.result;",
    ),
    (
      jsx_opts,
      "export default <Fragment>{items?.map?.((item,i)=><Item key={i}>{item?.label ?? \"\"}</Item>) ?? <Fallback/>}</Fragment>;",
    ),
    (
      default_opts,
      "const regex=/\\d+(?:\\.\\d+)?/gi.test(input)||/^[a-z]+$/i.test(other);",
    ),
    (
      default_opts,
      "const ctor=new (factory?.())(config?.options ?? {});",
    ),
    (
      default_opts,
      "async function run(){return await task?.(input ?? defaultVal);}",
    ),
    (
      jsx_opts,
      "export default <div>{items?.[0] ?? <span data-tag={label}>{label ?? \"\"}</span>}</div>;",
    ),
    (default_opts, "const tagged=tag`a`;"),
  ];

  for (opts, src) in cases {
    roundtrip(src, opts);
  }
}
