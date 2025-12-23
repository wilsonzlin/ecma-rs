use minify_js::TopLevelMode;
use neon::prelude::*;
use neon::types::buffer::TypedArray;

fn parse_top_level_mode(value: &str) -> Option<TopLevelMode> {
  match value {
    "global" => Some(TopLevelMode::Global),
    "module" => Some(TopLevelMode::Module),
    _ => None,
  }
}

fn minify(mut cx: FunctionContext) -> JsResult<JsBuffer> {
  let top_level_mode_raw = cx.argument::<JsString>(0).map(|v| v.value(&mut cx))?;
  let top_level_mode = match parse_top_level_mode(&top_level_mode_raw) {
    Some(mode) => mode,
    None => return cx.throw_type_error("invalid top-level mode"),
  };

  let src_arg = cx.argument::<JsValue>(1)?;
  let source_str = if let Ok(js_string) = src_arg.downcast::<JsString, _>(&mut cx) {
    js_string.value(&mut cx)
  } else if let Ok(js_buffer) = src_arg.downcast::<JsBuffer, _>(&mut cx) {
    let bytes = js_buffer.as_slice(&mut cx);
    match std::str::from_utf8(bytes) {
      Ok(s) => s.to_owned(),
      Err(_) => return cx.throw_type_error("src buffer must be valid UTF-8"),
    }
  } else {
    return cx.throw_type_error("src must be a string or Buffer");
  };

  let mut out = Vec::new();
  match minify_js::minify(top_level_mode, &source_str, &mut out) {
    Ok(()) => Ok(JsBuffer::external(&mut cx, out)),
    Err(err) => cx.throw_error(format!("{:?}", err)),
  }
}

#[neon::main]
fn main(mut cx: ModuleContext) -> NeonResult<()> {
  cx.export_function("minify", minify)?;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parses_top_level_mode() {
    assert_eq!(parse_top_level_mode("global"), Some(TopLevelMode::Global));
    assert_eq!(parse_top_level_mode("module"), Some(TopLevelMode::Module));
    assert_eq!(parse_top_level_mode("unknown"), None);
  }
}
