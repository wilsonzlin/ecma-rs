use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::Diagnostic;
use diagnostics::FileId;
use minify_js::TopLevelMode;
use neon::prelude::*;
use neon::types::buffer::TypedArray;
use serde_json::Value;

fn parse_top_level_mode(value: &str) -> Option<TopLevelMode> {
  match value {
    "global" => Some(TopLevelMode::Global),
    "module" => Some(TopLevelMode::Module),
    _ => None,
  }
}

struct SingleFileSource<'a> {
  name: &'a str,
  text: &'a str,
}

impl<'a> SourceProvider for SingleFileSource<'a> {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some(self.name)
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    Some(self.text)
  }
}

fn diagnostics_to_js_value<'a>(
  cx: &mut FunctionContext<'a>,
  diagnostics: &[Diagnostic],
) -> JsResult<'a, JsValue> {
  let value = match serde_json::to_value(diagnostics) {
    Ok(value) => value,
    Err(err) => return cx.throw_error(format!("failed to serialize diagnostics to JSON: {err}")),
  };
  json_to_js_value(cx, &value)
}

fn json_to_js_value<'a>(cx: &mut FunctionContext<'a>, value: &Value) -> JsResult<'a, JsValue> {
  match value {
    Value::Null => Ok(cx.null().upcast()),
    Value::Bool(v) => Ok(cx.boolean(*v).upcast()),
    Value::Number(v) => Ok(cx.number(v.as_f64().unwrap_or(0.0)).upcast()),
    Value::String(v) => Ok(cx.string(v.as_str()).upcast()),
    Value::Array(values) => {
      let js_array = JsArray::new(cx, values.len() as u32);
      for (idx, child) in values.iter().enumerate() {
        let js_value = json_to_js_value(cx, child)?;
        js_array.set(cx, idx as u32, js_value)?;
      }
      Ok(js_array.upcast())
    }
    Value::Object(map) => {
      let js_object = JsObject::new(cx);
      for (key, value) in map {
        let js_value = json_to_js_value(cx, value)?;
        js_object.set(cx, key.as_str(), js_value)?;
      }
      Ok(js_object.upcast())
    }
  }
}

fn minify(mut cx: FunctionContext) -> JsResult<JsBuffer> {
  let top_level_mode_raw = cx.argument::<JsString>(0).map(|v| v.value(&mut cx))?;
  let top_level_mode = match parse_top_level_mode(&top_level_mode_raw) {
    Some(mode) => mode,
    None => return cx.throw_type_error("invalid top-level mode"),
  };

  let src_arg = cx.argument::<JsValue>(1)?;
  let source = if let Ok(js_string) = src_arg.downcast::<JsString, _>(&mut cx) {
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
  match minify_js::minify(top_level_mode, &source, &mut out) {
    Ok(()) => Ok(JsBuffer::external(&mut cx, out)),
    Err(diagnostics) => {
      let provider = SingleFileSource {
        name: "<input>",
        text: &source,
      };
      let mut rendered = String::new();
      for (idx, diagnostic) in diagnostics.iter().enumerate() {
        if idx > 0 && !rendered.ends_with('\n') {
          rendered.push('\n');
        }
        rendered.push_str(&render_diagnostic(&provider, diagnostic));
      }

      let diagnostics_value = diagnostics_to_js_value(&mut cx, &diagnostics)?;
      let error = cx.error(rendered)?;
      error.set(&mut cx, "diagnostics", diagnostics_value)?;
      cx.throw(error)
    }
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
