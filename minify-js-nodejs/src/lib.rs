use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::Diagnostic;
use diagnostics::FileId;
use minify_js::{Dialect, MinifyOptions, TopLevelMode, TsEraseOptions};
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

#[derive(Clone, Copy, Debug)]
struct ParsedOptions {
  dialect: Option<Dialect>,
  ts_erase_options: TsEraseOptions,
}

fn parse_minify_options(
  dialect: Option<&str>,
  ts_lower_class_fields: Option<bool>,
  ts_use_define_for_class_fields: Option<bool>,
) -> Result<ParsedOptions, String> {
  let dialect = match dialect {
    None | Some("auto") => None,
    Some("js") => Some(Dialect::Js),
    Some("jsx") => Some(Dialect::Jsx),
    Some("ts") => Some(Dialect::Ts),
    Some("tsx") => Some(Dialect::Tsx),
    Some("dts") => Some(Dialect::Dts),
    Some(other) => return Err(format!(
      "invalid dialect {other:?} (expected \"auto\", \"js\", \"jsx\", \"ts\", \"tsx\", or \"dts\")"
    )),
  };

  let mut ts_erase_options = TsEraseOptions::default();
  if let Some(value) = ts_lower_class_fields {
    ts_erase_options.lower_class_fields = value;
  }
  if let Some(value) = ts_use_define_for_class_fields {
    ts_erase_options.use_define_for_class_fields = value;
  }

  Ok(ParsedOptions {
    dialect,
    ts_erase_options,
  })
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

  let options_arg = cx.argument_opt(2);
  let (dialect_raw, ts_lower_class_fields, ts_use_define_for_class_fields): (
    Option<String>,
    Option<bool>,
    Option<bool>,
  ) = if let Some(options) = options_arg {
    if options.is_a::<JsUndefined, _>(&mut cx) || options.is_a::<JsNull, _>(&mut cx) {
      (None, None, None)
    } else if let Ok(options) = options.downcast::<JsObject, _>(&mut cx) {
      let dialect_raw: Handle<JsValue> = options.get(&mut cx, "dialect")?;
      let dialect_raw =
        if dialect_raw.is_a::<JsUndefined, _>(&mut cx) || dialect_raw.is_a::<JsNull, _>(&mut cx) {
          None
        } else if let Ok(value) = dialect_raw.downcast::<JsString, _>(&mut cx) {
          Some(value.value(&mut cx))
        } else {
          return cx.throw_type_error("options.dialect must be a string");
        };

      let ts_lower_class_fields: Handle<JsValue> = options.get(&mut cx, "tsLowerClassFields")?;
      let ts_lower_class_fields = if ts_lower_class_fields.is_a::<JsUndefined, _>(&mut cx)
        || ts_lower_class_fields.is_a::<JsNull, _>(&mut cx)
      {
        None
      } else if let Ok(value) = ts_lower_class_fields.downcast::<JsBoolean, _>(&mut cx) {
        Some(value.value(&mut cx))
      } else {
        return cx.throw_type_error("options.tsLowerClassFields must be a boolean");
      };

      let ts_use_define_for_class_fields: Handle<JsValue> =
        options.get(&mut cx, "tsUseDefineForClassFields")?;
      let ts_use_define_for_class_fields = if ts_use_define_for_class_fields
        .is_a::<JsUndefined, _>(&mut cx)
        || ts_use_define_for_class_fields.is_a::<JsNull, _>(&mut cx)
      {
        None
      } else if let Ok(value) = ts_use_define_for_class_fields.downcast::<JsBoolean, _>(&mut cx) {
        Some(value.value(&mut cx))
      } else {
        return cx.throw_type_error("options.tsUseDefineForClassFields must be a boolean");
      };

      (
        dialect_raw,
        ts_lower_class_fields,
        ts_use_define_for_class_fields,
      )
    } else {
      return cx.throw_type_error("options must be an object");
    }
  } else {
    (None, None, None)
  };

  let parsed_options = match parse_minify_options(
    dialect_raw.as_deref(),
    ts_lower_class_fields,
    ts_use_define_for_class_fields,
  ) {
    Ok(parsed) => parsed,
    Err(err) => return cx.throw_type_error(err),
  };

  let mut options =
    MinifyOptions::new(top_level_mode).with_ts_erase_options(parsed_options.ts_erase_options);
  if let Some(dialect) = parsed_options.dialect {
    options = options.with_dialect(dialect);
  }

  let mut out = Vec::new();
  match minify_js::minify_with_options(options, &source, &mut out) {
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

  #[test]
  fn parses_minify_options_defaults() {
    let parsed = parse_minify_options(None, None, None).unwrap();
    assert_eq!(parsed.dialect, None);
    assert!(!parsed.ts_erase_options.lower_class_fields);
    assert!(parsed.ts_erase_options.use_define_for_class_fields);
  }

  #[test]
  fn parses_minify_options_dialect() {
    let parsed = parse_minify_options(Some("auto"), None, None).unwrap();
    assert_eq!(parsed.dialect, None);

    let parsed = parse_minify_options(Some("js"), None, None).unwrap();
    assert_eq!(parsed.dialect, Some(Dialect::Js));

    let parsed = parse_minify_options(Some("tsx"), None, None).unwrap();
    assert_eq!(parsed.dialect, Some(Dialect::Tsx));
  }

  #[test]
  fn parses_minify_options_ts_erase_flags() {
    let parsed = parse_minify_options(None, Some(true), Some(false)).unwrap();
    assert!(parsed.ts_erase_options.lower_class_fields);
    assert!(!parsed.ts_erase_options.use_define_for_class_fields);
  }

  #[test]
  fn rejects_invalid_dialect() {
    assert!(parse_minify_options(Some("wat"), None, None).is_err());
  }
}
