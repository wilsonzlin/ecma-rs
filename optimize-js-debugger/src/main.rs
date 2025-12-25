use axum::http::StatusCode;
use axum::routing::post;
use axum::Router;
use axum_msgpack::MsgPack;
use diagnostics::Diagnostic;
use optimize_js::compile_source;
use optimize_js::ProgramFunction;
use optimize_js::TopLevelMode;
use serde::Deserialize;
use serde::Serialize;
use serde_json::Value;
use tower_http::cors::Any;
use tower_http::cors::CorsLayer;

#[derive(Clone, Deserialize)]
pub struct PostCompileReq {
  pub source: String,
  pub is_global: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum IdRepr {
  Num(u64),
  Text(String),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SerializableId {
  repr: IdRepr,
}

impl SerializableId {
  fn from_u64(value: u64) -> Self {
    Self {
      repr: IdRepr::Num(value),
    }
  }

  fn from_value(value: &Value) -> Option<Self> {
    match value {
      Value::Number(num) => num.as_u64().map(Self::from_u64),
      Value::String(text) => Some(Self {
        repr: IdRepr::Text(text.clone()),
      }),
      Value::Bool(boolean) => Some(Self {
        repr: IdRepr::Text(boolean.to_string()),
      }),
      _ => None,
    }
  }

  fn display(&self) -> String {
    match &self.repr {
      IdRepr::Num(n) => n.to_string(),
      IdRepr::Text(text) => text.clone(),
    }
  }
}

impl Serialize for SerializableId {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    match &self.repr {
      IdRepr::Num(n) => serializer.serialize_u64(*n),
      IdRepr::Text(text) => serializer.serialize_str(text),
    }
  }
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SerializableProgramSymbol {
  pub id: SerializableId,
  pub name: String,
  pub scope: SerializableId,
  pub captured: bool,
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SerializableProgramFreeSymbols {
  pub top_level: Vec<SerializableId>,
  pub functions: Vec<Vec<SerializableId>>, // Index aligned with Program::functions.
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub struct SerializableProgramSymbols {
  pub symbols: Vec<SerializableProgramSymbol>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub free_symbols: Option<SerializableProgramFreeSymbols>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub names: Vec<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub scopes: Vec<SerializableScope>,
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SerializableScope {
  pub id: SerializableId,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub parent: Option<SerializableId>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub kind: Option<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub symbols: Vec<SerializableId>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub children: Vec<SerializableId>,
}

impl From<optimize_js::ProgramSymbols> for SerializableProgramSymbols {
  fn from(program: optimize_js::ProgramSymbols) -> Self {
    // We intentionally go through serde_json::Value so that changes to the optimizer-side
    // ProgramSymbols shape (e.g. semantic-js identifiers) can be normalized here without
    // coupling to concrete fields.
    let Ok(raw) = serde_json::to_value(program) else {
      return SerializableProgramSymbols {
        symbols: Vec::new(),
        free_symbols: None,
        names: Vec::new(),
        scopes: Vec::new(),
      };
    };
    SerializableProgramSymbols::from_value(raw)
  }
}

impl SerializableProgramSymbols {
  fn id_from_value_with_fallback(
    value: Option<&Value>,
    fallback: SerializableId,
  ) -> SerializableId {
    value
      .and_then(SerializableId::from_value)
      .unwrap_or(fallback)
  }

  fn parse_name(name: Option<&Value>, names: &[String]) -> Option<String> {
    let Some(name) = name else {
      return None;
    };
    match name {
      Value::String(text) => Some(text.clone()),
      Value::Number(num) => num
        .as_u64()
        .and_then(|idx| names.get(idx as usize).cloned()),
      _ => None,
    }
  }

  fn parse_symbol(symbol: &Value, idx: usize, names: &[String]) -> SerializableProgramSymbol {
    let fallback_id = SerializableId::from_u64(idx as u64);
    let default_scope = SerializableId::from_u64(0);
    let obj = symbol.as_object();
    let id = match obj
      .and_then(|o| o.get("id"))
      .or_else(|| obj.and_then(|o| o.get("symbol_id")))
      .or_else(|| obj.and_then(|o| o.get("symbolId")))
    {
      Some(value) => Self::id_from_value_with_fallback(Some(value), fallback_id.clone()),
      None => SerializableId::from_value(symbol).unwrap_or(fallback_id.clone()),
    };

    let scope = Self::id_from_value_with_fallback(
      obj
        .and_then(|o| o.get("scope"))
        .or_else(|| obj.and_then(|o| o.get("decl_scope")))
        .or_else(|| obj.and_then(|o| o.get("declScope"))),
      default_scope,
    );

    let name = Self::parse_name(obj.and_then(|o| o.get("name")), names)
      .or_else(|| {
        Self::parse_name(
          obj
            .and_then(|o| o.get("name_id"))
            .or_else(|| obj.and_then(|o| o.get("nameId"))),
          names,
        )
      })
      .unwrap_or_else(|| id.display());

    let captured = obj
      .and_then(|o| o.get("captured"))
      .and_then(Value::as_bool)
      .unwrap_or(false);

    SerializableProgramSymbol {
      id,
      name,
      scope,
      captured,
    }
  }

  fn parse_ids_array(value: &Value) -> Vec<SerializableId> {
    value
      .as_array()
      .map(|arr| {
        let mut out: Vec<_> = arr
          .iter()
          .enumerate()
          .map(|(idx, val)| {
            SerializableId::from_value(val).unwrap_or_else(|| SerializableId::from_u64(idx as u64))
          })
          .collect();
        out.sort();
        out
      })
      .unwrap_or_default()
  }

  fn parse_free_symbols(raw: &Value) -> Option<SerializableProgramFreeSymbols> {
    let free_symbols = raw
      .get("free_symbols")
      .or_else(|| raw.get("freeSymbols"))
      .and_then(Value::as_object)?;
    let top_level = free_symbols
      .get("top_level")
      .or_else(|| free_symbols.get("topLevel"))
      .map(Self::parse_ids_array)
      .unwrap_or_default();
    let functions: Vec<Vec<SerializableId>> = free_symbols
      .get("functions")
      .and_then(Value::as_array)
      .map(|arr| arr.iter().map(Self::parse_ids_array).collect())
      .unwrap_or_default();

    if top_level.is_empty() && functions.iter().all(|f| f.is_empty()) {
      None
    } else {
      Some(SerializableProgramFreeSymbols {
        top_level,
        functions,
      })
    }
  }

  fn find_names(raw: &Value) -> Vec<String> {
    let names_from = |container: &Value| -> Vec<String> {
      container
        .as_array()
        .map(|arr| {
          arr
            .iter()
            .filter_map(|v| v.as_str().map(str::to_string))
            .collect()
        })
        .unwrap_or_default()
    };
    raw
      .get("names")
      .map(names_from)
      .or_else(|| {
        raw
          .get("semantics")
          .and_then(|s| s.get("names"))
          .map(names_from)
      })
      .unwrap_or_default()
  }

  fn parse_scopes(raw: &Value, _names: &[String]) -> Vec<SerializableScope> {
    let scopes_from = |value: &Value| -> Vec<SerializableScope> {
      value
        .as_array()
        .map(|arr| {
          arr
            .iter()
            .enumerate()
            .map(|(idx, scope)| {
              let obj = scope.as_object();
              let id = obj
                .and_then(|o| o.get("id"))
                .or_else(|| obj.and_then(|o| o.get("scope")))
                .map(|v| {
                  SerializableId::from_value(v)
                    .unwrap_or_else(|| SerializableId::from_u64(idx as u64))
                })
                .unwrap_or_else(|| SerializableId::from_u64(idx as u64));
              let parent = obj
                .and_then(|o| o.get("parent"))
                .and_then(SerializableId::from_value);
              let kind = obj
                .and_then(|o| o.get("kind"))
                .and_then(Value::as_str)
                .map(str::to_string)
                .or_else(|| {
                  obj
                    .and_then(|o| o.get("type"))
                    .and_then(Value::as_str)
                    .map(str::to_string)
                });
              let symbols = obj
                .and_then(|o| o.get("symbols"))
                .map(|v| {
                  if v.is_array() {
                    Self::parse_ids_array(v)
                  } else if let Some(map) = v.as_object() {
                    let mut ids: Vec<_> = map
                      .values()
                      .map(|val| {
                        SerializableId::from_value(val).unwrap_or_else(|| {
                          // Try the key as a name-id index if possible.
                          SerializableId::from_u64(0)
                        })
                      })
                      .collect();
                    ids.sort();
                    ids
                  } else {
                    Vec::new()
                  }
                })
                .unwrap_or_default();
              let children = obj
                .and_then(|o| o.get("children"))
                .map(Self::parse_ids_array)
                .unwrap_or_default();

              SerializableScope {
                id,
                parent,
                kind,
                symbols,
                children,
              }
            })
            .collect()
        })
        .unwrap_or_default()
    };

    raw
      .get("scopes")
      .map(|scopes| scopes_from(scopes))
      .or_else(|| {
        raw
          .get("semantics")
          .and_then(|s| s.get("scopes"))
          .map(scopes_from)
      })
      .unwrap_or_default()
  }

  fn from_value(raw: Value) -> Self {
    let names = Self::find_names(&raw);
    let mut symbols = raw
      .get("symbols")
      .or_else(|| raw.get("semantics").and_then(|s| s.get("symbols")))
      .and_then(Value::as_array)
      .map(|arr| {
        arr
          .iter()
          .enumerate()
          .map(|(idx, sym)| Self::parse_symbol(sym, idx, &names))
          .collect::<Vec<_>>()
      })
      .unwrap_or_default();
    symbols.sort_by(|a, b| {
      (&a.scope, &a.name, &a.id, &a.captured).cmp(&(&b.scope, &b.name, &b.id, &b.captured))
    });

    let free_symbols = Self::parse_free_symbols(&raw);
    let mut scopes = Self::parse_scopes(&raw, &names);
    scopes.sort_by(|a, b| a.id.cmp(&b.id));

    SerializableProgramSymbols {
      symbols,
      free_symbols,
      names,
      scopes,
    }
  }
}

#[derive(Debug, Serialize)]
pub struct PostCompileRes {
  pub functions: Vec<ProgramFunction>,
  pub top_level: ProgramFunction,
  pub symbols: Option<SerializableProgramSymbols>,
}

#[derive(Debug, Serialize)]
pub struct PostCompileErrorRes {
  pub ok: bool,
  pub diagnostics: Vec<Diagnostic>,
}

pub async fn handle_post_compile(
  MsgPack(PostCompileReq { source, is_global }): MsgPack<PostCompileReq>,
) -> Result<MsgPack<PostCompileRes>, (StatusCode, MsgPack<PostCompileErrorRes>)> {
  let top_level_mode = if is_global {
    TopLevelMode::Global
  } else {
    TopLevelMode::Module
  };
  match compile_source(&source, top_level_mode, true) {
    Ok(program) => Ok(MsgPack(PostCompileRes {
      functions: program.functions,
      top_level: program.top_level,
      symbols: program.symbols.map(SerializableProgramSymbols::from),
    })),
    Err(diagnostics) => Err((
      StatusCode::BAD_REQUEST,
      MsgPack(PostCompileErrorRes {
        ok: false,
        diagnostics,
      }),
    )),
  }
}

#[tokio::main]
async fn main() {
  tracing_subscriber::fmt::init();

  let app = Router::new()
    .route("/compile", post(handle_post_compile))
    .layer(
      CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any),
    );

  let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
  axum::serve(listener, app).await.unwrap();
}

#[cfg(test)]
mod tests {
  #![allow(dead_code, non_snake_case)]
  use super::*;
  use serde::Deserialize;
  use serde_json::{to_string, to_value, Value};
  use std::collections::BTreeMap;

  #[tokio::test]
  async fn handle_post_compile_succeeds() {
    let MsgPack(res) = handle_post_compile(MsgPack(PostCompileReq {
      source: "let x = 1; let y = x + 2; y;".to_string(),
      is_global: false,
    }))
    .await
    .expect("compile should succeed");

    assert!(
      res.symbols.is_some(),
      "symbols should be present for code with declarations"
    );
  }

  #[tokio::test]
  async fn symbols_output_is_deterministic() {
    let req = PostCompileReq {
      source: r#"
        let x = 1;
        {
          let y = x + 1;
          y + x;
        }
        let z = x + 3;
        z + x;
      "#
      .to_string(),
      is_global: false,
    };

    let MsgPack(first) = handle_post_compile(MsgPack(req.clone()))
      .await
      .expect("first compile");
    let MsgPack(second) = handle_post_compile(MsgPack(req))
      .await
      .expect("second compile");

    let first_symbols = first.symbols.expect("symbols in first run");
    let second_symbols = second.symbols.expect("symbols in second run");

    assert_eq!(
      to_string(&first_symbols).expect("serialize first symbols"),
      to_string(&second_symbols).expect("serialize second symbols"),
      "symbol output should be deterministic"
    );
  }

  #[derive(Debug, Deserialize)]
  #[serde(untagged)]
  enum UiId {
    Num(u64),
    Text(String),
  }

  #[derive(Debug, Deserialize)]
  struct UiTextRange {
    start: u32,
    end: u32,
  }

  #[derive(Debug, Deserialize)]
  struct UiSpan {
    file: u32,
    range: UiTextRange,
  }

  #[derive(Debug, Deserialize)]
  struct UiArg {
    #[serde(default)]
    Builtin: Option<String>,
    #[serde(default)]
    Const: Option<Value>,
    #[serde(default)]
    Fn: Option<u64>,
    #[serde(default)]
    Var: Option<u64>,
  }

  #[derive(Debug, Deserialize)]
  struct UiInst {
    t: String,
    tgts: Vec<u32>,
    args: Vec<UiArg>,
    spreads: Vec<u32>,
    labels: Vec<u32>,
    #[serde(default)]
    bin_op: Option<String>,
    #[serde(default)]
    un_op: Option<String>,
    #[serde(default)]
    foreign: Option<UiId>,
    #[serde(default)]
    unknown: Option<String>,
    #[serde(default)]
    span: Option<UiSpan>,
  }

  #[derive(Debug, Deserialize)]
  #[serde(rename_all = "camelCase")]
  struct UiDebugStep {
    name: String,
    bblock_order: Vec<u32>,
    bblocks: BTreeMap<String, Vec<UiInst>>,
    cfg_children: BTreeMap<String, Vec<u32>>,
  }

  #[derive(Debug, Deserialize)]
  struct UiDebug {
    steps: Vec<UiDebugStep>,
  }

  #[derive(Debug, Deserialize)]
  struct UiProgramFunction {
    debug: UiDebug,
    #[serde(default)]
    body: Value,
  }

  #[derive(Debug, Deserialize)]
  struct UiFreeSymbols {
    #[serde(default)]
    top_level: Vec<UiId>,
    #[serde(default)]
    functions: Vec<Vec<UiId>>,
  }

  #[derive(Debug, Deserialize)]
  struct UiScope {
    #[serde(default)]
    id: Option<UiId>,
    #[serde(default)]
    parent: Option<UiId>,
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    symbols: Option<Vec<UiId>>,
    #[serde(default)]
    children: Option<Vec<UiId>>,
  }

  #[derive(Debug, Deserialize)]
  struct UiProgramSymbol {
    id: UiId,
    #[serde(default)]
    name: Option<String>,
    #[serde(default, rename = "name_id")]
    name_id_snake: Option<UiId>,
    #[serde(default, rename = "nameId")]
    name_id_camel: Option<UiId>,
    #[serde(default)]
    scope: Option<UiId>,
    #[serde(default)]
    captured: Option<bool>,
  }

  #[derive(Debug, Deserialize)]
  struct UiProgramSymbols {
    symbols: Vec<UiProgramSymbol>,
    #[serde(default)]
    free_symbols: Option<UiFreeSymbols>,
    #[serde(default)]
    names: Option<Vec<String>>,
    #[serde(default)]
    scopes: Option<Vec<UiScope>>,
  }

  #[derive(Debug, Deserialize)]
  struct UiDebuggerResponse {
    functions: Vec<UiProgramFunction>,
    top_level: UiProgramFunction,
    #[serde(default)]
    symbols: Option<UiProgramSymbols>,
  }

  #[test]
  fn optimizer_output_matches_debugger_schema() {
    let program = compile_source(
      include_str!("../tests/fixtures/debug_input.js"),
      TopLevelMode::Module,
      true,
    )
    .expect("compile");

    let payload = PostCompileRes {
      functions: program.functions,
      top_level: program.top_level,
      symbols: program.symbols.map(SerializableProgramSymbols::from),
    };

    let value = to_value(payload).expect("serialize to JSON");
    let parsed: UiDebuggerResponse =
      serde_json::from_value(value).expect("optimizer output should match debugger schema");

    assert!(
      parsed.top_level.debug.steps.first().is_some(),
      "debug steps should be present"
    );
    if let Some(symbols) = parsed.symbols {
      assert!(!symbols.symbols.is_empty(), "symbols should be present");
    }
  }
}
