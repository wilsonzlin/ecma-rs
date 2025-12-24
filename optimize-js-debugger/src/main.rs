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
use std::fmt;
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
  fn from_debug(value: impl fmt::Debug) -> Self {
    let text = format!("{value:?}");
    let digits: String = text
      .chars()
      .skip_while(|c| !c.is_ascii_digit())
      .take_while(|c| c.is_ascii_digit())
      .collect();
    let repr = digits
      .parse::<u64>()
      .map(IdRepr::Num)
      .unwrap_or_else(|_| IdRepr::Text(text));
    Self { repr }
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
}

impl From<optimize_js::ProgramSymbols> for SerializableProgramSymbols {
  fn from(program: optimize_js::ProgramSymbols) -> Self {
    let optimize_js::ProgramSymbols {
      mut symbols,
      free_symbols,
    } = program;

    let mut symbols: Vec<_> = symbols
      .drain(..)
      .map(|symbol| SerializableProgramSymbol {
        id: SerializableId::from_debug(symbol.id),
        name: symbol.name,
        scope: SerializableId::from_debug(symbol.scope),
        captured: symbol.captured,
      })
      .collect();
    symbols.sort_by(|a, b| {
      (&a.scope, &a.name, &a.id, &a.captured).cmp(&(&b.scope, &b.name, &b.id, &b.captured))
    });

    let free_symbols = free_symbols.map(|free| {
      let mut top_level: Vec<_> = free
        .top_level
        .into_iter()
        .map(SerializableId::from_debug)
        .collect();
      top_level.sort();

      let functions: Vec<_> = free
        .functions
        .into_iter()
        .map(|func| {
          let mut mapped: Vec<_> = func.into_iter().map(SerializableId::from_debug).collect();
          mapped.sort();
          mapped
        })
        .collect();

      SerializableProgramFreeSymbols {
        top_level,
        functions,
      }
    });

    SerializableProgramSymbols {
      symbols,
      free_symbols,
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
  use super::*;
  use serde_json::to_string;

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
}
