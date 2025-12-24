use axum::http::StatusCode;
use axum::routing::post;
use axum::Router;
use axum_msgpack::MsgPack;
use diagnostics::Diagnostic;
use optimize_js::compile_source;
use optimize_js::ProgramFunction;
use optimize_js::ProgramSymbols;
use optimize_js::TopLevelMode;
use serde::Deserialize;
use serde::Serialize;
use tower_http::cors::Any;
use tower_http::cors::CorsLayer;

#[derive(Deserialize)]
pub struct PostCompileReq {
  pub source: String,
  pub is_global: bool,
}

#[derive(Serialize)]
pub struct PostCompileRes {
  pub functions: Vec<ProgramFunction>,
  pub top_level: ProgramFunction,
  pub symbols: Option<ProgramSymbols>,
}

#[derive(Serialize)]
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
      symbols: program.symbols,
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
