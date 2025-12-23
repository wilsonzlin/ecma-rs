use axum::routing::post;
use axum::Router;
use axum_msgpack::MsgPack;
use optimize_js::Program;
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

pub async fn handle_post_compile(
  MsgPack(PostCompileReq { source, is_global }): MsgPack<PostCompileReq>,
) -> MsgPack<PostCompileRes> {
  let top_level_mode = if is_global {
    TopLevelMode::Global
  } else {
    TopLevelMode::Module
  };
  let Program {
    functions,
    top_level,
    symbols,
  } = optimize_js::compile_source(&source, top_level_mode, true).expect("compile input");
  MsgPack(PostCompileRes {
    functions,
    top_level,
    symbols,
  })
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
