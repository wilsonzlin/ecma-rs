use axum::routing::post;
use axum::Json;
use axum::Router;
use axum_msgpack::MsgPack;
use optimize_js::Program;
use optimize_js::ProgramFunction;
use parse_js::parse;
use serde::Deserialize;
use serde::Serialize;
use symbol_js::compute_symbols;
use symbol_js::TopLevelMode;
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
}

pub async fn handle_post_compile(
  MsgPack(PostCompileReq { source, is_global }): MsgPack<PostCompileReq>,
) -> MsgPack<PostCompileRes> {
  let top_level_mode = if is_global {
    TopLevelMode::Global
  } else {
    TopLevelMode::Module
  };
  let mut top_level_node = parse(source.as_bytes()).expect("parse input");
  compute_symbols(&mut top_level_node, top_level_mode);
  let Program {
    functions,
    top_level,
  } = Program::compile(top_level_node, true);
  MsgPack(PostCompileRes {
    functions,
    top_level,
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
        .allow_headers(Any)
    );

  let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
  axum::serve(listener, app).await.unwrap();
}
