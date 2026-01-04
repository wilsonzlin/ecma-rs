use axum::http::StatusCode;
use axum::routing::post;
use axum::Router;
use axum_msgpack::MsgPack;
use diagnostics::Diagnostic;
use optimize_js::cfg::cfg::Cfg;
use optimize_js::il::inst::{Arg, BinOp, Const, Inst, InstTyp, UnOp};
use optimize_js::{
  compile_source, ProgramFunction, ProgramScope, ProgramScopeKind, ProgramSymbols, TopLevelMode,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::PathBuf;
use std::str::FromStr;
use tower_http::cors::Any;
use tower_http::cors::CorsLayer;

#[derive(Clone, Serialize, Deserialize)]
pub struct PostCompileReq {
  pub source: String,
  pub is_global: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Hash)]
#[serde(rename_all = "snake_case", tag = "type", content = "value")]
pub enum StableId {
  Number(String),
  Text(String),
}

impl StableId {
  fn number<T: Into<u128>>(value: T) -> Self {
    StableId::Number(value.into().to_string())
  }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind", content = "value")]
pub enum StableConst {
  Null,
  Undefined,
  BigInt(String),
  Bool(bool),
  Num(f64),
  Str(String),
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum StableArg {
  Builtin { value: String },
  Const { value: StableConst },
  Fn { value: u64 },
  Var { value: u32 },
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StableInst {
  pub t: String,
  pub tgts: Vec<u32>,
  pub args: Vec<StableArg>,
  pub spreads: Vec<u32>,
  pub labels: Vec<u32>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub bin_op: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub un_op: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub foreign: Option<StableId>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub unknown: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StableDebugStep {
  pub name: String,
  #[serde(rename = "bblockOrder")]
  pub bblock_order: Vec<u32>,
  pub bblocks: BTreeMap<u32, Vec<StableInst>>,
  #[serde(rename = "cfgChildren")]
  pub cfg_children: BTreeMap<u32, Vec<u32>>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StableDebug {
  pub steps: Vec<StableDebugStep>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StableCfg {
  pub bblock_order: Vec<u32>,
  pub bblocks: BTreeMap<u32, Vec<StableInst>>,
  pub cfg_children: BTreeMap<u32, Vec<u32>>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StableFunction {
  pub debug: StableDebug,
  pub cfg: StableCfg,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StableProgramSymbol {
  pub id: StableId,
  pub name: String,
  pub scope: StableId,
  pub captured: bool,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StableFreeSymbols {
  pub top_level: Vec<StableId>,
  pub functions: Vec<Vec<StableId>>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StableScope {
  pub id: StableId,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub parent: Option<StableId>,
  pub kind: String,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub symbols: Vec<StableId>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub children: Vec<StableId>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub tdz_bindings: Vec<StableId>,
  pub is_dynamic: bool,
  pub has_direct_eval: bool,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StableProgramSymbols {
  pub symbols: Vec<StableProgramSymbol>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub free_symbols: Option<StableFreeSymbols>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub names: Vec<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub scopes: Vec<StableScope>,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct PostCompileRes {
  pub functions: Vec<StableFunction>,
  pub top_level: StableFunction,
  pub symbols: Option<StableProgramSymbols>,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct PostCompileErrorRes {
  pub ok: bool,
  pub diagnostics: Vec<Diagnostic>,
}

fn stable_const(value: &Const) -> StableConst {
  match value {
    Const::Null => StableConst::Null,
    Const::Undefined => StableConst::Undefined,
    Const::Bool(v) => StableConst::Bool(*v),
    Const::Num(num) => StableConst::Num(num.0),
    Const::Str(s) => StableConst::Str(s.clone()),
    Const::BigInt(v) => StableConst::BigInt(v.to_string()),
  }
}

fn stable_arg(arg: &Arg) -> StableArg {
  match arg {
    Arg::Builtin(path) => StableArg::Builtin {
      value: path.clone(),
    },
    Arg::Const(value) => StableArg::Const {
      value: stable_const(value),
    },
    Arg::Fn(idx) => StableArg::Fn { value: *idx as u64 },
    Arg::Var(id) => StableArg::Var { value: *id },
  }
}

fn stable_inst(inst: &Inst) -> StableInst {
  let bin_op = match inst.t {
    InstTyp::Bin if !matches!(inst.bin_op, BinOp::_Dummy) => Some(format!("{:?}", inst.bin_op)),
    _ => None,
  };
  let un_op = match inst.t {
    InstTyp::Un if !matches!(inst.un_op, UnOp::_Dummy) => Some(format!("{:?}", inst.un_op)),
    _ => None,
  };
  let foreign = match inst.t {
    InstTyp::ForeignLoad | InstTyp::ForeignStore => Some(StableId::number(inst.foreign.raw_id())),
    _ => None,
  };
  let unknown = match inst.t {
    InstTyp::UnknownLoad | InstTyp::UnknownStore if !inst.unknown.is_empty() => {
      Some(inst.unknown.clone())
    }
    _ => None,
  };

  StableInst {
    t: format!("{:?}", inst.t),
    tgts: inst.tgts.clone(),
    args: inst.args.iter().map(stable_arg).collect(),
    spreads: inst.spreads.iter().map(|s| *s as u32).collect(),
    labels: inst.labels.clone(),
    bin_op,
    un_op,
    foreign,
    unknown,
  }
}

fn stable_bblocks<'a, I>(blocks: I) -> BTreeMap<u32, Vec<StableInst>>
where
  I: IntoIterator<Item = (u32, &'a Vec<Inst>)>,
{
  blocks
    .into_iter()
    .map(|(label, insts)| {
      (
        label,
        insts.iter().map(stable_inst).collect::<Vec<StableInst>>(),
      )
    })
    .collect()
}

fn stable_cfg(cfg: &Cfg) -> StableCfg {
  StableCfg {
    bblock_order: cfg.graph.calculate_postorder(0).0,
    bblocks: stable_bblocks(cfg.bblocks.all()),
    cfg_children: cfg
      .graph
      .labels_sorted()
      .into_iter()
      .map(|label| (label, cfg.graph.children_sorted(label)))
      .collect(),
  }
}

fn stable_step(name: impl Into<String>, cfg: &Cfg) -> StableDebugStep {
  StableDebugStep {
    name: name.into(),
    bblock_order: cfg.graph.calculate_postorder(0).0,
    bblocks: stable_bblocks(cfg.bblocks.all()),
    cfg_children: cfg
      .graph
      .labels_sorted()
      .into_iter()
      .map(|label| (label, cfg.graph.children_sorted(label)))
      .collect(),
  }
}

fn stable_debug(
  debug: Option<&optimize_js::util::debug::OptimizerDebug>,
  cfg: &Cfg,
) -> StableDebug {
  let steps = if let Some(debug) = debug {
    debug
      .steps()
      .iter()
      .map(|step| StableDebugStep {
        name: step.name.clone(),
        bblock_order: step.bblock_order.clone(),
        bblocks: step
          .bblocks
          .iter()
          .map(|(label, insts)| (*label, insts.iter().map(stable_inst).collect()))
          .collect(),
        cfg_children: step.cfg_children.clone(),
      })
      .collect()
  } else {
    vec![stable_step("final", cfg)]
  };
  StableDebug { steps }
}

fn stable_function(func: &ProgramFunction) -> StableFunction {
  StableFunction {
    debug: stable_debug(func.debug.as_ref(), &func.body),
    cfg: stable_cfg(&func.body),
  }
}

fn scope_kind_string(kind: &ProgramScopeKind) -> &'static str {
  match kind {
    ProgramScopeKind::Global => "global",
    ProgramScopeKind::Module => "module",
    ProgramScopeKind::Class => "class",
    ProgramScopeKind::StaticBlock => "static_block",
    ProgramScopeKind::NonArrowFunction => "non_arrow_function",
    ProgramScopeKind::ArrowFunction => "arrow_function",
    ProgramScopeKind::Block => "block",
    ProgramScopeKind::FunctionExpressionName => "function_expression_name",
  }
}

fn stable_scope(scope: &ProgramScope) -> StableScope {
  StableScope {
    id: StableId::number(scope.id.raw_id()),
    parent: scope.parent.map(|p| StableId::number(p.raw_id())),
    kind: scope_kind_string(&scope.kind).to_string(),
    symbols: scope
      .symbols
      .iter()
      .map(|id| StableId::number(id.raw_id()))
      .collect(),
    children: scope
      .children
      .iter()
      .map(|id| StableId::number(id.raw_id()))
      .collect(),
    tdz_bindings: scope
      .tdz_bindings
      .iter()
      .map(|id| StableId::number(id.raw_id()))
      .collect(),
    is_dynamic: scope.is_dynamic,
    has_direct_eval: scope.has_direct_eval,
  }
}

fn stable_symbols(symbols: &ProgramSymbols) -> StableProgramSymbols {
  let mut stable = StableProgramSymbols {
    symbols: symbols
      .symbols
      .iter()
      .map(|symbol| StableProgramSymbol {
        id: StableId::number(symbol.id.raw_id()),
        name: symbol.name.clone(),
        scope: StableId::number(symbol.scope.raw_id()),
        captured: symbol.captured,
      })
      .collect(),
    free_symbols: symbols.free_symbols.as_ref().map(|free| StableFreeSymbols {
      top_level: free
        .top_level
        .iter()
        .map(|id| StableId::number(id.raw_id()))
        .collect(),
      functions: free
        .functions
        .iter()
        .map(|func| {
          func
            .iter()
            .map(|id| StableId::number(id.raw_id()))
            .collect()
        })
        .collect(),
    }),
    names: symbols.names.clone(),
    scopes: symbols.scopes.iter().map(stable_scope).collect(),
  };

  stable.symbols.sort_by(|a, b| {
    (
      &a.scope,
      &a.name,
      &a.id,
      a.captured.then_some(1usize).unwrap_or(0usize),
    )
      .cmp(&(
        &b.scope,
        &b.name,
        &b.id,
        b.captured.then_some(1usize).unwrap_or(0usize),
      ))
  });
  stable.scopes.sort_by(|a, b| a.id.cmp(&b.id));
  stable
}

fn build_response(program: optimize_js::Program) -> PostCompileRes {
  let functions = program.functions.iter().map(stable_function).collect();
  let top_level = stable_function(&program.top_level);
  let symbols = program.symbols.as_ref().map(stable_symbols);

  PostCompileRes {
    functions,
    top_level,
    symbols,
  }
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
    Ok(program) => Ok(MsgPack(build_response(program))),
    Err(diagnostics) => Err((
      StatusCode::BAD_REQUEST,
      MsgPack(PostCompileErrorRes {
        ok: false,
        diagnostics,
      }),
    )),
  }
}

fn build_app() -> Router {
  Router::new()
    .route("/compile", post(handle_post_compile))
    .layer(
      CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any),
    )
}

fn arg_value(args: &[String], flag: &str) -> Option<String> {
  let mut iter = args.iter();
  while let Some(arg) = iter.next() {
    if arg == flag {
      return iter.next().map(|v| v.to_string());
    }
    if let Some(value) = arg.strip_prefix(&(flag.to_owned() + "=")) {
      return Some(value.to_string());
    }
  }
  None
}

fn read_source(path: Option<PathBuf>) -> io::Result<String> {
  if let Some(path) = path {
    fs::read_to_string(path)
  } else {
    let mut src = String::new();
    io::stdin().read_to_string(&mut src)?;
    Ok(src)
  }
}

fn run_snapshot_mode(args: &[String]) -> Result<bool, Box<dyn std::error::Error>> {
  if !args.iter().any(|arg| arg == "--snapshot") {
    return Ok(false);
  }
  let input = arg_value(args, "--input").map(PathBuf::from);
  let output = arg_value(args, "--output").map(PathBuf::from);
  let mode = arg_value(args, "--mode")
    .and_then(|m| TopLevelMode::from_str(&m).ok())
    .unwrap_or(TopLevelMode::Module);

  let source = read_source(input)?;
  match compile_source(&source, mode, true) {
    Ok(program) => {
      let snapshot = build_response(program);
      let json = serde_json::to_string_pretty(&snapshot)?;
      if let Some(path) = output {
        fs::write(path, json)?;
      } else {
        println!("{json}");
      }
    }
    Err(diags) => {
      let json = serde_json::to_string_pretty(&PostCompileErrorRes {
        ok: false,
        diagnostics: diags,
      })?;
      let mut stderr = io::stderr();
      stderr.write_all(json.as_bytes())?;
      stderr.write_all(b"\n")?;
      std::process::exit(1);
    }
  }

  Ok(true)
}

#[tokio::main]
async fn main() {
  tracing_subscriber::fmt::init();

  let args: Vec<String> = env::args().skip(1).collect();
  if let Ok(true) = run_snapshot_mode(&args) {
    return;
  }

  let app = build_app();
  let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
  axum::serve(listener, app).await.unwrap();
}

#[cfg(test)]
mod tests {
  #![allow(dead_code, non_snake_case)]
  use super::*;
  use axum::body;
  use axum::body::Body;
  use axum::http::Request;
  use rmp_serde::{from_slice, to_vec};
  use tower::ServiceExt;

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
    assert!(
      !res.top_level.debug.steps.is_empty(),
      "debug steps should be present"
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

    assert_eq!(
      serde_json::to_string(&first).expect("serialize first symbols"),
      serde_json::to_string(&second).expect("serialize second symbols"),
      "symbol output should be deterministic"
    );
  }

  fn build_http_request(body: Vec<u8>) -> Request<Body> {
    Request::builder()
      .uri("/compile")
      .method("POST")
      .header("content-type", "application/msgpack")
      .body(Body::from(body))
      .unwrap()
  }

  #[tokio::test]
  async fn optimizer_output_matches_snapshot_fixture() {
    let app = build_app();
    let body = to_vec(&PostCompileReq {
      source: include_str!("../tests/fixtures/debug_input.js").to_string(),
      is_global: false,
    })
    .expect("serialize request");
    let response = app
      .oneshot(build_http_request(body))
      .await
      .expect("response");
    assert_eq!(response.status(), StatusCode::OK);
    let bytes = body::to_bytes(response.into_body(), usize::MAX)
      .await
      .expect("read body");
    let parsed: PostCompileRes = from_slice(&bytes).expect("decode msgpack body");
    let expected: PostCompileRes =
      serde_json::from_str(include_str!("../tests/fixtures/debug_input.snapshot.json"))
        .expect("parse snapshot");
    if std::env::var_os("UPDATE_SNAPSHOT").is_some() {
      std::fs::write(
        "tests/fixtures/debug_input.snapshot.json",
        serde_json::to_string_pretty(&parsed).expect("serialize snapshot"),
      )
      .expect("write snapshot");
    }
    assert_eq!(
      parsed, expected,
      "debugger response should match recorded snapshot"
    );
  }

  #[tokio::test]
  async fn snapshot_endpoint_is_deterministic_over_http() {
    let app = build_app();
    let req = PostCompileReq {
      source: "let a = 1; const b = a + 1; b;".to_string(),
      is_global: false,
    };
    let body = to_vec(&req).expect("serialize request");
    let first = app
      .clone()
      .oneshot(build_http_request(body.clone()))
      .await
      .expect("first response");
    let second = app
      .oneshot(build_http_request(body))
      .await
      .expect("second response");

    let first_parsed: PostCompileRes =
      from_slice(&body::to_bytes(first.into_body(), usize::MAX).await.unwrap()).unwrap();
    let second_parsed: PostCompileRes = from_slice(
      &body::to_bytes(second.into_body(), usize::MAX)
        .await
        .unwrap(),
    )
    .unwrap();
    assert_eq!(first_parsed, second_parsed);
  }
}
