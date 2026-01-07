use diagnostics::FileId;
use hir_js::{lower_file, Body, BodyId, DefKind, FileKind, LowerResult, NameInterner, PatId};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::ts::locals::{bind_ts_locals, TsLocalSemantics};
use typecheck_ts::check::flow_bindings::{FlowBindingId, FlowBindings};

#[allow(dead_code)]
pub struct Parsed {
  pub ast: Node<TopLevel>,
  pub semantics: TsLocalSemantics,
  pub lowered: LowerResult,
}

pub fn parse_lower_with_locals(source: &str) -> Parsed {
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let semantics = bind_ts_locals(&mut ast, FileId(0));
  let lowered = lower_file(FileId(0), FileKind::Ts, &ast);
  Parsed {
    ast,
    semantics,
    lowered,
  }
}

pub fn body_of<'a>(
  lowered: &'a LowerResult,
  names: &NameInterner,
  func: &str,
) -> (BodyId, &'a Body) {
  let def = lowered
    .defs
    .iter()
    .find(|d| names.resolve(d.name) == Some(func) && d.path.kind == DefKind::Function)
    .unwrap_or_else(|| panic!("missing function {func}"));
  let body_id = def.body.expect("function body");
  (body_id, lowered.body(body_id).unwrap())
}

pub fn binding_for_name(
  body: &Body,
  bindings: &FlowBindings,
  semantics: &TsLocalSemantics,
  target: &str,
) -> Option<FlowBindingId> {
  for (idx, expr) in body.exprs.iter().enumerate() {
    if !matches!(expr.kind, hir_js::ExprKind::Ident(_)) {
      continue;
    }
    let binding = match bindings.binding_for_expr(hir_js::ExprId(idx as u32)) {
      Some(binding) => binding,
      None => continue,
    };
    let symbol = semantics.symbol(binding);
    if semantics.names.get(&symbol.name).map(|n| n.as_str()) == Some(target) {
      return Some(binding);
    }
  }
  None
}

pub fn binding_for_pat(
  body: &Body,
  semantics: &TsLocalSemantics,
  pat: PatId,
) -> Option<FlowBindingId> {
  let span = body.pats.get(pat.0 as usize)?.span;
  semantics.resolve_expr_span(span)
}
