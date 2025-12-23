use crate::check::BodyCheckResult;
use crate::ids::BodyId;
use crate::types::TypeStore;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::error::SyntaxResult;
use parse_js::loc::Loc;
use std::sync::Arc;

pub struct Body {
  pub id: BodyId,
  pub kind: BodyKind,
  pub source: Arc<str>,
  pub expr_spans: Vec<Loc>,
  pub pat_spans: Vec<Loc>,
}

pub enum BodyKind {
  TopLevel(Vec<Node<Stmt>>),
}

pub struct TypeDatabase {
  pub type_store: TypeStore,
  pub(crate) bodies: Vec<Body>,
  pub(crate) results: Vec<Option<Arc<BodyCheckResult>>>,
}

impl TypeDatabase {
  pub fn new() -> Self {
    Self {
      type_store: TypeStore::new(),
      bodies: Vec::new(),
      results: Vec::new(),
    }
  }

  pub fn add_body_from_source(&mut self, source: &str) -> SyntaxResult<BodyId> {
    let parsed = parse_js::parse(source)?;
    self.add_parsed_body(parsed, Arc::from(source.to_string()))
  }

  pub fn add_parsed_body(
    &mut self,
    top_level: Node<TopLevel>,
    source: Arc<str>,
  ) -> SyntaxResult<BodyId> {
    let body_id = BodyId(self.bodies.len());
    let body = Body {
      id: body_id,
      kind: BodyKind::TopLevel(top_level.stx.body),
      source,
      expr_spans: Vec::new(),
      pat_spans: Vec::new(),
    };
    self.bodies.push(body);
    self.results.push(None);
    Ok(body_id)
  }

  pub fn body(&self, id: BodyId) -> Option<&Body> {
    self.bodies.get(id.index())
  }

  pub fn body_result(&self, id: BodyId) -> Option<&Arc<BodyCheckResult>> {
    self.results.get(id.index()).and_then(|r| r.as_ref())
  }
}
