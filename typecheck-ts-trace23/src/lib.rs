pub use crate::tracing::ProfileEvent;
pub use crate::tracing::Profiler;
use ::tracing::instrument;
use hir_js_trace23::lower_to_hir;
use hir_js_trace23::BodyId;
use semantic_js::bind_file;
use semantic_js::BoundFile;
use serde::Deserialize;
use serde::Serialize;
use std::time::Instant;
use types_ts_trace23::CacheReport;
use types_ts_trace23::RelateContext;
use types_ts_trace23::RelationCache;
use types_ts_trace23::TypeKind;
use types_ts_trace23::TypeStore;

mod tracing;

#[derive(Debug, Clone)]
pub struct InputFile {
  pub path: String,
  pub text: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Profile {
  pub events: Vec<ProfileEvent>,
  pub caches: CacheReport,
}

pub struct Typechecker {
  store: TypeStore,
  relations: RelationCache,
}

impl Typechecker {
  pub fn new() -> Self {
    Self {
      store: TypeStore::new(),
      relations: RelationCache::new(),
    }
  }

  /// Run the pipeline for a set of input files.
  pub fn check_files(&mut self, inputs: &[InputFile], profiler: &mut Profiler) {
    for input in inputs {
      let parsed = profiler.record("parse_file", Some(&input.path), None, || input.text.clone());
      let hir = profiler.record("hir_lower", Some(&input.path), None, || {
        lower_to_hir(&input.path, &parsed)
      });
      let bound = profiler.record("bind_file", Some(&input.path), None, || bind_file(&hir));
      self.profile_check_file(&bound, &parsed, profiler);
    }
  }

  fn profile_check_file(&mut self, bound: &BoundFile, source: &str, profiler: &mut Profiler) {
    let start = Instant::now();
    for body in &bound.bodies {
      let label = format!("{}", body.0);
      profiler.record(
        "check_body",
        Some(&bound.path),
        Some(label.as_str()),
        || self.check_body(bound, *body, source),
      );
    }
    let duration = start.elapsed();
    profiler.push_event("check_file", Some(&bound.path), None, duration);
  }

  #[instrument(level = "info", skip(self, source), fields(file = %bound.path, body = body.0))]
  fn check_body(&mut self, bound: &BoundFile, body: BodyId, source: &str) {
    // Touch the source so the compiler doesn't optimize it away completely.
    let _source_len = source.len();

    // Exercise the type store.
    let number = self.store.intern(TypeKind::Number);
    let string = self.store.intern(TypeKind::String);
    let boolean = self.store.intern(TypeKind::Boolean);
    let _number_again = self.store.intern(TypeKind::Number);

    // Instantiation cache: the second call should be a hit.
    let instantiated = self.store.instantiate(number, &[string]);
    let _instantiated_again = self.store.instantiate(number, &[string]);

    // Relation cache: the repeated calls should surface hits/misses.
    let mut relate = RelateContext::new(&self.store, &mut self.relations);
    let _ = relate.assignable(number, instantiated);
    let _ = relate.assignable(number, instantiated);
    let _ = relate.assignable(number, string);
    let _ = relate.assignable(string, number);
    let _ = relate.evaluate_conditional(boolean, boolean, number, string);

    ::tracing::debug!(
        target: "typecheck_ts::check_body",
        file = %bound.path,
        body = body.0,
        types_seen = 4,
        "finished check_body"
    );
  }

  pub fn into_profile(self, profiler: Profiler) -> Profile {
    Profile {
      events: profiler.finish(),
      caches: CacheReport::new(&self.store, &self.relations),
    }
  }
}
