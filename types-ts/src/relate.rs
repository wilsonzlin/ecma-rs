use crate::types::FunctionType;
use crate::types::IndexKind;
use crate::types::MemberVisibility;
use crate::types::ObjectType;
use crate::types::Property;
use crate::types::TypeId;
use crate::types::TypeKind;
use crate::types::TypeOptions;
use crate::types::TypeRefId;
use crate::types::TypeStore;
use bitflags::bitflags;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::time::Instant;
use tracing::debug_span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelationKind {
  Assignable,
  Comparable,
  StrictSubtype,
}

bitflags! {
  #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
  pub struct RelationMode: u8 {
    const NONE = 0;
    const BIVARIANT_PARAMS = 1 << 0;
  }
}

#[derive(Debug, Clone)]
pub struct RelationResult {
  pub result: bool,
  pub reason: Option<ReasonNode>,
}

#[derive(Debug, Clone)]
pub struct ReasonNode {
  pub src: TypeId,
  pub dst: TypeId,
  pub relation: RelationKind,
  pub outcome: bool,
  pub note: Option<String>,
  pub children: Vec<ReasonNode>,
}

pub struct RelateHooks<'a> {
  pub expander: Option<&'a dyn TypeExpander>,
  pub is_same_origin_private_member: Option<&'a dyn Fn(&Property, &Property) -> bool>,
}

impl<'a> Default for RelateHooks<'a> {
  fn default() -> Self {
    Self {
      expander: None,
      is_same_origin_private_member: None,
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RelationKey {
  src: TypeId,
  dst: TypeId,
  kind: RelationKind,
  mode: RelationMode,
}

struct RelationSpan {
  span: tracing::Span,
  start: Instant,
}

impl RelationSpan {
  fn enter(key: RelationKey, cache_hit: bool) -> Option<RelationSpan> {
    let span = debug_span!(
      "types_ts.relate",
      file = Option::<u32>::None,
      def = Option::<u32>::None,
      body = Option::<u32>::None,
      type_id = key.src.0,
      target_type_id = key.dst.0,
      relation = ?key.kind,
      cache_hit,
      duration_ms = tracing::field::Empty,
      outcome = tracing::field::Empty,
    );
    if span.is_disabled() {
      return None;
    }
    let _guard = span.enter();
    drop(_guard);
    Some(RelationSpan {
      span,
      start: Instant::now(),
    })
  }

  fn finish(self, outcome: bool) {
    self.span.record("outcome", outcome);
    self
      .span
      .record("duration_ms", self.start.elapsed().as_secs_f64() * 1000.0);
  }
}

pub trait TypeExpander {
  fn expand_ref(&self, store: &TypeStore, reference: TypeRefId) -> Option<TypeId>;
}

pub struct RelateCtx<'a> {
  store: &'a TypeStore,
  pub options: TypeOptions,
  hooks: RelateHooks<'a>,
  cache: RefCell<HashMap<RelationKey, bool>>,
  in_progress: RefCell<HashSet<RelationKey>>,
}

impl<'a> RelateCtx<'a> {
  pub fn new(store: &'a TypeStore, options: TypeOptions) -> Self {
    Self {
      store,
      options,
      hooks: RelateHooks::default(),
      cache: RefCell::new(HashMap::new()),
      in_progress: RefCell::new(HashSet::new()),
    }
  }

  pub fn with_hooks(store: &'a TypeStore, options: TypeOptions, hooks: RelateHooks<'a>) -> Self {
    Self {
      store,
      options,
      hooks,
      cache: RefCell::new(HashMap::new()),
      in_progress: RefCell::new(HashSet::new()),
    }
  }

  pub fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    self
      .relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::NONE,
        false,
      )
      .result
  }

  pub fn explain_assignable(&self, src: TypeId, dst: TypeId) -> RelationResult {
    self.relate_internal(src, dst, RelationKind::Assignable, RelationMode::NONE, true)
  }

  fn relate_internal(
    &self,
    src: TypeId,
    dst: TypeId,
    kind: RelationKind,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind,
      mode,
    };
    let cached = self.cache.borrow().get(&key).copied();
    let mut span = RelationSpan::enter(key, cached.is_some());
    if let Some(hit) = cached {
      if let Some(span) = span.take() {
        span.finish(hit);
      }
      return RelationResult {
        result: hit,
        reason: record.then(|| self.cached_reason(key, hit)),
      };
    }
    if self.in_progress.borrow().contains(&key) {
      if let Some(span) = span.take() {
        span.finish(true);
      }
      return RelationResult {
        result: true,
        reason: record.then(|| self.cycle_reason(key)),
      };
    }

    self.in_progress.borrow_mut().insert(key);

    let outcome = match kind {
      RelationKind::Assignable => self.assignable(src, dst, mode, record),
      RelationKind::Comparable => {
        let left = self.assignable(src, dst, mode, record);
        if !left.result {
          left
        } else {
          let right = self.assignable(dst, src, mode, record);
          RelationResult {
            result: right.result,
            reason: self.join_reasons(
              record,
              key,
              vec![left.reason, right.reason],
              right.result,
              None,
            ),
          }
        }
      }
      RelationKind::StrictSubtype => {
        let forward = self.assignable(src, dst, mode, record);
        if !forward.result {
          forward
        } else {
          let backward = self.assignable(dst, src, mode, record);
          let res = forward.result && !backward.result;
          RelationResult {
            result: res,
            reason: self.join_reasons(
              record,
              key,
              vec![forward.reason, backward.reason],
              res,
              Some("strict subtype".into()),
            ),
          }
        }
      }
    };

    self.cache.borrow_mut().insert(key, outcome.result);
    self.in_progress.borrow_mut().remove(&key);
    if let Some(span) = span.take() {
      span.finish(outcome.result);
    }
    outcome
  }

  fn cached_reason(&self, key: RelationKey, result: bool) -> ReasonNode {
    ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome: result,
      note: Some("cached".into()),
      children: Vec::new(),
    }
  }

  fn cycle_reason(&self, key: RelationKey) -> ReasonNode {
    ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome: true,
      note: Some("cycle".into()),
      children: Vec::new(),
    }
  }

  fn join_reasons(
    &self,
    record: bool,
    key: RelationKey,
    children: Vec<Option<ReasonNode>>,
    outcome: bool,
    note: Option<String>,
  ) -> Option<ReasonNode> {
    record.then(|| ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome,
      note,
      children: children.into_iter().flatten().collect(),
    })
  }

  fn assignable(
    &self,
    src: TypeId,
    dst: TypeId,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind: RelationKind::Assignable,
      mode,
    };

    let mut reason_children: Vec<RelationResult> = Vec::new();

    if src == dst {
      return RelationResult {
        result: true,
        reason: self.join_reasons(record, key, Vec::new(), true, Some("identical".into())),
      };
    }

    let src_kind = self.store.get(src).clone();
    let dst_kind = self.store.get(dst).clone();

    // fast paths for primitives
    if let Some(res) = self.assignable_special(&src_kind, &dst_kind) {
      return RelationResult {
        result: res,
        reason: self.join_reasons(record, key, Vec::new(), res, Some("special".into())),
      };
    }

    // expand references lazily
    if let TypeKind::Ref(r) = src_kind {
      if let Some(expanded) = self.expand_ref(r) {
        let related = self.relate_internal(expanded, dst, RelationKind::Assignable, mode, record);
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("expand src".into()),
          ),
        };
      }
    }
    if let TypeKind::Ref(r) = dst_kind {
      if let Some(expanded) = self.expand_ref(r) {
        let related = self.relate_internal(src, expanded, RelationKind::Assignable, mode, record);
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("expand dst".into()),
          ),
        };
      }
    }

    // unions
    if let TypeKind::Union(srcs) = &src_kind {
      for member in srcs {
        let related = self.relate_internal(*member, dst, RelationKind::Assignable, mode, record);
        if record {
          reason_children.push(related.clone());
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              reason_children.into_iter().map(|r| r.reason).collect(),
              false,
              Some("union source".into()),
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          reason_children.into_iter().map(|r| r.reason).collect(),
          true,
          Some("union source".into()),
        ),
      };
    }
    if let TypeKind::Union(dsts) = &dst_kind {
      let mut any_child: Vec<RelationResult> = Vec::new();
      for member in dsts {
        let related = self.relate_internal(src, *member, RelationKind::Assignable, mode, record);
        if record {
          any_child.push(related.clone());
        }
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              true,
              Some("union target".into()),
            ),
          };
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          any_child.into_iter().map(|r| r.reason).collect(),
          false,
          Some("union target".into()),
        ),
      };
    }

    // intersections
    if let TypeKind::Intersection(dsts) = &dst_kind {
      for member in dsts {
        let related = self.relate_internal(src, *member, RelationKind::Assignable, mode, record);
        if record {
          reason_children.push(related.clone());
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              reason_children.into_iter().map(|r| r.reason).collect(),
              false,
              Some("intersection target".into()),
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          reason_children.into_iter().map(|r| r.reason).collect(),
          true,
          Some("intersection target".into()),
        ),
      };
    }

    if let TypeKind::Intersection(srcs) = &src_kind {
      if let TypeKind::Object(dst_obj) = &dst_kind {
        if let Some(merged) = self.merge_intersection(srcs) {
          let related = self.relate_object(src, dst, &merged, dst_obj, mode, record);
          return RelationResult {
            result: related.result,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              related.result,
              Some("intersection merge".into()),
            ),
          };
        }
      }
      for member in srcs {
        let related = self.relate_internal(*member, dst, RelationKind::Assignable, mode, record);
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              true,
              Some("intersection source".into()),
            ),
          };
        }
        if record {
          reason_children.push(related.clone());
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          reason_children.into_iter().map(|r| r.reason).collect(),
          false,
          Some("intersection source".into()),
        ),
      };
    }

    match (&src_kind, &dst_kind) {
      (TypeKind::Literal(lit_a), TypeKind::Literal(lit_b)) => RelationResult {
        result: lit_a == lit_b,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          lit_a == lit_b,
          Some("literal".into()),
        ),
      },
      (TypeKind::Literal(lit), TypeKind::String) => match lit {
        crate::types::LiteralType::String(_) => RelationResult {
          result: true,
          reason: self.join_reasons(record, key, Vec::new(), true, Some("literal string".into())),
        },
        _ => RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            false,
            Some("literal mismatch".into()),
          ),
        },
      },
      (TypeKind::Literal(lit), TypeKind::Number) => match lit {
        crate::types::LiteralType::Number(_) => RelationResult {
          result: true,
          reason: self.join_reasons(record, key, Vec::new(), true, Some("literal number".into())),
        },
        _ => RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            false,
            Some("literal mismatch".into()),
          ),
        },
      },
      (TypeKind::Literal(crate::types::LiteralType::Boolean(_)), TypeKind::Boolean) => {
        RelationResult {
          result: true,
          reason: self.join_reasons(record, key, Vec::new(), true, Some("literal bool".into())),
        }
      }
      (TypeKind::Function(src_fn), TypeKind::Function(dst_fn)) => {
        let related = self.relate_function(src, dst, src_fn, dst_fn, mode, record);
        RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("function".into()),
          ),
        }
      }
      (TypeKind::Object(src_obj), TypeKind::Object(dst_obj)) => {
        self.relate_object(src, dst, src_obj, dst_obj, mode, record)
      }
      _ => RelationResult {
        result: false,
        reason: self.join_reasons(record, key, Vec::new(), false, Some("structural".into())),
      },
    }
  }

  fn merge_intersection(&self, members: &[TypeId]) -> Option<ObjectType> {
    let mut merged_props: Vec<Property> = Vec::new();
    let mut merged_indexes: Vec<crate::types::IndexSignature> = Vec::new();
    for member in members {
      match self.store.get(*member) {
        TypeKind::Object(obj) => {
          for prop in &obj.properties {
            if !merged_props.iter().any(|p| p.name == prop.name) {
              merged_props.push(prop.clone());
            }
          }
          for idx in &obj.index_signatures {
            if !merged_indexes.iter().any(|p| p.kind == idx.kind) {
              merged_indexes.push(idx.clone());
            }
          }
        }
        _ => return None,
      }
    }
    Some(ObjectType::new(merged_props, merged_indexes))
  }

  fn assignable_special(&self, src: &TypeKind, dst: &TypeKind) -> Option<bool> {
    let opts = &self.options;
    match (src, dst) {
      (TypeKind::Any, _) | (_, TypeKind::Any) => Some(true),
      (TypeKind::Unknown, TypeKind::Unknown) => Some(true),
      (_, TypeKind::Unknown) => Some(true),
      (TypeKind::Unknown, _) => Some(false),
      (TypeKind::Never, _) => Some(true),
      (_, TypeKind::Never) => Some(matches!(src, TypeKind::Never)),
      (TypeKind::Null, _)
      | (TypeKind::Undefined, _)
      | (_, TypeKind::Null)
      | (_, TypeKind::Undefined) => {
        if !opts.strict_null_checks {
          Some(true)
        } else {
          match (src, dst) {
            (TypeKind::Null, TypeKind::Null) => Some(true),
            (TypeKind::Undefined, TypeKind::Undefined) => Some(true),
            (TypeKind::Null, TypeKind::Any | TypeKind::Unknown) => Some(true),
            (TypeKind::Undefined, TypeKind::Any | TypeKind::Unknown) => Some(true),
            _ => Some(false),
          }
        }
      }
      _ => None,
    }
  }

  fn relate_object(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src: &ObjectType,
    dst: &ObjectType,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children: Vec<Option<ReasonNode>> = Vec::new();

    for dst_prop in &dst.properties {
      match src.find_property(&dst_prop.name) {
        Some(src_prop) => {
          if !self.private_compatible(src_prop, dst_prop) {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some(format!("private/protected {}", dst_prop.name)),
              ),
            };
          }

          if dst_prop.optional && !src_prop.optional {
            // required in source is acceptable, optional target fine
          }
          if !dst_prop.optional && src_prop.optional {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some(format!("missing required {}", dst_prop.name)),
              ),
            };
          }

          let next_mode = if src_prop.is_method || dst_prop.is_method {
            mode | RelationMode::BIVARIANT_PARAMS
          } else {
            mode
          };
          let related = self.relate_internal(
            src_prop.ty,
            dst_prop.ty,
            RelationKind::Assignable,
            next_mode,
            record,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some(format!("property {}", dst_prop.name)),
              ),
            };
          }
        }
        None => {
          if dst_prop.optional {
            continue;
          }
          if let Some(index) = self.index_for_prop(src, &dst_prop.name) {
            let related = self.relate_internal(
              index.ty,
              dst_prop.ty,
              RelationKind::Assignable,
              mode,
              record,
            );
            if record {
              children.push(related.reason);
            }
            if !related.result {
              return RelationResult {
                result: false,
                reason: self.join_reasons(
                  record,
                  key,
                  children,
                  false,
                  Some(format!("index {}", dst_prop.name)),
                ),
              };
            }
          } else {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some(format!("missing property {}", dst_prop.name)),
              ),
            };
          }
        }
      }
    }

    for dst_index in &dst.index_signatures {
      let source_index = src
        .index_signatures
        .iter()
        .find(|s| s.kind == dst_index.kind);
      if let Some(src_idx) = source_index {
        let related = self.relate_internal(
          src_idx.ty,
          dst_index.ty,
          RelationKind::Assignable,
          mode,
          record,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(record, key, children, false, Some("index signature".into())),
          };
        }
      } else {
        // ensure all properties compatible with target index
        for prop in &src.properties {
          if dst_index.kind == IndexKind::Number && prop.name.parse::<f64>().is_err() {
            continue;
          }
          let related = self.relate_internal(
            prop.ty,
            dst_index.ty,
            RelationKind::Assignable,
            mode,
            record,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("property vs index".into()),
              ),
            };
          }
        }
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("object".into())),
    }
  }

  fn private_compatible(&self, src: &Property, dst: &Property) -> bool {
    use MemberVisibility::Public;
    match (src.visibility, dst.visibility) {
      (Public, Public) => true,
      (Public, _) | (_, Public) => false,
      _ => self
        .hooks
        .is_same_origin_private_member
        .map(|cb| cb(src, dst))
        .unwrap_or(false),
    }
  }

  fn index_for_prop<'b>(
    &self,
    obj: &'b ObjectType,
    name: &str,
  ) -> Option<&'b crate::types::IndexSignature> {
    let numeric = name.parse::<f64>().is_ok();
    obj
      .index_signatures
      .iter()
      .find(|idx| idx.kind == IndexKind::String || (numeric && idx.kind == IndexKind::Number))
  }

  fn relate_function(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src: &FunctionType,
    dst: &FunctionType,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children: Vec<Option<ReasonNode>> = Vec::new();
    let allow_bivariance = !self.options.strict_function_types
      || src.is_method
      || dst.is_method
      || mode.contains(RelationMode::BIVARIANT_PARAMS);

    if let Some(dst_this) = dst.this_param {
      let src_this = src.this_param.unwrap_or_else(|| self.store.any());
      let this_related = if allow_bivariance {
        let forward =
          self.relate_internal(src_this, dst_this, RelationKind::Assignable, mode, record);
        if forward.result {
          forward
        } else {
          self.relate_internal(dst_this, src_this, RelationKind::Assignable, mode, record)
        }
      } else {
        self.relate_internal(dst_this, src_this, RelationKind::Assignable, mode, record)
      };

      if record {
        children.push(this_related.reason);
      }

      if !this_related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("this".into())),
        };
      }
    }

    let src_required = src.required_params();
    let dst_required = dst.required_params();
    if src_required > dst_required {
      return RelationResult {
        result: false,
        reason: self.join_reasons(record, key, children, false, Some("parameter count".into())),
      };
    }

    let paired = src.params.iter().zip(dst.params.iter());
    for (s_param, d_param) in paired {
      let related = if allow_bivariance {
        let forward = self.relate_internal(
          s_param.ty,
          d_param.ty,
          RelationKind::Assignable,
          mode,
          record,
        );
        if forward.result {
          forward
        } else {
          self.relate_internal(
            d_param.ty,
            s_param.ty,
            RelationKind::Assignable,
            mode,
            record,
          )
        }
      } else {
        self.relate_internal(
          d_param.ty,
          s_param.ty,
          RelationKind::Assignable,
          mode,
          record,
        )
      };

      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("parameter".into())),
        };
      }
    }

    // handle extra dst params using src rest parameter if present
    if dst.params.len() > src.params.len() {
      if let Some(rest) = src.params.iter().find(|p| p.rest) {
        for extra in dst.params.iter().skip(src.params.len()) {
          let related = if allow_bivariance {
            let forward =
              self.relate_internal(rest.ty, extra.ty, RelationKind::Assignable, mode, record);
            if forward.result {
              forward
            } else {
              self.relate_internal(extra.ty, rest.ty, RelationKind::Assignable, mode, record)
            }
          } else {
            self.relate_internal(extra.ty, rest.ty, RelationKind::Assignable, mode, record)
          };
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(record, key, children, false, Some("rest".into())),
            };
          }
        }
      }
    }

    let ret_related =
      self.relate_internal(src.ret, dst.ret, RelationKind::Assignable, mode, record);
    if record {
      children.push(ret_related.reason);
    }
    if !ret_related.result {
      return RelationResult {
        result: false,
        reason: self.join_reasons(record, key, children, false, Some("return".into())),
      };
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("function".into())),
    }
  }

  fn expand_ref(&self, reference: TypeRefId) -> Option<TypeId> {
    self
      .hooks
      .expander
      .and_then(|expander| expander.expand_ref(self.store, reference))
  }
}
