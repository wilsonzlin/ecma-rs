use crate::diagnostic::Diagnostic;
use crate::types::MappedModifier;
use crate::types::MappedType;
use crate::types::ObjectType;
use crate::types::Property;
use crate::types::TemplatePart;
use crate::types::TemplateType;
use crate::types::TypeId;
use crate::types::TypeKind;
use crate::types::TypeStore;
use std::collections::HashMap;
use std::collections::HashSet;

pub type Env = HashMap<TypeId, TypeId>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct EnvKey(Vec<(TypeId, TypeId)>);

impl EnvKey {
  fn from_env(env: &Env) -> Self {
    let mut pairs: Vec<(TypeId, TypeId)> = env.iter().map(|(k, v)| (*k, *v)).collect();
    pairs.sort_by_key(|(k, _)| k.0);
    EnvKey(pairs)
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CacheKey {
  ty: TypeId,
  env: EnvKey,
}

impl CacheKey {
  fn new(ty: TypeId, env: &Env) -> Self {
    CacheKey {
      ty,
      env: EnvKey::from_env(env),
    }
  }
}

pub struct Normalizer<'a> {
  store: &'a mut TypeStore,
  cache: HashMap<CacheKey, TypeId>,
  in_progress: HashSet<CacheKey>,
  assign_cache: HashMap<(TypeId, TypeId, EnvKey), bool>,
  diagnostics: Vec<Diagnostic>,
}

impl<'a> Normalizer<'a> {
  pub fn new(store: &'a mut TypeStore) -> Self {
    Self {
      store,
      cache: HashMap::new(),
      in_progress: HashSet::new(),
      assign_cache: HashMap::new(),
      diagnostics: Vec::new(),
    }
  }

  pub fn diagnostics(&self) -> &[Diagnostic] {
    &self.diagnostics
  }

  pub fn normalize(&mut self, ty: TypeId, env: &Env) -> TypeId {
    let key = CacheKey::new(ty, env);
    if let Some(result) = self.cache.get(&key) {
      return *result;
    }
    if !self.in_progress.insert(key.clone()) {
      self.diagnostics.push(
        Diagnostic::new("cycle detected while normalizing type").with_note("returning unknown"),
      );
      return self.store.unknown();
    }

    let kind = self.store.kind(ty).clone();
    let result = match kind {
      TypeKind::Any
      | TypeKind::Unknown
      | TypeKind::Never
      | TypeKind::Boolean
      | TypeKind::True
      | TypeKind::False
      | TypeKind::Number
      | TypeKind::String
      | TypeKind::LiteralString(_)
      | TypeKind::LiteralNumber(_) => ty,

      TypeKind::TypeParam { .. } => env
        .get(&ty)
        .copied()
        .map(|t| self.normalize(t, env))
        .unwrap_or(ty),

      TypeKind::Union(members) => {
        let mut normed = Vec::new();
        for m in members.into_iter() {
          normed.push(self.normalize(m, env));
        }
        self.store.union(normed)
      }

      TypeKind::Intersection(members) => {
        let mut normed = Vec::new();
        for m in members.into_iter() {
          normed.push(self.normalize(m, env));
        }
        self.store.intersection(normed)
      }

      TypeKind::Object(_) => ty,

      TypeKind::Conditional {
        check_type,
        extends_type,
        true_type,
        false_type,
        check_param,
      } => self.normalize_conditional(
        check_type,
        extends_type,
        true_type,
        false_type,
        check_param,
        env,
      ),

      TypeKind::IndexedAccess { object, index } => {
        self.normalize_indexed_access(object, index, env)
      }

      TypeKind::KeyOf(inner) => self.normalize_keyof(inner, env),

      TypeKind::Mapped(mapped) => self.normalize_mapped(&mapped, env),

      TypeKind::Template(tpl) => self.normalize_template(&tpl, env),
    };

    self.in_progress.remove(&key);
    self.cache.insert(key, result);
    result
  }

  fn normalize_conditional(
    &mut self,
    check_type: TypeId,
    extends_type: TypeId,
    true_type: TypeId,
    false_type: TypeId,
    check_param: Option<TypeId>,
    env: &Env,
  ) -> TypeId {
    let check_norm = self.normalize(check_type, env);

    if let Some(param) = check_param {
      if let TypeKind::Union(members) = self.store.kind(check_norm).clone() {
        let mut results = Vec::new();
        for member in members.into_iter() {
          let mut new_env = env.clone();
          new_env.insert(param, member);
          let res =
            self.eval_conditional_basic(check_type, extends_type, true_type, false_type, &new_env);
          results.push(res);
        }
        return self.store.union(results);
      }
    }

    self.eval_conditional_basic(check_type, extends_type, true_type, false_type, env)
  }

  fn eval_conditional_basic(
    &mut self,
    check_type: TypeId,
    extends_type: TypeId,
    true_type: TypeId,
    false_type: TypeId,
    env: &Env,
  ) -> TypeId {
    let check_norm = self.normalize(check_type, env);
    let extends_norm = self.normalize(extends_type, env);
    if self.is_assignable(check_norm, extends_norm, env) {
      self.normalize(true_type, env)
    } else {
      self.normalize(false_type, env)
    }
  }

  fn normalize_indexed_access(&mut self, object: TypeId, index: TypeId, env: &Env) -> TypeId {
    let obj_norm = self.normalize(object, env);
    let index_norm = self.normalize(index, env);

    if let TypeKind::Union(keys) = self.store.kind(index_norm).clone() {
      let mut results = Vec::new();
      for key in keys.into_iter() {
        results.push(self.normalize_indexed_access(obj_norm, key, env));
      }
      return self.store.union(results);
    }

    match self.store.kind(obj_norm).clone() {
      TypeKind::Any => self.store.any(),
      TypeKind::Unknown => self.store.unknown(),
      TypeKind::Union(members) => {
        let mut parts = Vec::new();
        for m in members.into_iter() {
          parts.push(self.normalize_indexed_access(m, index_norm, env));
        }
        self.store.union(parts)
      }
      TypeKind::Intersection(members) => {
        let mut parts = Vec::new();
        for m in members.into_iter() {
          parts.push(self.normalize_indexed_access(m, index_norm, env));
        }
        self.store.intersection(parts)
      }
      TypeKind::Object(obj) => self.index_object(&obj, index_norm),
      _ => {
        self.diagnostics.push(
          Diagnostic::new("unsupported indexed access target").with_note("returning unknown"),
        );
        self.store.unknown()
      }
    }
  }

  fn index_object(&mut self, obj: &ObjectType, index: TypeId) -> TypeId {
    match self.store.kind(index).clone() {
      TypeKind::LiteralString(name) => obj
        .properties
        .get(&name)
        .map(|p| p.ty)
        .unwrap_or_else(|| self.store.unknown()),
      TypeKind::String => {
        let mut collected = Vec::new();
        for prop in obj.properties.values() {
          collected.push(prop.ty);
        }
        if collected.is_empty() {
          self.store.unknown()
        } else {
          self.store.union(collected)
        }
      }
      _ => self.store.unknown(),
    }
  }

  fn normalize_keyof(&mut self, target: TypeId, env: &Env) -> TypeId {
    let target_norm = self.normalize(target, env);
    match self.collect_keys(target_norm, env) {
      KeyResult::Any => {
        self.diagnostics.push(
          Diagnostic::new("keyof applied to a non-object or any-like type")
            .with_note("returning string as conservative result"),
        );
        self.store.string()
      }
      KeyResult::Never => self.store.never(),
      KeyResult::Known(keys) => {
        if keys.is_empty() {
          self.store.never()
        } else {
          let mut types = Vec::new();
          for key in keys {
            types.push(self.store.literal_string(key));
          }
          self.store.union(types)
        }
      }
    }
  }

  fn normalize_mapped(&mut self, mapped: &MappedType, env: &Env) -> TypeId {
    let keys = match self.string_literals(mapped.keys, env) {
      Some(k) => k,
      None => {
        self.diagnostics.push(
          Diagnostic::new("unable to enumerate mapped type keys").with_note("returning unknown"),
        );
        return self.store.unknown();
      }
    };

    let mut properties = HashMap::<String, Property>::new();

    for key in keys {
      let lit_ty = self.store.literal_string(key.clone());
      let mut branch_env = env.clone();
      branch_env.insert(mapped.param, lit_ty);

      let final_keys = if let Some(as_type) = mapped.as_type {
        match self.string_literals(as_type, &branch_env) {
          Some(names) => names,
          None => {
            self.diagnostics.push(
              Diagnostic::new("unable to remap mapped type key").with_note("returning unknown"),
            );
            return self.store.unknown();
          }
        }
      } else {
        vec![key.clone()]
      };

      let value_ty = self.normalize(mapped.value_type, &branch_env);

      for final_key in final_keys {
        let entry = properties.entry(final_key.clone()).or_insert(Property {
          ty: value_ty,
          optional: false,
          readonly: false,
        });
        if entry.ty != value_ty {
          entry.ty = self.store.union(vec![entry.ty, value_ty]);
        }
        entry.optional = match mapped.optional {
          MappedModifier::Add => true,
          MappedModifier::Remove => false,
          MappedModifier::Inherit => entry.optional,
        };
        entry.readonly = match mapped.readonly {
          MappedModifier::Add => true,
          MappedModifier::Remove => false,
          MappedModifier::Inherit => entry.readonly,
        };
      }
    }

    let mut sorted = Vec::new();
    for (k, v) in properties.into_iter() {
      sorted.push((k, v));
    }
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    self.store.object(sorted)
  }

  fn normalize_template(&mut self, tpl: &TemplateType, env: &Env) -> TypeId {
    match self.expand_template_parts(&tpl.parts, env) {
      Some(parts) => {
        let mut lits = Vec::new();
        let mut seen = HashSet::new();
        for part in parts {
          if seen.insert(part.clone()) {
            lits.push(self.store.literal_string(part));
          }
        }
        self.store.union(lits)
      }
      None => {
        self.diagnostics.push(
          Diagnostic::new("unable to expand template literal type")
            .with_note("falling back to string"),
        );
        self.store.string()
      }
    }
  }

  fn expand_template_parts(&mut self, parts: &[TemplatePart], env: &Env) -> Option<Vec<String>> {
    let mut acc = vec![String::new()];
    for part in parts.iter() {
      let options: Vec<String> = match part {
        TemplatePart::Literal(s) => vec![s.clone()],
        TemplatePart::Type(ty) => self.string_literals(*ty, env)?,
      };
      let mut next = Vec::new();
      for prefix in acc.iter() {
        for opt in options.iter() {
          let mut combined = prefix.clone();
          combined.push_str(opt);
          next.push(combined);
        }
      }
      acc = next;
    }
    acc.sort();
    acc.dedup();
    Some(acc)
  }

  fn string_literals(&mut self, ty: TypeId, env: &Env) -> Option<Vec<String>> {
    let norm = self.normalize(ty, env);
    match self.store.kind(norm).clone() {
      TypeKind::LiteralString(s) => Some(vec![s.clone()]),
      TypeKind::Never => Some(Vec::new()),
      TypeKind::Union(members) => {
        let mut res = Vec::new();
        for m in members.into_iter() {
          let Some(mut more) = self.string_literals(m, env) else {
            return None;
          };
          res.append(&mut more);
        }
        res.sort();
        res.dedup();
        Some(res)
      }
      TypeKind::Template(tpl) => self.expand_template_parts(&tpl.parts, env),
      _ => None,
    }
  }

  fn is_assignable(&mut self, src: TypeId, target: TypeId, env: &Env) -> bool {
    let key = (src, target, EnvKey::from_env(env));
    if let Some(cached) = self.assign_cache.get(&key) {
      return *cached;
    }

    let result = self.is_assignable_inner(src, target, env);
    self.assign_cache.insert(key, result);
    result
  }

  fn is_assignable_inner(&mut self, src: TypeId, target: TypeId, env: &Env) -> bool {
    if target == self.store.any() || target == self.store.unknown() {
      return true;
    }
    if src == self.store.any() {
      return true;
    }
    if src == self.store.never() {
      return true;
    }
    if target == self.store.never() {
      return src == self.store.never();
    }
    if src == target {
      return true;
    }

    let left = self.store.kind(src).clone();
    let right = self.store.kind(target).clone();

    match (left, right) {
      (_, TypeKind::Union(targets)) => targets.iter().any(|t| self.is_assignable(src, *t, env)),
      (TypeKind::Union(members), _) => members.iter().all(|m| self.is_assignable(*m, target, env)),
      (_, TypeKind::Intersection(targets)) => {
        targets.iter().all(|t| self.is_assignable(src, *t, env))
      }
      (TypeKind::Intersection(members), _) => {
        members.iter().any(|m| self.is_assignable(*m, target, env))
      }

      (TypeKind::LiteralString(_), TypeKind::String) => true,
      (TypeKind::LiteralNumber(_), TypeKind::Number) => true,
      (TypeKind::True, TypeKind::Boolean) => true,
      (TypeKind::False, TypeKind::Boolean) => true,

      (TypeKind::Object(src_obj), TypeKind::Object(target_obj)) => {
        for (name, target_prop) in target_obj.properties.iter() {
          if let Some(src_prop) = src_obj.properties.get(name) {
            if !self.is_assignable(src_prop.ty, target_prop.ty, env) {
              return false;
            }
          } else {
            return false;
          }
        }
        true
      }

      _ => false,
    }
  }

  fn collect_keys(&mut self, ty: TypeId, env: &Env) -> KeyResult {
    match self.store.kind(ty).clone() {
      TypeKind::Any | TypeKind::Unknown => KeyResult::Any,
      TypeKind::Never => KeyResult::Never,
      TypeKind::Object(obj) => KeyResult::Known(obj.properties.keys().cloned().collect()),
      TypeKind::Union(members) => {
        let mut cur: Option<HashSet<String>> = None;
        for member in members.into_iter() {
          match self.collect_keys(member, env) {
            KeyResult::Any => {}
            KeyResult::Never => return KeyResult::Never,
            KeyResult::Known(keys) => {
              if let Some(existing) = cur.as_mut() {
                existing.retain(|k| keys.contains(k));
              } else {
                cur = Some(keys);
              }
            }
          }
        }
        cur.map(KeyResult::Known).unwrap_or(KeyResult::Any)
      }
      TypeKind::Intersection(members) => {
        let mut set = HashSet::new();
        for member in members.into_iter() {
          match self.collect_keys(member, env) {
            KeyResult::Any => return KeyResult::Any,
            KeyResult::Never => return KeyResult::Never,
            KeyResult::Known(keys) => {
              set.extend(keys.into_iter());
            }
          }
        }
        KeyResult::Known(set)
      }
      _ => KeyResult::Any,
    }
  }
}

#[derive(Clone, Debug)]
enum KeyResult {
  Any,
  Never,
  Known(HashSet<String>),
}
