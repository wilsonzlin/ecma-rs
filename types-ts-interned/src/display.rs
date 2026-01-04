use crate::ids::{DefId, NameId, TypeId};
use crate::kind::MappedModifier;
use crate::kind::TemplateLiteralType;
use crate::kind::TypeKind;
use crate::shape::PropKey;
use crate::shape::Property;
use crate::store::TypeStore;
use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;
use unicode_ident::{is_xid_continue, is_xid_start};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
  Union,
  Intersection,
  Primary,
}

pub struct TypeDisplay<'a> {
  store: &'a TypeStore,
  ty: TypeId,
  ref_resolver: Option<Arc<dyn Fn(DefId) -> Option<String> + Send + Sync + 'a>>,
}

impl<'a> TypeDisplay<'a> {
  pub fn new(store: &'a TypeStore, ty: TypeId) -> Self {
    Self {
      store,
      ty,
      ref_resolver: None,
    }
  }

  /// Provide a resolver for [`TypeKind::Ref`] nodes that returns a friendly name
  /// for the referenced definition, if available.
  pub fn with_ref_resolver(
    mut self,
    resolver: Arc<dyn Fn(DefId) -> Option<String> + Send + Sync + 'a>,
  ) -> Self {
    self.ref_resolver = Some(resolver);
    self
  }

  fn precedence(&self, ty: TypeId) -> Precedence {
    match self.store.type_kind(ty) {
      TypeKind::Union(_) => Precedence::Union,
      TypeKind::Intersection(_) => Precedence::Intersection,
      _ => Precedence::Primary,
    }
  }

  fn fmt_with_prec(
    &self,
    ty: TypeId,
    parent: Precedence,
    f: &mut fmt::Formatter<'_>,
  ) -> fmt::Result {
    let needs_paren = self.precedence(ty) < parent;
    if needs_paren {
      write!(f, "(")?;
    }
    self.fmt_type(ty, f)?;
    if needs_paren {
      write!(f, ")")?;
    }
    Ok(())
  }

  fn fmt_property(&self, prop: &Property, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(access) = &prop.data.accessibility {
      write!(
        f,
        "{} ",
        match access {
          crate::shape::Accessibility::Public => "public",
          crate::shape::Accessibility::Protected => "protected",
          crate::shape::Accessibility::Private => "private",
        }
      )?;
    }
    if prop.data.readonly {
      write!(f, "readonly ")?;
    }
    self.fmt_prop_key(&prop.key, f)?;
    if prop.data.optional {
      write!(f, "?")?;
    }
    write!(f, ": ")?;
    self.fmt_with_prec(prop.data.ty, Precedence::Primary, f)
  }

  fn fmt_prop_key(&self, key: &PropKey, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match key {
      PropKey::String(id) => self.fmt_name(*id, f),
      PropKey::Number(num) => write!(f, "{}", num),
      PropKey::Symbol(id) => {
        write!(f, "[")?;
        self.fmt_name(*id, f)?;
        write!(f, "]")
      }
    }
  }

  fn fmt_name(&self, id: NameId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let name = self.store.name(id);
    if is_identifier(&name) {
      write!(f, "{}", name)
    } else {
      write!(f, "\"{}\"", escape_ts_string_literal(&name))
    }
  }

  fn fmt_template(&self, tpl: &TemplateLiteralType, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "`")?;
    write!(f, "{}", escape_ts_template_literal_chunk(&tpl.head))?;
    for span in &tpl.spans {
      write!(f, "${{")?;
      self.fmt_type(span.ty, f)?;
      write!(f, "}}{}", escape_ts_template_literal_chunk(&span.literal))?;
    }
    write!(f, "`")
  }

  fn fmt_mapped_modifier(
    &self,
    modifier: MappedModifier,
    keyword: &str,
    f: &mut fmt::Formatter<'_>,
  ) -> fmt::Result {
    match modifier {
      MappedModifier::Preserve => Ok(()),
      MappedModifier::Add => write!(f, "{} ", keyword),
      MappedModifier::Remove => write!(f, "-{} ", keyword),
    }
  }

  fn fmt_type(&self, ty: TypeId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.store.type_kind(ty) {
      TypeKind::Any => write!(f, "any"),
      TypeKind::Unknown => write!(f, "unknown"),
      TypeKind::Never => write!(f, "never"),
      TypeKind::Void => write!(f, "void"),
      TypeKind::Null => write!(f, "null"),
      TypeKind::Undefined => write!(f, "undefined"),
      TypeKind::EmptyObject => write!(f, "{{}}"),
      TypeKind::Boolean => write!(f, "boolean"),
      TypeKind::Number => write!(f, "number"),
      TypeKind::String => write!(f, "string"),
      TypeKind::BigInt => write!(f, "bigint"),
      TypeKind::Symbol => write!(f, "symbol"),
      TypeKind::UniqueSymbol => write!(f, "unique symbol"),
      TypeKind::BooleanLiteral(val) => write!(f, "{}", val),
      TypeKind::NumberLiteral(val) => write!(f, "{}", val.0),
      TypeKind::StringLiteral(id) => {
        let s = self.store.name(id);
        write!(f, "\"{}\"", escape_ts_string_literal(&s))
      }
      TypeKind::BigIntLiteral(ref val) => write!(f, "{}n", val),
      TypeKind::This => write!(f, "this"),
      TypeKind::Infer { param, constraint } => {
        write!(f, "infer T{}", param.0)?;
        if let Some(constraint) = constraint {
          write!(f, " extends ")?;
          self.fmt_with_prec(constraint, Precedence::Primary, f)?;
        }
        Ok(())
      }
      TypeKind::Tuple(elems) => {
        let readonly_tuple = elems.iter().all(|elem| elem.readonly);
        if readonly_tuple {
          write!(f, "readonly ")?;
        }
        write!(f, "[")?;
        let mut iter = elems.iter().peekable();
        while let Some(elem) = iter.next() {
          if elem.rest {
            write!(f, "...")?;
          }
          if elem.readonly && !readonly_tuple {
            write!(f, "readonly ")?;
          }
          self.fmt_with_prec(elem.ty, Precedence::Primary, f)?;
          if elem.optional {
            write!(f, "?")?;
          }
          if iter.peek().is_some() {
            write!(f, ", ")?;
          }
        }
        write!(f, "]")
      }
      TypeKind::Array { ty, readonly } => {
        if readonly {
          write!(f, "readonly ")?;
        }
        self.fmt_with_prec(ty, Precedence::Primary, f)?;
        write!(f, "[]")
      }
      TypeKind::Union(members) => {
        let mut members = members.clone();
        members.sort_by(|a, b| self.union_member_cmp(*a, *b));
        let mut iter = members.iter().peekable();
        while let Some(member) = iter.next() {
          self.fmt_with_prec(*member, Precedence::Union, f)?;
          if iter.peek().is_some() {
            write!(f, " | ")?;
          }
        }
        Ok(())
      }
      TypeKind::Intersection(members) => {
        let mut iter = members.iter().peekable();
        while let Some(member) = iter.next() {
          self.fmt_with_prec(*member, Precedence::Intersection, f)?;
          if iter.peek().is_some() {
            write!(f, " & ")?;
          }
        }
        Ok(())
      }
      TypeKind::Object(obj) => {
        let object = self.store.object(obj);
        let shape = self.store.shape(object.shape);
        if shape.properties.is_empty()
          && shape.call_signatures.is_empty()
          && shape.construct_signatures.is_empty()
          && shape.indexers.is_empty()
        {
          return write!(f, "object");
        }
        write!(f, "{{")?;
        let mut first = true;
        for prop in shape.properties.iter() {
          if first {
            write!(f, " ")?;
            first = false;
          } else {
            write!(f, "; ")?;
          }
          self.fmt_property(prop, f)?;
        }
        for idxer in shape.indexers.iter() {
          if first {
            write!(f, " ")?;
            first = false;
          } else {
            write!(f, "; ")?;
          }
          if idxer.readonly {
            write!(f, "readonly ")?;
          }
          write!(f, "[")?;
          self.fmt_with_prec(idxer.key_type, Precedence::Primary, f)?;
          write!(f, "]: ")?;
          self.fmt_with_prec(idxer.value_type, Precedence::Primary, f)?;
        }
        for sig in shape.call_signatures.iter() {
          let sig = self.store.signature(*sig);
          if first {
            write!(f, " ")?;
            first = false;
          } else {
            write!(f, "; ")?;
          }
          self.fmt_signature(&sig, f)?;
        }
        for sig in shape.construct_signatures.iter() {
          let sig = self.store.signature(*sig);
          if first {
            write!(f, " ")?;
            first = false;
          } else {
            write!(f, "; ")?;
          }
          write!(f, "new ")?;
          self.fmt_signature(&sig, f)?;
        }
        if !first {
          write!(f, " ")?;
        }
        write!(f, "}}")
      }
      TypeKind::Callable { overloads } => {
        let mut iter = overloads.iter().peekable();
        while let Some(sig_id) = iter.next() {
          let sig = self.store.signature(*sig_id);
          self.fmt_signature(&sig, f)?;
          if iter.peek().is_some() {
            write!(f, " & ")?;
          }
        }
        Ok(())
      }
      TypeKind::Ref { def, args } => {
        if let Some(resolver) = &self.ref_resolver {
          if let Some(name) = resolver(def) {
            write!(f, "{name}")?;
            if !args.is_empty() {
              write!(f, "<")?;
              let mut iter = args.iter().peekable();
              while let Some(arg) = iter.next() {
                self.fmt_type(*arg, f)?;
                if iter.peek().is_some() {
                  write!(f, ", ")?;
                }
              }
              write!(f, ">")?;
            }
            return Ok(());
          }
        }
        write!(f, "ref#{}", def.0)?;
        if !args.is_empty() {
          write!(f, "<")?;
          let mut iter = args.iter().peekable();
          while let Some(arg) = iter.next() {
            self.fmt_type(*arg, f)?;
            if iter.peek().is_some() {
              write!(f, ", ")?;
            }
          }
          write!(f, ">")?;
        }
        Ok(())
      }
      TypeKind::TypeParam(id) => write!(f, "T{}", id.0),
      TypeKind::Predicate {
        asserted, asserts, ..
      } => {
        if let Some(asserted) = asserted {
          let inner = TypeDisplay::new(self.store, asserted);
          if asserts {
            write!(f, "asserts {}", inner)
          } else {
            write!(f, "{}", inner)
          }
        } else if asserts {
          write!(f, "asserts boolean")
        } else {
          write!(f, "boolean")
        }
      }
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => {
        if distributive {
          write!(f, "distrib ")?;
        }
        self.fmt_type(check, f)?;
        write!(f, " extends ")?;
        self.fmt_type(extends, f)?;
        write!(f, " ? ")?;
        self.fmt_type(true_ty, f)?;
        write!(f, " : ")?;
        self.fmt_type(false_ty, f)
      }
      TypeKind::Mapped(mapped) => {
        write!(f, "{{ ")?;
        self.fmt_mapped_modifier(mapped.readonly, "readonly", f)?;
        write!(f, "[K in ")?;
        self.fmt_type(mapped.source, f)?;
        if let Some(as_type) = mapped.as_type {
          write!(f, " as ")?;
          self.fmt_type(as_type, f)?;
        }
        write!(
          f,
          "]{}",
          match mapped.optional {
            MappedModifier::Preserve => ": ",
            MappedModifier::Add => "?: ",
            MappedModifier::Remove => "-?: ",
          }
        )?;
        self.fmt_type(mapped.value, f)?;
        write!(f, " }}")
      }
      TypeKind::TemplateLiteral(tpl) => self.fmt_template(&tpl, f),
      TypeKind::Intrinsic { kind, ty } => {
        if matches!(kind, crate::kind::IntrinsicKind::BuiltinIteratorReturn) {
          write!(f, "{}", kind.as_str())
        } else {
          write!(f, "{}<", kind.as_str())?;
          self.fmt_type(ty, f)?;
          write!(f, ">")
        }
      }
      TypeKind::IndexedAccess { obj, index } => {
        self.fmt_with_prec(obj, Precedence::Primary, f)?;
        write!(f, "[")?;
        self.fmt_type(index, f)?;
        write!(f, "]")
      }
      TypeKind::KeyOf(inner) => {
        write!(f, "keyof ")?;
        let prec = self.precedence(inner);
        if prec == Precedence::Primary {
          self.fmt_type(inner, f)
        } else {
          write!(f, "(")?;
          self.fmt_type(inner, f)?;
          write!(f, ")")
        }
      }
    }
  }

  fn union_member_cmp(&self, a: TypeId, b: TypeId) -> Ordering {
    let a_kind = self.store.type_kind(a);
    let b_kind = self.store.type_kind(b);
    let a_ref = matches!(a_kind, TypeKind::Ref { .. });
    let b_ref = matches!(b_kind, TypeKind::Ref { .. });
    let a_nullish = matches!(a_kind, TypeKind::Null | TypeKind::Undefined);
    let b_nullish = matches!(b_kind, TypeKind::Null | TypeKind::Undefined);
    if a_ref && b_nullish {
      return Ordering::Less;
    }
    if b_ref && a_nullish {
      return Ordering::Greater;
    }
    self.store.type_cmp(a, b)
  }

  fn fmt_signature(
    &self,
    sig: &crate::signature::Signature,
    f: &mut fmt::Formatter<'_>,
  ) -> fmt::Result {
    if !sig.type_params.is_empty() {
      write!(f, "<")?;
      let mut iter = sig.type_params.iter().peekable();
      while let Some(param) = iter.next() {
        write!(f, "T{}", param.id.0)?;
        if let Some(constraint) = param.constraint {
          write!(f, " extends ")?;
          self.fmt_type(constraint, f)?;
        }
        if let Some(default) = param.default {
          write!(f, " = ")?;
          self.fmt_type(default, f)?;
        }
        if iter.peek().is_some() {
          write!(f, ", ")?;
        }
      }
      write!(f, ">")?;
    }
    write!(f, "(")?;
    let mut needs_comma = false;

    if let Some(this_param) = sig.this_param {
      write!(f, "this: ")?;
      self.fmt_type(this_param, f)?;
      needs_comma = true;
    }

    let mut iter = sig.params.iter().peekable();
    while let Some(param) = iter.next() {
      if needs_comma {
        write!(f, ", ")?;
      }
      if param.rest {
        write!(f, "...")?;
      }
      if let Some(name) = param.name {
        self.fmt_name(name, f)?;
        if param.optional {
          write!(f, "?")?;
        }
        write!(f, ": ")?;
      }
      self.fmt_type(param.ty, f)?;
      needs_comma = true;
    }
    write!(f, ") => ")?;
    self.fmt_type(sig.ret, f)
  }
}

impl<'a> fmt::Debug for TypeDisplay<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("TypeDisplay").field("ty", &self.ty).finish()
  }
}

impl<'a> fmt::Display for TypeDisplay<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.fmt_type(self.ty, f)
  }
}

#[derive(Debug, Clone, Copy)]
enum EscapeKind {
  StringLiteral,
  TemplateChunk,
}

fn escape_ts_string_literal(s: &str) -> String {
  escape_string_like(s, EscapeKind::StringLiteral)
}

fn escape_ts_template_literal_chunk(s: &str) -> String {
  escape_string_like(s, EscapeKind::TemplateChunk)
}

fn escape_string_like(s: &str, kind: EscapeKind) -> String {
  let mut escaped = String::with_capacity(s.len());
  let mut chars = s.chars().peekable();
  while let Some(ch) = chars.next() {
    if matches!(kind, EscapeKind::TemplateChunk) && ch == '$' {
      if let Some('{') = chars.peek() {
        escaped.push_str("\\${");
        chars.next();
        continue;
      }
    }
    match ch {
      '\\' => escaped.push_str("\\\\"),
      '"' if matches!(kind, EscapeKind::StringLiteral) => escaped.push_str("\\\""),
      '`' if matches!(kind, EscapeKind::TemplateChunk) => escaped.push_str("\\`"),
      '\n' => escaped.push_str("\\n"),
      '\r' => escaped.push_str("\\r"),
      '\t' => escaped.push_str("\\t"),
      '\u{08}' => escaped.push_str("\\b"),
      '\u{0B}' => escaped.push_str("\\v"),
      '\u{0C}' => escaped.push_str("\\f"),
      '\0' => escaped.push_str("\\0"),
      '\u{2028}' => escaped.push_str("\\u2028"),
      '\u{2029}' => escaped.push_str("\\u2029"),
      other => escaped.push(other),
    }
  }
  escaped
}

fn is_identifier(name: &str) -> bool {
  let mut chars = name.chars();
  match chars.next() {
    Some(c) if is_identifier_start(c) => {}
    _ => return false,
  }
  chars.all(is_identifier_continue)
}

fn is_identifier_start(ch: char) -> bool {
  ch == '_' || ch == '$' || is_xid_start(ch)
}

fn is_identifier_continue(ch: char) -> bool {
  ch == '_' || ch == '$' || is_xid_continue(ch)
}
