use crate::ids::NameId;
use crate::ids::TypeId;
use crate::kind::MappedModifier;
use crate::kind::TemplateLiteralType;
use crate::kind::TypeKind;
use crate::shape::PropKey;
use crate::shape::Property;
use crate::store::TypeStore;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
  Union,
  Intersection,
  Primary,
}

#[derive(Debug)]
pub struct TypeDisplay<'a> {
  store: &'a TypeStore,
  ty: TypeId,
}

impl<'a> TypeDisplay<'a> {
  pub fn new(store: &'a TypeStore, ty: TypeId) -> Self {
    Self { store, ty }
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
      write!(f, "\"{}\"", name)
    }
  }

  fn fmt_template(&self, tpl: &TemplateLiteralType, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "`")?;
    write!(f, "{}", tpl.head)?;
    for span in &tpl.spans {
      write!(f, "${{")?;
      self.fmt_type(span.ty, f)?;
      write!(f, "}}{}", span.literal)?;
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
        write!(f, "\"{}\"", s)
      }
      TypeKind::BigIntLiteral(ref val) => write!(f, "{}n", val),
      TypeKind::Union(members) => {
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
        write!(
          f,
          "[K{} in ",
          match mapped.optional {
            MappedModifier::Add => "?",
            MappedModifier::Remove => "-?",
            MappedModifier::Preserve => "",
          }
        )?;
        self.fmt_type(mapped.source, f)?;
        if let Some(as_type) = mapped.as_type {
          write!(f, " as ")?;
          self.fmt_type(as_type, f)?;
        }
        write!(f, "]: ")?;
        self.fmt_type(mapped.value, f)?;
        write!(f, " }}")
      }
      TypeKind::TemplateLiteral(tpl) => self.fmt_template(&tpl, f),
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

  fn fmt_signature(
    &self,
    sig: &crate::signature::Signature,
    f: &mut fmt::Formatter<'_>,
  ) -> fmt::Result {
    write!(f, "(")?;
    let mut iter = sig.params.iter().peekable();
    while let Some(param) = iter.next() {
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
      if iter.peek().is_some() {
        write!(f, ", ")?;
      }
    }
    write!(f, ") => ")?;
    self.fmt_type(sig.ret, f)
  }
}

impl<'a> fmt::Display for TypeDisplay<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.fmt_type(self.ty, f)
  }
}

fn is_identifier(name: &str) -> bool {
  let mut chars = name.chars();
  match chars.next() {
    Some(c) if c.is_ascii_alphabetic() || c == '_' || c == '$' => {}
    _ => return false,
  }
  chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}
