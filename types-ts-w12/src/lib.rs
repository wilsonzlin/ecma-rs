use semantic_js::DefId;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeKind {
  Any,
  Unknown,
  Never,
  Void,
  Null,
  Undefined,
  Boolean,
  Number,
  String,
  BigInt,
  Symbol,
  Literal(LiteralType),
  Ref(TypeRef),
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  Array(ArrayType),
  Tuple(Vec<TupleElement>),
  Function(FunctionType),
  Constructor(FunctionType),
  Object(ObjectType),
  KeyOf(TypeId),
  IndexedAccess { object: TypeId, index: TypeId },
  Conditional(ConditionalType),
  Mapped(MappedType),
  TemplateLiteral(TemplateLiteralType),
  Enum(EnumType),
  Class(ClassType),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LiteralType {
  String(String),
  Number(String),
  BigInt(String),
  Boolean(bool),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeRef {
  pub def: DefId,
  pub name: String,
  pub args: Vec<TypeId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArrayType {
  pub element: TypeId,
  pub readonly: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TupleElement {
  pub name: Option<String>,
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType {
  pub type_params: Vec<String>,
  pub params: Vec<FnParam>,
  pub ret: TypeId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnParam {
  pub name: Option<String>,
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ObjectType {
  pub properties: Vec<Property>,
  pub call_signatures: Vec<FunctionType>,
  pub construct_signatures: Vec<FunctionType>,
  pub index_signatures: Vec<IndexSignature>,
}

impl ObjectType {
  pub fn new() -> Self {
    Self {
      properties: Vec::new(),
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      index_signatures: Vec::new(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Property {
  pub name: String,
  pub ty: TypeId,
  pub optional: bool,
  pub readonly: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IndexSignature {
  pub key_type: TypeId,
  pub value_type: TypeId,
  pub readonly: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConditionalType {
  pub check: TypeId,
  pub extends: TypeId,
  pub true_type: TypeId,
  pub false_type: TypeId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MappedType {
  pub type_param: String,
  pub constraint: TypeId,
  pub name_type: Option<TypeId>,
  pub value: TypeId,
  pub optional_modifier: Option<bool>,
  pub readonly_modifier: Option<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TemplateLiteralType {
  pub head: String,
  pub spans: Vec<TemplateLiteralSpan>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TemplateLiteralSpan {
  pub type_id: TypeId,
  pub literal: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EnumType {
  pub name: String,
  pub members: Vec<EnumMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EnumMember {
  pub name: String,
  pub value: Option<EnumValue>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum EnumValue {
  String(String),
  Number(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassType {
  pub name: String,
  pub instance: TypeId,
  pub static_side: TypeId,
}

pub struct TypeStore {
  types: Vec<TypeKind>,
  interner: HashMap<TypeKind, TypeId>,
}

impl TypeStore {
  pub fn new() -> Self {
    TypeStore {
      types: Vec::new(),
      interner: HashMap::new(),
    }
  }

  pub fn intern(&mut self, kind: TypeKind) -> TypeId {
    if let Some(id) = self.interner.get(&kind) {
      *id
    } else {
      let id = TypeId(self.types.len() as u32);
      self.types.push(kind.clone());
      self.interner.insert(kind, id);
      id
    }
  }

  pub fn union(&mut self, mut types: Vec<TypeId>) -> TypeId {
    if types.is_empty() {
      return self.never();
    }
    types.sort();
    types.dedup();
    if types.len() == 1 {
      return types[0];
    }
    self.intern(TypeKind::Union(types))
  }

  pub fn intersection(&mut self, mut types: Vec<TypeId>) -> TypeId {
    if types.is_empty() {
      return self.never();
    }
    types.sort();
    types.dedup();
    if types.len() == 1 {
      return types[0];
    }
    self.intern(TypeKind::Intersection(types))
  }

  pub fn any(&mut self) -> TypeId {
    self.intern(TypeKind::Any)
  }

  pub fn unknown(&mut self) -> TypeId {
    self.intern(TypeKind::Unknown)
  }

  pub fn never(&mut self) -> TypeId {
    self.intern(TypeKind::Never)
  }

  pub fn void(&mut self) -> TypeId {
    self.intern(TypeKind::Void)
  }

  pub fn null(&mut self) -> TypeId {
    self.intern(TypeKind::Null)
  }

  pub fn undefined(&mut self) -> TypeId {
    self.intern(TypeKind::Undefined)
  }

  pub fn boolean(&mut self) -> TypeId {
    self.intern(TypeKind::Boolean)
  }

  pub fn number(&mut self) -> TypeId {
    self.intern(TypeKind::Number)
  }

  pub fn string(&mut self) -> TypeId {
    self.intern(TypeKind::String)
  }

  pub fn bigint(&mut self) -> TypeId {
    self.intern(TypeKind::BigInt)
  }

  pub fn symbol(&mut self) -> TypeId {
    self.intern(TypeKind::Symbol)
  }

  pub fn get(&self, id: TypeId) -> &TypeKind {
    &self.types[id.0 as usize]
  }
}

pub struct TypeDisplay<'a> {
  store: &'a TypeStore,
}

impl<'a> TypeDisplay<'a> {
  pub fn new(store: &'a TypeStore) -> Self {
    Self { store }
  }

  pub fn format(&self, id: TypeId) -> String {
    let mut out = String::new();
    self.fmt_type(id, &mut out);
    out
  }

  fn fmt_type(&self, id: TypeId, out: &mut String) {
    match self.store.get(id) {
      TypeKind::Any => out.push_str("any"),
      TypeKind::Unknown => out.push_str("unknown"),
      TypeKind::Never => out.push_str("never"),
      TypeKind::Void => out.push_str("void"),
      TypeKind::Null => out.push_str("null"),
      TypeKind::Undefined => out.push_str("undefined"),
      TypeKind::Boolean => out.push_str("boolean"),
      TypeKind::Number => out.push_str("number"),
      TypeKind::String => out.push_str("string"),
      TypeKind::BigInt => out.push_str("bigint"),
      TypeKind::Symbol => out.push_str("symbol"),
      TypeKind::Literal(lit) => self.fmt_literal(lit, out),
      TypeKind::Ref(r) => {
        out.push_str(&r.name);
        if !r.args.is_empty() {
          out.push('<');
          for (i, arg) in r.args.iter().enumerate() {
            if i > 0 {
              out.push_str(", ");
            }
            self.fmt_type(*arg, out);
          }
          out.push('>');
        }
      }
      TypeKind::Union(types) => self.join(types, " | ", out),
      TypeKind::Intersection(types) => self.join(types, " & ", out),
      TypeKind::Array(arr) => {
        if arr.readonly {
          out.push_str("readonly ");
        }
        self.wrap_if_union(arr.element, out);
        out.push_str("[]");
      }
      TypeKind::Tuple(elements) => {
        out.push('[');
        for (i, elem) in elements.iter().enumerate() {
          if i > 0 {
            out.push_str(", ");
          }
          if let Some(name) = &elem.name {
            out.push_str(name);
            out.push_str(": ");
          }
          if elem.rest {
            out.push_str("...");
          }
          self.fmt_type(elem.ty, out);
          if elem.optional {
            out.push('?');
          }
        }
        out.push(']');
      }
      TypeKind::Function(func) => self.fmt_function("=>", func, out),
      TypeKind::Constructor(func) => self.fmt_function("=>", func, out),
      TypeKind::Object(obj) => self.fmt_object(obj, out),
      TypeKind::KeyOf(inner) => {
        out.push_str("keyof ");
        self.fmt_type(*inner, out);
      }
      TypeKind::IndexedAccess { object, index } => {
        self.fmt_type(*object, out);
        out.push('[');
        self.fmt_type(*index, out);
        out.push(']');
      }
      TypeKind::Conditional(cond) => {
        self.fmt_type(cond.check, out);
        out.push_str(" extends ");
        self.fmt_type(cond.extends, out);
        out.push_str(" ? ");
        self.fmt_type(cond.true_type, out);
        out.push_str(" : ");
        self.fmt_type(cond.false_type, out);
      }
      TypeKind::Mapped(mapped) => {
        out.push('{');
        out.push_str(" [");
        out.push_str(&mapped.type_param);
        out.push_str(" in ");
        self.fmt_type(mapped.constraint, out);
        out.push(']');
        if let Some(opt) = mapped.optional_modifier {
          out.push(if opt { '?' } else { '!' });
        }
        out.push_str(": ");
        self.fmt_type(mapped.value, out);
        out.push_str(" }");
      }
      TypeKind::TemplateLiteral(tpl) => {
        out.push('`');
        out.push_str(&tpl.head);
        for span in &tpl.spans {
          out.push_str("${");
          self.fmt_type(span.type_id, out);
          out.push('}');
          out.push_str(&span.literal);
        }
        out.push('`');
      }
      TypeKind::Enum(enm) => {
        out.push_str("enum ");
        out.push_str(&enm.name);
      }
      TypeKind::Class(class) => {
        out.push_str("class ");
        out.push_str(&class.name);
      }
    }
  }

  fn fmt_literal(&self, lit: &LiteralType, out: &mut String) {
    match lit {
      LiteralType::String(s) => {
        out.push('"');
        out.push_str(s);
        out.push('"');
      }
      LiteralType::Number(n) => out.push_str(n),
      LiteralType::BigInt(n) => {
        out.push_str(n);
        out.push('n');
      }
      LiteralType::Boolean(b) => out.push_str(if *b { "true" } else { "false" }),
    }
  }

  fn fmt_function(&self, arrow: &str, func: &FunctionType, out: &mut String) {
    out.push('(');
    for (i, param) in func.params.iter().enumerate() {
      if i > 0 {
        out.push_str(", ");
      }
      if let Some(name) = &param.name {
        out.push_str(name);
        if param.optional {
          out.push('?');
        }
        out.push_str(": ");
      }
      if param.rest {
        out.push_str("...");
      }
      self.fmt_type(param.ty, out);
    }
    out.push(')');
    out.push(' ');
    out.push_str(arrow);
    out.push(' ');
    self.fmt_type(func.ret, out);
  }

  fn fmt_object(&self, obj: &ObjectType, out: &mut String) {
    out.push('{');
    let mut first = true;
    let mut properties = obj.properties.clone();
    properties.sort_by(|a, b| a.name.cmp(&b.name));
    for prop in &properties {
      if !first {
        out.push(' ');
      }
      first = false;
      out.push_str(&prop.name);
      if prop.optional {
        out.push('?');
      }
      out.push_str(": ");
      self.fmt_type(prop.ty, out);
      out.push(';');
    }
    for call in &obj.call_signatures {
      if !first {
        out.push(' ');
      }
      first = false;
      self.fmt_function("=>", call, out);
      out.push(';');
    }
    for construct in &obj.construct_signatures {
      if !first {
        out.push(' ');
      }
      first = false;
      out.push_str("new ");
      self.fmt_function("=>", construct, out);
      out.push(';');
    }
    for index in &obj.index_signatures {
      if !first {
        out.push(' ');
      }
      first = false;
      out.push('[');
      out.push_str("key: ");
      self.fmt_type(index.key_type, out);
      out.push(']');
      out.push_str(": ");
      self.fmt_type(index.value_type, out);
      out.push(';');
    }
    out.push('}');
  }

  fn join(&self, types: &[TypeId], sep: &str, out: &mut String) {
    for (i, ty) in types.iter().enumerate() {
      if i > 0 {
        out.push_str(sep);
      }
      self.fmt_type(*ty, out);
    }
  }

  fn wrap_if_union(&self, id: TypeId, out: &mut String) {
    let needs_wrap = matches!(self.store.get(id), TypeKind::Union(_));
    if needs_wrap {
      out.push('(');
    }
    self.fmt_type(id, out);
    if needs_wrap {
      out.push(')');
    }
  }
}
