use crate::diagnostics::Diagnostic;
use crate::FileId;
use crate::Program;
use parse_js::ast::class_or_object::ClassMember;
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ParamDecl;
use parse_js::ast::ts_stmt::EnumDecl;
use parse_js::ast::type_expr::*;
use parse_js::loc::Loc;
use semantic_js::DefId;
use semantic_js::GlobalSymbols;
use types_ts::*;

pub struct TypeLowerer<'a> {
  program: &'a Program,
  pub(crate) store: &'a mut TypeStore,
  globals: &'a GlobalSymbols,
  file_id: FileId,
}

impl<'a> TypeLowerer<'a> {
  pub fn new(
    program: &'a Program,
    store: &'a mut TypeStore,
    globals: &'a GlobalSymbols,
    file_id: FileId,
  ) -> Self {
    TypeLowerer {
      program,
      store,
      globals,
      file_id,
    }
  }

  pub fn lower_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match &*expr.stx {
      TypeExpr::Any(_) => self.store.any(),
      TypeExpr::Unknown(_) => self.store.unknown(),
      TypeExpr::Never(_) => self.store.never(),
      TypeExpr::Void(_) => self.store.void(),
      TypeExpr::String(_) => self.store.string(),
      TypeExpr::Number(_) => self.store.number(),
      TypeExpr::Boolean(_) => self.store.boolean(),
      TypeExpr::BigInt(_) => self.store.bigint(),
      TypeExpr::Symbol(_) | TypeExpr::UniqueSymbol(_) => self.store.symbol(),
      TypeExpr::Object(_) => self.store.intern(TypeKind::Object(ObjectType::new())),
      TypeExpr::Null(_) => self.store.null(),
      TypeExpr::Undefined(_) => self.store.undefined(),
      TypeExpr::TypeReference(reference) => self.lower_type_reference(reference, expr.loc),
      TypeExpr::LiteralType(lit) => self.lower_literal(lit),
      TypeExpr::ArrayType(arr) => {
        let element = self.lower_type_expr(&arr.stx.element_type);
        self.store.intern(TypeKind::Array(ArrayType {
          element,
          readonly: arr.stx.readonly,
        }))
      }
      TypeExpr::TupleType(tuple) => {
        let elements = tuple
          .stx
          .elements
          .iter()
          .map(|elem| TupleElement {
            name: elem.stx.label.clone(),
            ty: self.lower_type_expr(&elem.stx.type_expr),
            optional: elem.stx.optional,
            rest: elem.stx.rest,
          })
          .collect();
        self.store.intern(TypeKind::Tuple(elements))
      }
      TypeExpr::UnionType(union) => {
        let members = union
          .stx
          .types
          .iter()
          .map(|t| self.lower_type_expr(t))
          .collect();
        self.store.union(members)
      }
      TypeExpr::IntersectionType(intersection) => {
        let members = intersection
          .stx
          .types
          .iter()
          .map(|t| self.lower_type_expr(t))
          .collect();
        self.store.intersection(members)
      }
      TypeExpr::FunctionType(func) => {
        let function = self.lower_function_signature(
          &func.stx.type_parameters,
          &func.stx.parameters,
          Some(&func.stx.return_type),
        );
        self.store.intern(TypeKind::Function(function))
      }
      TypeExpr::ConstructorType(func) => {
        let function = self.lower_function_signature(
          &func.stx.type_parameters,
          &func.stx.parameters,
          Some(&func.stx.return_type),
        );
        self.store.intern(TypeKind::Constructor(function))
      }
      TypeExpr::ObjectType(obj) => self.lower_object_members(&obj.stx.members),
      TypeExpr::ParenthesizedType(inner) => self.lower_type_expr(&inner.stx.type_expr),
      TypeExpr::TypeQuery(_query) => {
        self.unsupported("TC1001", "type query not yet supported", expr.loc);
        self.store.unknown()
      }
      TypeExpr::KeyOfType(keyof) => {
        let inner = self.lower_type_expr(&keyof.stx.type_expr);
        self.store.intern(TypeKind::KeyOf(inner))
      }
      TypeExpr::IndexedAccessType(indexed) => {
        let object = self.lower_type_expr(&indexed.stx.object_type);
        let index = self.lower_type_expr(&indexed.stx.index_type);
        self.store.intern(TypeKind::IndexedAccess { object, index })
      }
      TypeExpr::ConditionalType(cond) => {
        let check = self.lower_type_expr(&cond.stx.check_type);
        let extends = self.lower_type_expr(&cond.stx.extends_type);
        let true_type = self.lower_type_expr(&cond.stx.true_type);
        let false_type = self.lower_type_expr(&cond.stx.false_type);
        self.store.intern(TypeKind::Conditional(ConditionalType {
          check,
          extends,
          true_type,
          false_type,
        }))
      }
      TypeExpr::InferType(_) => {
        self.unsupported("TC1001", "infer types are not yet supported", expr.loc);
        self.store.unknown()
      }
      TypeExpr::MappedType(mapped) => self.lower_mapped_type(mapped),
      TypeExpr::TemplateLiteralType(template) => self.lower_template_literal(template),
      TypeExpr::TypePredicate(_) => {
        self.unsupported("TC1001", "type predicates are not yet supported", expr.loc);
        self.store.boolean()
      }
      TypeExpr::ThisType(_) => self.store.unknown(),
      TypeExpr::ImportType(import) => {
        self.unsupported(
          "TC1001",
          format!("import type {}", import.stx.module_specifier),
          expr.loc,
        );
        self.store.unknown()
      }
    }
  }

  pub fn lower_function_signature(
    &mut self,
    type_parameters: &Option<Vec<Node<TypeParameter>>>,
    parameters: &[Node<TypeFunctionParameter>],
    return_type: Option<&Node<TypeExpr>>,
  ) -> FunctionType {
    let type_params = self.lower_type_params(type_parameters);
    let params = parameters
      .iter()
      .map(|param| FnParam {
        name: param.stx.name.clone(),
        ty: self.lower_type_expr(&param.stx.type_expr),
        optional: param.stx.optional,
        rest: param.stx.rest,
      })
      .collect();
    let ret = return_type
      .map(|r| self.lower_type_expr(r))
      .unwrap_or_else(|| self.store.unknown());
    FunctionType {
      type_params,
      params,
      ret,
    }
  }

  pub fn lower_function_from_func(&mut self, func: &Func) -> FunctionType {
    let type_params = self.lower_type_params(&func.type_parameters);
    let params = func
      .parameters
      .iter()
      .map(|param| self.lower_param_decl(param))
      .collect();
    let ret = match &func.return_type {
      Some(ret) => self.lower_type_expr(ret),
      None => self.store.unknown(),
    };
    FunctionType {
      type_params,
      params,
      ret,
    }
  }

  pub fn lower_object_members(&mut self, members: &[Node<TypeMember>]) -> TypeId {
    let mut object = ObjectType::new();
    for member in members {
      match &*member.stx {
        TypeMember::Property(prop) => {
          if let Some(name) = self.property_name(&prop.stx.key) {
            let ty = prop
              .stx
              .type_annotation
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or_else(|| self.store.unknown());
            object.properties.push(Property {
              name,
              ty,
              optional: prop.stx.optional,
              readonly: prop.stx.readonly,
            });
          } else {
            self.unsupported(
              "TC1001",
              "computed property keys are not supported",
              member.loc,
            );
          }
        }
        TypeMember::Method(method) => {
          if let Some(name) = self.property_name(&method.stx.key) {
            let func = self.lower_function_signature(
              &method.stx.type_parameters,
              &method.stx.parameters,
              method.stx.return_type.as_ref(),
            );
            let func_type = self.store.intern(TypeKind::Function(func));
            object.properties.push(Property {
              name,
              ty: func_type,
              optional: method.stx.optional,
              readonly: false,
            });
          }
        }
        TypeMember::Constructor(cons) => {
          let func = self.lower_function_signature(
            &cons.stx.type_parameters,
            &cons.stx.parameters,
            cons.stx.return_type.as_ref(),
          );
          object.construct_signatures.push(func);
        }
        TypeMember::CallSignature(call) => {
          let func = self.lower_function_signature(
            &call.stx.type_parameters,
            &call.stx.parameters,
            call.stx.return_type.as_ref(),
          );
          object.call_signatures.push(func);
        }
        TypeMember::IndexSignature(sig) => {
          let key_type = self.lower_type_expr(&sig.stx.parameter_type);
          let value_type = self.lower_type_expr(&sig.stx.type_annotation);
          object.index_signatures.push(IndexSignature {
            key_type,
            value_type,
            readonly: sig.stx.readonly,
          });
        }
        TypeMember::GetAccessor(acc) => {
          if let Some(name) = self.property_name(&acc.stx.key) {
            let ty = acc
              .stx
              .return_type
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or_else(|| self.store.unknown());
            object.properties.push(Property {
              name,
              ty,
              optional: false,
              readonly: true,
            });
          }
        }
        TypeMember::SetAccessor(acc) => {
          if let Some(name) = self.property_name(&acc.stx.key) {
            let ty = self.lower_type_expr(&acc.stx.parameter.stx.type_expr);
            object.properties.push(Property {
              name,
              ty,
              optional: false,
              readonly: false,
            });
          }
        }
        TypeMember::MappedProperty(mapped) => {
          let mapped_type = self.lower_mapped_type(mapped);
          object.properties.push(Property {
            name: format!("[{}]", mapped.stx.type_parameter),
            ty: mapped_type,
            optional: false,
            readonly: false,
          });
        }
      }
    }
    self.store.intern(TypeKind::Object(object))
  }

  pub fn lower_enum(&mut self, decl: &Node<EnumDecl>) -> TypeId {
    let mut members = Vec::new();
    for member in &decl.stx.members {
      let value = member
        .stx
        .initializer
        .as_ref()
        .and_then(|init| match &*init.stx {
          parse_js::ast::expr::Expr::LitStr(lit) => Some(EnumValue::String(lit.stx.value.clone())),
          parse_js::ast::expr::Expr::LitNum(lit) => {
            Some(EnumValue::Number(lit.stx.value.to_string()))
          }
          parse_js::ast::expr::Expr::LitBigInt(lit) => {
            Some(EnumValue::Number(lit.stx.value.clone()))
          }
          parse_js::ast::expr::Expr::LitBool(lit) => {
            Some(EnumValue::String(lit.stx.value.to_string()))
          }
          _ => None,
        });
      members.push(EnumMember {
        name: member.stx.name.clone(),
        value,
      });
    }

    let enum_type = EnumType {
      name: decl.stx.name.clone(),
      members,
    };
    self.store.intern(TypeKind::Enum(enum_type))
  }

  pub fn lower_class_members(&mut self, members: &[Node<ClassMember>]) -> (TypeId, TypeId) {
    let mut instance = ObjectType::new();
    let mut static_side = ObjectType::new();
    for member in members {
      let m = &member.stx;
      match &m.val {
        parse_js::ast::class_or_object::ClassOrObjVal::Method(method) => {
          let func = self.lower_function_from_func(&method.stx.func.stx);
          let func_type = self.store.intern(TypeKind::Function(func));
          let name = self.class_member_name(&m.key);
          if let Some(name) = name {
            let target = if m.static_ {
              &mut static_side
            } else {
              &mut instance
            };
            target.properties.push(Property {
              name,
              ty: func_type,
              optional: m.optional,
              readonly: false,
            });
          }
        }
        parse_js::ast::class_or_object::ClassOrObjVal::Getter(getter) => {
          if let Some(name) = self.class_member_name(&m.key) {
            let ret = getter
              .stx
              .func
              .stx
              .return_type
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or_else(|| self.store.unknown());
            let target = if m.static_ {
              &mut static_side
            } else {
              &mut instance
            };
            target.properties.push(Property {
              name,
              ty: ret,
              optional: false,
              readonly: true,
            });
          }
        }
        parse_js::ast::class_or_object::ClassOrObjVal::Setter(setter) => {
          if let Some(name) = self.class_member_name(&m.key) {
            let ty = setter
              .stx
              .func
              .stx
              .parameters
              .get(0)
              .and_then(|p| p.stx.type_annotation.as_ref())
              .map(|t| self.lower_type_expr(t))
              .unwrap_or_else(|| self.store.unknown());
            let target = if m.static_ {
              &mut static_side
            } else {
              &mut instance
            };
            target.properties.push(Property {
              name,
              ty,
              optional: false,
              readonly: false,
            });
          }
        }
        parse_js::ast::class_or_object::ClassOrObjVal::Prop(_) => {
          if let Some(name) = self.class_member_name(&m.key) {
            let ty = m
              .type_annotation
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or_else(|| self.store.unknown());
            let target = if m.static_ {
              &mut static_side
            } else {
              &mut instance
            };
            target.properties.push(Property {
              name,
              ty,
              optional: m.optional,
              readonly: m.readonly,
            });
          }
        }
        parse_js::ast::class_or_object::ClassOrObjVal::IndexSignature(index_sig) => {
          let key_type = self.lower_type_expr(&index_sig.stx.parameter_type);
          let value_type = self.lower_type_expr(&index_sig.stx.type_annotation);
          let target = if m.static_ {
            &mut static_side
          } else {
            &mut instance
          };
          target.index_signatures.push(IndexSignature {
            key_type,
            value_type,
            readonly: m.readonly,
          });
        }
        parse_js::ast::class_or_object::ClassOrObjVal::StaticBlock(_) => {}
      }
    }

    let instance_type = self.store.intern(TypeKind::Object(instance));
    let static_type = self.store.intern(TypeKind::Object(static_side));
    (instance_type, static_type)
  }

  fn lower_literal(&mut self, lit: &Node<TypeLiteral>) -> TypeId {
    let lit = match &*lit.stx {
      TypeLiteral::String(s) => LiteralType::String(s.clone()),
      TypeLiteral::Number(n) => LiteralType::Number(n.clone()),
      TypeLiteral::BigInt(n) => LiteralType::BigInt(n.clone()),
      TypeLiteral::Boolean(b) => LiteralType::Boolean(*b),
      TypeLiteral::Null => return self.store.null(),
    };
    self.store.intern(TypeKind::Literal(lit))
  }

  fn lower_type_reference(&mut self, reference: &Node<TypeReference>, loc: Loc) -> TypeId {
    match &reference.stx.name {
      TypeEntityName::Identifier(name) => {
        let args = reference
          .stx
          .type_arguments
          .as_ref()
          .map(|args| args.iter().map(|arg| self.lower_type_expr(arg)).collect())
          .unwrap_or_default();
        if let Some(def) = self.resolve_type_ref(name) {
          self.store.intern(TypeKind::Ref(TypeRef {
            def,
            name: name.clone(),
            args,
          }))
        } else {
          self.unsupported("TC1002", format!("Unresolved type reference `{name}`"), loc);
          self.store.unknown()
        }
      }
      _ => {
        self.unsupported(
          "TC1001",
          "Qualified or import type references are not supported",
          loc,
        );
        self.store.unknown()
      }
    }
  }

  fn resolve_type_ref(&self, name: &str) -> Option<DefId> {
    self.globals.lookup(name).and_then(|defs| {
      defs
        .iter()
        .find(|d| d.file_id == self.file_id)
        .copied()
        .or_else(|| defs.first().copied())
    })
  }

  fn lower_mapped_type(&mut self, mapped: &Node<TypeMapped>) -> TypeId {
    let constraint = self.lower_type_expr(&mapped.stx.constraint);
    let value = self.lower_type_expr(&mapped.stx.type_expr);
    let name_type = mapped
      .stx
      .name_type
      .as_ref()
      .map(|t| self.lower_type_expr(t));
    let mapped_type = MappedType {
      type_param: mapped.stx.type_parameter.clone(),
      constraint,
      name_type,
      value,
      optional_modifier: mapped
        .stx
        .optional_modifier
        .map(|m| matches!(m, MappedTypeModifier::Plus)),
      readonly_modifier: mapped
        .stx
        .readonly_modifier
        .map(|m| matches!(m, MappedTypeModifier::Plus)),
    };
    self.store.intern(TypeKind::Mapped(mapped_type))
  }

  fn lower_template_literal(&mut self, template: &Node<TypeTemplateLiteral>) -> TypeId {
    let spans = template
      .stx
      .spans
      .iter()
      .map(|span| TemplateLiteralSpan {
        type_id: self.lower_type_expr(&span.stx.type_expr),
        literal: span.stx.literal.clone(),
      })
      .collect();
    let tpl = TemplateLiteralType {
      head: template.stx.head.clone(),
      spans,
    };
    self.store.intern(TypeKind::TemplateLiteral(tpl))
  }

  fn lower_type_params(&mut self, params: &Option<Vec<Node<TypeParameter>>>) -> Vec<String> {
    params
      .as_ref()
      .map(|params| params.iter().map(|p| p.stx.name.clone()).collect())
      .unwrap_or_default()
  }

  fn lower_param_decl(&mut self, param: &Node<ParamDecl>) -> FnParam {
    let name = match &*param.stx.pattern.stx.pat.stx {
      parse_js::ast::expr::pat::Pat::Id(id) => Some(id.stx.name.clone()),
      _ => None,
    };
    let ty = param
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.lower_type_expr(t))
      .unwrap_or_else(|| self.store.unknown());
    FnParam {
      name,
      ty,
      optional: param.stx.optional,
      rest: param.stx.rest,
    }
  }

  fn property_name(&self, key: &TypePropertyKey) -> Option<String> {
    match key {
      TypePropertyKey::Identifier(id) => Some(id.clone()),
      TypePropertyKey::String(s) => Some(s.clone()),
      TypePropertyKey::Number(n) => Some(n.clone()),
      TypePropertyKey::Computed(_) => None,
    }
  }

  fn class_member_name(
    &self,
    key: &parse_js::ast::class_or_object::ClassOrObjKey,
  ) -> Option<String> {
    match key {
      parse_js::ast::class_or_object::ClassOrObjKey::Direct(direct) => Some(direct.stx.key.clone()),
      parse_js::ast::class_or_object::ClassOrObjKey::Computed(_) => None,
    }
  }

  fn unsupported(&self, code: &'static str, message: impl Into<String>, loc: Loc) {
    self.program.push_diagnostic(Diagnostic::unsupported(
      code,
      message.into(),
      crate::Span::new(self.file_id, loc),
    ));
  }
}
