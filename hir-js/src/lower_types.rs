use crate::hir::ClassMemberAccessibility;
use crate::hir::ClassMemberSig;
use crate::hir::ClassMemberSigKind;
use crate::hir::ConditionalType;
use crate::hir::DefTypeInfo;
use crate::hir::EnumMemberInfo;
use crate::hir::EnumMemberValue;
use crate::hir::PropertyName;
use crate::hir::TypeArenas;
use crate::hir::TypeArray;
use crate::hir::TypeExpr as HirTypeExpr;
use crate::hir::TypeExprKind;
use crate::hir::TypeFnParam;
use crate::hir::TypeFunction as HirTypeFunction;
use crate::hir::TypeGetterSignature;
use crate::hir::TypeImport as HirTypeImport;
use crate::hir::TypeImportName;
use crate::hir::TypeIndexSignature as HirTypeIndexSignature;
use crate::hir::TypeLiteral as HirTypeLiteral;
use crate::hir::TypeLiteralType;
use crate::hir::TypeMapped as HirTypeMapped;
use crate::hir::TypeMappedModifier;
use crate::hir::TypeMember as HirTypeMember;
use crate::hir::TypeMemberKind;
use crate::hir::TypeMethodSignature as HirTypeMethodSignature;
use crate::hir::TypeName;
use crate::hir::TypeParam;
use crate::hir::TypePredicate as HirTypePredicate;
use crate::hir::TypePropertySignature as HirTypePropertySignature;
use crate::hir::TypeRef;
use crate::hir::TypeSetterSignature;
use crate::hir::TypeSignature as HirTypeSignature;
use crate::hir::TypeTemplateLiteral as HirTypeTemplateLiteral;
use crate::hir::TypeTemplateLiteralSpan as HirTypeTemplateLiteralSpan;
use crate::hir::TypeTuple;
use crate::hir::TypeTupleElement;
use crate::hir::TypeVariance;
use crate::ids::DefId;
use crate::ids::NameId;
use crate::ids::TypeExprId;
use crate::ids::TypeMemberId;
use crate::ids::TypeParamId;
use crate::intern::NameInterner;
use crate::lower::LoweringContext;
use crate::span_map::SpanMap;
use diagnostics::TextRange;
use parse_js::ast::class_or_object::*;
use parse_js::ast::expr::ClassExpr as AstClassExpr;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::ImportExpr;
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ClassDecl, ParamDecl};
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::ast::ts_stmt::{AmbientClassDecl, EnumDecl};
use parse_js::ast::type_expr::*;
use parse_js::token::TT;
use std::collections::{HashMap, HashSet};

pub(crate) struct TypeLowerer<'a> {
  arenas: &'a mut TypeArenas,
  owner: DefId,
  names: &'a mut NameInterner,
  span_map: &'a mut SpanMap,
  ctx: &'a mut LoweringContext,
}

impl<'a> TypeLowerer<'a> {
  pub fn new(
    owner: DefId,
    arenas: &'a mut TypeArenas,
    names: &'a mut NameInterner,
    span_map: &'a mut SpanMap,
    ctx: &'a mut LoweringContext,
  ) -> Self {
    Self {
      arenas,
      owner,
      names,
      span_map,
      ctx,
    }
  }

  pub fn lower_type_alias(&mut self, decl: &Node<TypeAliasDecl>) -> DefTypeInfo {
    let type_params = self.lower_type_params(decl.stx.type_parameters.as_deref());
    let type_expr = self.lower_type_expr(&decl.stx.type_expr);
    DefTypeInfo::TypeAlias {
      type_expr,
      type_params,
    }
  }

  pub fn lower_interface(&mut self, decl: &Node<InterfaceDecl>) -> DefTypeInfo {
    let type_params = self.lower_type_params(decl.stx.type_parameters.as_deref());
    let extends = decl
      .stx
      .extends
      .iter()
      .map(|ty| self.lower_type_expr(ty))
      .collect();
    let members = self.lower_type_members(&decl.stx.members);
    DefTypeInfo::Interface {
      type_params,
      extends,
      members,
    }
  }

  pub fn lower_class_decl(&mut self, decl: &Node<ClassDecl>) -> DefTypeInfo {
    let type_params = self.lower_type_params(decl.stx.type_parameters.as_deref());
    let extends = decl
      .stx
      .extends
      .as_ref()
      .map(|base| self.lower_heritage_expr(base));
    let implements = decl
      .stx
      .implements
      .iter()
      .map(|imp| self.lower_heritage_expr(imp))
      .collect();
    let members = self.lower_class_members(&decl.stx.members);
    DefTypeInfo::Class {
      type_params,
      extends,
      implements,
      members,
    }
  }

  pub fn lower_class_expr(&mut self, expr: &Node<AstClassExpr>) -> DefTypeInfo {
    let type_params = self.lower_type_params(expr.stx.type_parameters.as_deref());
    let extends = expr
      .stx
      .extends
      .as_ref()
      .map(|base| self.lower_heritage_expr(base));
    let implements = expr
      .stx
      .implements
      .iter()
      .map(|imp| self.lower_type_expr(imp))
      .collect();
    let members = self.lower_class_members(&expr.stx.members);
    DefTypeInfo::Class {
      type_params,
      extends,
      implements,
      members,
    }
  }

  pub fn lower_ambient_class(&mut self, decl: &Node<AmbientClassDecl>) -> DefTypeInfo {
    let type_params = self.lower_type_params(decl.stx.type_parameters.as_deref());
    let extends = decl
      .stx
      .extends
      .as_ref()
      .map(|base| self.lower_type_expr(base));
    let implements = decl
      .stx
      .implements
      .iter()
      .map(|imp| self.lower_type_expr(imp))
      .collect();
    let members = self.lower_type_member_signatures(&decl.stx.members);
    DefTypeInfo::Class {
      type_params,
      extends,
      implements,
      members,
    }
  }

  pub fn lower_enum(&mut self, decl: &Node<EnumDecl>) -> DefTypeInfo {
    let members = decl
      .stx
      .members
      .iter()
      .map(|member| self.lower_enum_member(member))
      .collect();
    DefTypeInfo::Enum { members }
  }

  pub fn lower_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeExprId {
    let span = self.ctx.to_range(expr.loc);
    let kind = match &*expr.stx {
      TypeExpr::Any(_) => TypeExprKind::Any,
      TypeExpr::Unknown(_) => TypeExprKind::Unknown,
      TypeExpr::Never(_) => TypeExprKind::Never,
      TypeExpr::Void(_) => TypeExprKind::Void,
      TypeExpr::String(_) => TypeExprKind::String,
      TypeExpr::Number(_) => TypeExprKind::Number,
      TypeExpr::Boolean(_) => TypeExprKind::Boolean,
      TypeExpr::BigInt(_) => TypeExprKind::BigInt,
      TypeExpr::Symbol(_) => TypeExprKind::Symbol,
      TypeExpr::UniqueSymbol(_) => TypeExprKind::UniqueSymbol,
      TypeExpr::Object(_) => TypeExprKind::Object,
      TypeExpr::Null(_) => TypeExprKind::Null,
      TypeExpr::Undefined(_) => TypeExprKind::Undefined,
      TypeExpr::ThisType(_) => TypeExprKind::This,
      TypeExpr::TypeReference(reference) => {
        let type_args = reference
          .stx
          .type_arguments
          .as_ref()
          .map(|args| args.iter().map(|arg| self.lower_type_expr(arg)).collect())
          .unwrap_or_default();
        TypeExprKind::TypeRef(TypeRef {
          name: self.lower_entity_name(&reference.stx.name),
          type_args,
        })
      }
      TypeExpr::LiteralType(lit) => TypeExprKind::Literal(self.lower_literal(&lit.stx)),
      TypeExpr::ArrayType(arr) => {
        let element = self.lower_type_expr(&arr.stx.element_type);
        TypeExprKind::Array(TypeArray {
          readonly: arr.stx.readonly,
          element,
        })
      }
      TypeExpr::TupleType(tuple) => {
        let elements = tuple
          .stx
          .elements
          .iter()
          .map(|el| TypeTupleElement {
            label: el.stx.label.as_ref().map(|l| self.names.intern(l)),
            optional: el.stx.optional,
            rest: el.stx.rest,
            ty: self.lower_type_expr(&el.stx.type_expr),
          })
          .collect();
        TypeExprKind::Tuple(TypeTuple {
          readonly: tuple.stx.readonly,
          elements,
        })
      }
      TypeExpr::UnionType(union) => {
        let members = union
          .stx
          .types
          .iter()
          .map(|t| self.lower_type_expr(t))
          .collect();
        TypeExprKind::Union(self.canonicalize_union(members))
      }
      TypeExpr::IntersectionType(inter) => {
        let members = inter
          .stx
          .types
          .iter()
          .map(|t| self.lower_type_expr(t))
          .collect();
        TypeExprKind::Intersection(self.canonicalize_intersection(members))
      }
      TypeExpr::FunctionType(func) => TypeExprKind::Function(self.lower_function_like(
        func.stx.type_parameters.as_ref(),
        &func.stx.parameters,
        &func.stx.return_type,
      )),
      TypeExpr::ConstructorType(func) => TypeExprKind::Constructor(self.lower_function_like(
        func.stx.type_parameters.as_ref(),
        &func.stx.parameters,
        &func.stx.return_type,
      )),
      TypeExpr::ObjectType(obj) => {
        let members = self.lower_type_members(&obj.stx.members);
        TypeExprKind::TypeLiteral(TypeLiteralType { members })
      }
      TypeExpr::ParenthesizedType(par) => {
        TypeExprKind::Parenthesized(self.lower_type_expr(&par.stx.type_expr))
      }
      TypeExpr::TypeQuery(query) => {
        TypeExprKind::TypeQuery(self.lower_entity_name(&query.stx.expr_name))
      }
      TypeExpr::KeyOfType(keyof) => TypeExprKind::KeyOf(self.lower_type_expr(&keyof.stx.type_expr)),
      TypeExpr::IndexedAccessType(index) => TypeExprKind::IndexedAccess {
        object_type: self.lower_type_expr(&index.stx.object_type),
        index_type: self.lower_type_expr(&index.stx.index_type),
      },
      TypeExpr::ConditionalType(cond) => TypeExprKind::Conditional(ConditionalType {
        check_type: self.lower_type_expr(&cond.stx.check_type),
        extends_type: self.lower_type_expr(&cond.stx.extends_type),
        true_type: self.lower_type_expr(&cond.stx.true_type),
        false_type: self.lower_type_expr(&cond.stx.false_type),
      }),
      TypeExpr::InferType(infer) => {
        TypeExprKind::Infer(self.lower_infer_type_param(&infer.stx.type_parameter, infer))
      }
      TypeExpr::MappedType(mapped) => TypeExprKind::Mapped(self.lower_mapped_type(mapped)),
      TypeExpr::TemplateLiteralType(tmpl) => {
        TypeExprKind::TemplateLiteral(self.lower_template_literal(tmpl))
      }
      TypeExpr::TypePredicate(pred) => TypeExprKind::TypePredicate(self.lower_type_predicate(pred)),
      TypeExpr::ImportType(import) => TypeExprKind::Import(self.lower_import_type(import)),
    };

    self.alloc_type_expr(span, kind)
  }

  fn alloc_type_expr(&mut self, span: TextRange, kind: TypeExprKind) -> TypeExprId {
    let id = TypeExprId(self.arenas.type_exprs.len() as u32);
    self.arenas.type_exprs.push(HirTypeExpr { span, kind });
    self.span_map.add_type_expr(span, self.owner, id);
    id
  }

  fn alloc_type_member(&mut self, span: TextRange, kind: TypeMemberKind) -> TypeMemberId {
    let id = TypeMemberId(self.arenas.type_members.len() as u32);
    self.arenas.type_members.push(HirTypeMember { span, kind });
    self.span_map.add_type_member(span, self.owner, id);
    id
  }

  fn alloc_type_param(&mut self, param: TypeParam) -> TypeParamId {
    let id = TypeParamId(self.arenas.type_params.len() as u32);
    let span = param.span;
    self.arenas.type_params.push(param);
    self.span_map.add_type_param(span, self.owner, id);
    id
  }

  fn lower_literal(&mut self, lit: &TypeLiteral) -> HirTypeLiteral {
    match lit {
      TypeLiteral::String(s) => HirTypeLiteral::String(s.clone()),
      TypeLiteral::Number(n) => HirTypeLiteral::Number(n.clone()),
      TypeLiteral::BigInt(n) => HirTypeLiteral::BigInt(n.clone()),
      TypeLiteral::Boolean(b) => HirTypeLiteral::Boolean(*b),
      TypeLiteral::Null => HirTypeLiteral::Null,
    }
  }

  fn lower_entity_name(&mut self, name: &TypeEntityName) -> TypeName {
    match self.lower_entity_name_parts(name) {
      LoweredEntityName::Path(mut path) => {
        if path.len() == 1 {
          TypeName::Ident(path.pop().unwrap())
        } else {
          TypeName::Qualified(path)
        }
      }
      LoweredEntityName::Import(import) => TypeName::Import(import),
    }
  }

  fn lower_entity_name_parts(&mut self, name: &TypeEntityName) -> LoweredEntityName {
    match name {
      TypeEntityName::Identifier(id) => LoweredEntityName::Path(vec![self.names.intern(id)]),
      TypeEntityName::Import(import_expr) => LoweredEntityName::Import(TypeImportName {
        module: self.import_module_specifier(import_expr),
        qualifier: None,
      }),
      TypeEntityName::Qualified(qualified) => {
        let right = self.names.intern(&qualified.right);
        match self.lower_entity_name_parts(&qualified.left) {
          LoweredEntityName::Path(mut path) => {
            path.push(right);
            LoweredEntityName::Path(path)
          }
          LoweredEntityName::Import(mut import) => {
            let mut qualifier = import.qualifier.take().unwrap_or_default();
            qualifier.push(right);
            import.qualifier = Some(qualifier);
            LoweredEntityName::Import(import)
          }
        }
      }
    }
  }

  fn import_module_specifier(&self, import: &Node<ImportExpr>) -> Option<String> {
    match &*import.stx.module.stx {
      Expr::LitStr(lit) => Some(lit.stx.value.clone()),
      _ => None,
    }
  }

  fn lower_function_like(
    &mut self,
    type_params: Option<&Vec<Node<TypeParameter>>>,
    params: &[Node<TypeFunctionParameter>],
    ret: &Node<TypeExpr>,
  ) -> HirTypeFunction {
    let type_params = self.lower_type_params(type_params.map(|v| v.as_slice()));
    let params = params
      .iter()
      .map(|p| self.lower_function_param(p))
      .collect();
    let ret = self.lower_type_expr(ret);
    HirTypeFunction {
      type_params,
      params,
      ret,
    }
  }

  fn lower_function_param(&mut self, param: &Node<TypeFunctionParameter>) -> TypeFnParam {
    TypeFnParam {
      name: param.stx.name.as_ref().map(|n| self.names.intern(n)),
      ty: self.lower_type_expr(&param.stx.type_expr),
      optional: param.stx.optional,
      rest: param.stx.rest,
    }
  }

  fn lower_type_params(&mut self, params: Option<&[Node<TypeParameter>]>) -> Vec<TypeParamId> {
    params
      .map(|params| {
        params
          .iter()
          .map(|p| self.lower_type_param(p, false))
          .collect()
      })
      .unwrap_or_default()
  }

  fn lower_type_param(&mut self, param: &Node<TypeParameter>, is_infer: bool) -> TypeParamId {
    let span = self.ctx.to_range(param.loc);
    let constraint = param
      .stx
      .constraint
      .as_ref()
      .map(|c| self.lower_type_expr(c));
    let default = param.stx.default.as_ref().map(|d| self.lower_type_expr(d));
    let variance = param.stx.variance.map(|v| match v {
      Variance::In => TypeVariance::In,
      Variance::Out => TypeVariance::Out,
      Variance::InOut => TypeVariance::InOut,
    });
    let param = TypeParam {
      span,
      name: self.names.intern(&param.stx.name),
      constraint,
      default,
      variance,
      const_: param.stx.const_,
      is_infer,
    };
    self.alloc_type_param(param)
  }

  fn lower_infer_type_param(&mut self, name: &str, infer: &Node<TypeInfer>) -> TypeParamId {
    let span = self.ctx.to_range(infer.loc);
    let constraint = infer
      .stx
      .constraint
      .as_ref()
      .map(|c| self.lower_type_expr(c));
    let param = TypeParam {
      span,
      name: self.names.intern(name),
      constraint,
      default: None,
      variance: None,
      const_: false,
      is_infer: true,
    };
    self.alloc_type_param(param)
  }

  fn lower_class_members(&mut self, members: &[Node<ClassMember>]) -> Vec<ClassMemberSig> {
    let mut lowered = Vec::new();
    for member in members.iter() {
      let span = self.ctx.to_range(member.loc);
      let accessibility = self.lower_member_accessibility(member.stx.accessibility);
      let static_ = member.stx.static_;
      let readonly = member.stx.readonly;
      let optional = member.stx.optional;
      match &member.stx.val {
        ClassOrObjVal::Prop(_) => {
          let name = self.lower_class_member_name(&member.stx.key);
          let type_annotation = member
            .stx
            .type_annotation
            .as_ref()
            .map(|ty| self.lower_type_expr(ty));
          lowered.push(ClassMemberSig {
            span,
            static_,
            accessibility,
            readonly,
            optional,
            kind: ClassMemberSigKind::Field {
              name,
              type_annotation,
            },
          });
        }
        ClassOrObjVal::Method(method) => {
          let signature = self.lower_method_signature_from_func(&method.stx.func);
          let name = self.lower_class_member_name(&member.stx.key);
          let is_constructor = !static_ && self.is_constructor_name(&name);
          let kind = if is_constructor {
            // Parameter properties declared via constructor parameters (e.g.
            // `constructor(public x: string)`) act like instance fields. Model
            // them as additional field signatures so downstream consumers can
            // type-check `x` without re-reading the AST.
            for param in method.stx.func.stx.parameters.iter() {
              if param.stx.accessibility.is_none() && !param.stx.readonly {
                continue;
              }
              let Some(name) = (match &*param.stx.pattern.stx.pat.stx {
                parse_js::ast::expr::pat::Pat::Id(id) => Some(self.names.intern(&id.stx.name)),
                _ => None,
              }) else {
                continue;
              };
              let span = self.ctx.to_range(param.loc);
              let type_annotation = param
                .stx
                .type_annotation
                .as_ref()
                .map(|ty| self.lower_type_expr(ty));
              lowered.push(ClassMemberSig {
                span,
                static_: false,
                accessibility: self.lower_member_accessibility(param.stx.accessibility),
                readonly: param.stx.readonly,
                optional: param.stx.optional,
                kind: ClassMemberSigKind::Field {
                  name: PropertyName::Ident(name),
                  type_annotation,
                },
              });
            }
            ClassMemberSigKind::Constructor(signature)
          } else {
            ClassMemberSigKind::Method { name, signature }
          };
          lowered.push(ClassMemberSig {
            span,
            static_,
            accessibility,
            readonly,
            optional,
            kind,
          });
        }
        ClassOrObjVal::Getter(get) => {
          let name = self.lower_class_member_name(&member.stx.key);
          let return_type = get
            .stx
            .func
            .stx
            .return_type
            .as_ref()
            .map(|ret| self.lower_type_expr(ret));
          lowered.push(ClassMemberSig {
            span,
            static_,
            accessibility,
            readonly,
            optional,
            kind: ClassMemberSigKind::Getter { name, return_type },
          });
        }
        ClassOrObjVal::Setter(set) => {
          let name = self.lower_class_member_name(&member.stx.key);
          let parameter = set
            .stx
            .func
            .stx
            .parameters
            .get(0)
            .map(|param| self.lower_param_decl(param))
            .unwrap_or_else(|| TypeFnParam {
              name: None,
              ty: self.alloc_type_expr(span, TypeExprKind::Any),
              optional: false,
              rest: false,
            });
          lowered.push(ClassMemberSig {
            span,
            static_,
            accessibility,
            readonly,
            optional,
            kind: ClassMemberSigKind::Setter { name, parameter },
          });
        }
        ClassOrObjVal::IndexSignature(sig) => {
          let signature = self.lower_class_index_signature(sig, readonly);
          lowered.push(ClassMemberSig {
            span,
            static_,
            accessibility,
            readonly,
            optional,
            kind: ClassMemberSigKind::IndexSignature(signature),
          });
        }
        ClassOrObjVal::StaticBlock(_) => {}
      }
    }
    lowered
  }

  fn lower_type_member_signatures(&mut self, members: &[Node<TypeMember>]) -> Vec<ClassMemberSig> {
    let mut lowered = Vec::new();
    for member in members.iter() {
      let span = self.ctx.to_range(member.loc);
      match &*member.stx {
        TypeMember::Property(prop) => {
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: prop.stx.readonly,
            optional: prop.stx.optional,
            kind: ClassMemberSigKind::Field {
              name: self.lower_property_name(&prop.stx.key),
              type_annotation: prop
                .stx
                .type_annotation
                .as_ref()
                .map(|t| self.lower_type_expr(t)),
            },
          });
        }
        TypeMember::Method(method) => {
          let signature = self.lower_method_signature(method);
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: false,
            optional: method.stx.optional,
            kind: ClassMemberSigKind::Method {
              name: self.lower_property_name(&method.stx.key),
              signature: HirTypeSignature {
                type_params: signature.type_params,
                params: signature.params,
                return_type: signature.return_type,
              },
            },
          });
        }
        TypeMember::Constructor(cons) => {
          let signature = self.lower_type_signature(
            cons.stx.type_parameters.as_deref(),
            &cons.stx.parameters,
            cons.stx.return_type.as_ref(),
          );
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: false,
            optional: false,
            kind: ClassMemberSigKind::Constructor(signature),
          });
        }
        TypeMember::CallSignature(call) => {
          let signature = self.lower_type_signature(
            call.stx.type_parameters.as_deref(),
            &call.stx.parameters,
            call.stx.return_type.as_ref(),
          );
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: false,
            optional: false,
            kind: ClassMemberSigKind::CallSignature(signature),
          });
        }
        TypeMember::IndexSignature(sig) => {
          let signature = self.lower_index_signature(sig);
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: sig.stx.readonly,
            optional: false,
            kind: ClassMemberSigKind::IndexSignature(signature),
          });
        }
        TypeMember::GetAccessor(get) => {
          let sig = self.lower_get_accessor(get);
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: false,
            optional: false,
            kind: ClassMemberSigKind::Getter {
              name: sig.name,
              return_type: sig.return_type,
            },
          });
        }
        TypeMember::SetAccessor(set) => {
          let sig = self.lower_set_accessor(set);
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: false,
            optional: false,
            kind: ClassMemberSigKind::Setter {
              name: sig.name,
              parameter: sig.parameter,
            },
          });
        }
        TypeMember::MappedProperty(mapped) => {
          let mapped = self.lower_mapped_type(mapped);
          let mapped_id = self.alloc_type_expr(span, TypeExprKind::Mapped(mapped));
          lowered.push(ClassMemberSig {
            span,
            static_: false,
            accessibility: None,
            readonly: false,
            optional: false,
            kind: ClassMemberSigKind::Field {
              name: PropertyName::Computed,
              type_annotation: Some(mapped_id),
            },
          });
        }
      }
    }
    lowered
  }

  fn lower_enum_member(
    &mut self,
    member: &Node<parse_js::ast::ts_stmt::EnumMember>,
  ) -> EnumMemberInfo {
    let name = self.names.intern(&member.stx.name);
    let span = self.ctx.to_range(member.loc);
    let value = match &member.stx.initializer {
      Some(init) => match &*init.stx {
        AstExpr::LitNum(_) => EnumMemberValue::Number,
        AstExpr::LitStr(_) => EnumMemberValue::String,
        _ => EnumMemberValue::Computed,
      },
      None => EnumMemberValue::Number,
    };
    EnumMemberInfo { name, span, value }
  }

  fn lower_member_accessibility(
    &self,
    accessibility: Option<parse_js::ast::stmt::decl::Accessibility>,
  ) -> Option<ClassMemberAccessibility> {
    accessibility.map(|acc| match acc {
      parse_js::ast::stmt::decl::Accessibility::Public => ClassMemberAccessibility::Public,
      parse_js::ast::stmt::decl::Accessibility::Protected => ClassMemberAccessibility::Protected,
      parse_js::ast::stmt::decl::Accessibility::Private => ClassMemberAccessibility::Private,
    })
  }

  fn lower_class_member_name(&mut self, key: &ClassOrObjKey) -> PropertyName {
    match key {
      ClassOrObjKey::Direct(direct) => match direct.stx.tt {
        TT::LiteralString | TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd => {
          PropertyName::String(direct.stx.key.clone())
        }
        TT::LiteralNumber | TT::LiteralNumberBin | TT::LiteralNumberHex | TT::LiteralNumberOct => {
          PropertyName::Number(direct.stx.key.clone())
        }
        _ => PropertyName::Ident(self.names.intern(&direct.stx.key)),
      },
      ClassOrObjKey::Computed(_) => PropertyName::Computed,
    }
  }

  fn lower_method_signature_from_func(&mut self, func: &Node<Func>) -> HirTypeSignature {
    let type_params = self.lower_type_params(func.stx.type_parameters.as_deref());
    let params = func
      .stx
      .parameters
      .iter()
      .map(|p| self.lower_param_decl(p))
      .collect();
    let return_type = func
      .stx
      .return_type
      .as_ref()
      .map(|ret| self.lower_type_expr(ret));
    HirTypeSignature {
      type_params,
      params,
      return_type,
    }
  }

  fn lower_param_decl(&mut self, param: &Node<ParamDecl>) -> TypeFnParam {
    let name = match &*param.stx.pattern.stx.pat.stx {
      parse_js::ast::expr::pat::Pat::Id(id) => Some(self.names.intern(&id.stx.name)),
      _ => None,
    };
    let ty = if let Some(annotation) = param.stx.type_annotation.as_ref() {
      self.lower_type_expr(annotation)
    } else {
      let span = self.ctx.to_range(param.loc);
      self.alloc_type_expr(span, TypeExprKind::Any)
    };
    TypeFnParam {
      name,
      ty,
      optional: param.stx.optional,
      rest: param.stx.rest,
    }
  }

  fn lower_class_index_signature(
    &mut self,
    sig: &Node<ClassIndexSignature>,
    readonly: bool,
  ) -> HirTypeIndexSignature {
    HirTypeIndexSignature {
      readonly,
      parameter_name: self.names.intern(&sig.stx.parameter_name),
      parameter_type: self.lower_type_expr(&sig.stx.parameter_type),
      type_annotation: self.lower_type_expr(&sig.stx.type_annotation),
    }
  }

  fn lower_heritage_expr(&mut self, expr: &Node<AstExpr>) -> TypeExprId {
    let span = self.ctx.to_range(expr.loc);
    if let Some(name) = self.type_name_from_expr(expr) {
      self.alloc_type_expr(
        span,
        TypeExprKind::TypeRef(TypeRef {
          name,
          type_args: Vec::new(),
        }),
      )
    } else {
      self.warn_heritage(
        span,
        "heritage clause expression could not be lowered; using `any`",
      );
      self.alloc_type_expr(span, TypeExprKind::Any)
    }
  }

  fn type_name_from_expr(&mut self, expr: &Node<AstExpr>) -> Option<TypeName> {
    match &*expr.stx {
      AstExpr::Id(id) => Some(TypeName::Ident(self.names.intern(&id.stx.name))),
      AstExpr::Member(member) if !member.stx.optional_chaining => {
        let mut parts = Vec::new();
        if self.collect_member_path(&member.stx.left, &mut parts) {
          parts.push(self.names.intern(&member.stx.right));
          if parts.len() == 1 {
            Some(TypeName::Ident(parts[0]))
          } else {
            Some(TypeName::Qualified(parts))
          }
        } else {
          None
        }
      }
      _ => None,
    }
  }

  fn collect_member_path(&mut self, expr: &Node<AstExpr>, acc: &mut Vec<NameId>) -> bool {
    match &*expr.stx {
      AstExpr::Id(id) => {
        acc.push(self.names.intern(&id.stx.name));
        true
      }
      AstExpr::Member(member) if !member.stx.optional_chaining => {
        if !self.collect_member_path(&member.stx.left, acc) {
          return false;
        }
        acc.push(self.names.intern(&member.stx.right));
        true
      }
      _ => false,
    }
  }

  fn warn_heritage(&mut self, range: TextRange, message: impl Into<String>) {
    self.ctx.warn("LOWER0003", message, range);
  }

  fn is_constructor_name(&self, name: &PropertyName) -> bool {
    match name {
      PropertyName::Ident(id) => self.names.resolve(*id) == Some("constructor"),
      _ => false,
    }
  }

  fn lower_type_members(&mut self, members: &[Node<TypeMember>]) -> Vec<TypeMemberId> {
    let mut lowered: Vec<TypeMemberId> = members
      .iter()
      .map(|member| {
        let span = self.ctx.to_range(member.loc);
        let kind = match &*member.stx {
          TypeMember::Property(prop) => {
            TypeMemberKind::Property(self.lower_property_signature(prop))
          }
          TypeMember::Method(method) => TypeMemberKind::Method(self.lower_method_signature(method)),
          TypeMember::Constructor(cons) => TypeMemberKind::Constructor(self.lower_type_signature(
            cons.stx.type_parameters.as_deref(),
            &cons.stx.parameters,
            cons.stx.return_type.as_ref(),
          )),
          TypeMember::CallSignature(call) => {
            TypeMemberKind::CallSignature(self.lower_type_signature(
              call.stx.type_parameters.as_deref(),
              &call.stx.parameters,
              call.stx.return_type.as_ref(),
            ))
          }
          TypeMember::IndexSignature(sig) => {
            TypeMemberKind::IndexSignature(self.lower_index_signature(sig))
          }
          TypeMember::GetAccessor(get) => TypeMemberKind::Getter(self.lower_get_accessor(get)),
          TypeMember::SetAccessor(set) => TypeMemberKind::Setter(self.lower_set_accessor(set)),
          TypeMember::MappedProperty(mapped) => {
            TypeMemberKind::Mapped(self.lower_mapped_type(mapped))
          }
        };
        self.alloc_type_member(span, kind)
      })
      .collect();

    lowered.sort_by(|a, b| {
      let a_member = &self.arenas.type_members[a.0 as usize];
      let b_member = &self.arenas.type_members[b.0 as usize];
      self
        .member_sort_key(a_member)
        .cmp(&self.member_sort_key(b_member))
    });
    lowered
  }

  fn member_sort_key(&self, member: &HirTypeMember) -> (String, u8) {
    let (name, variant) = match &member.kind {
      TypeMemberKind::Property(prop) => (self.property_name_key(&prop.name), 0),
      TypeMemberKind::Method(method) => (self.property_name_key(&method.name), 1),
      TypeMemberKind::Getter(get) => (self.property_name_key(&get.name), 2),
      TypeMemberKind::Setter(set) => (self.property_name_key(&set.name), 3),
      TypeMemberKind::CallSignature(_) => ("()".to_string(), 4),
      TypeMemberKind::Constructor(_) => ("new".to_string(), 5),
      TypeMemberKind::IndexSignature(_) => ("[]".to_string(), 6),
      TypeMemberKind::Mapped(_) => ("[mapped]".to_string(), 7),
    };
    (name, variant)
  }

  fn property_name_key(&self, name: &PropertyName) -> String {
    match name {
      PropertyName::Ident(id) => self.names.resolve(*id).unwrap_or("").to_string(),
      PropertyName::String(s) => s.clone(),
      PropertyName::Number(n) => n.clone(),
      PropertyName::Computed => "[computed]".to_string(),
    }
  }

  fn lower_property_signature(
    &mut self,
    sig: &Node<TypePropertySignature>,
  ) -> HirTypePropertySignature {
    HirTypePropertySignature {
      readonly: sig.stx.readonly,
      optional: sig.stx.optional,
      name: self.lower_property_name(&sig.stx.key),
      type_annotation: sig
        .stx
        .type_annotation
        .as_ref()
        .map(|t| self.lower_type_expr(t)),
    }
  }

  fn lower_method_signature(&mut self, sig: &Node<TypeMethodSignature>) -> HirTypeMethodSignature {
    let type_params = self.lower_type_params(sig.stx.type_parameters.as_deref());
    let params = sig
      .stx
      .parameters
      .iter()
      .map(|p| self.lower_function_param(p))
      .collect();
    let return_type = sig
      .stx
      .return_type
      .as_ref()
      .map(|t| self.lower_type_expr(t));
    HirTypeMethodSignature {
      optional: sig.stx.optional,
      name: self.lower_property_name(&sig.stx.key),
      type_params,
      params,
      return_type,
    }
  }

  fn lower_type_signature(
    &mut self,
    type_params: Option<&[Node<TypeParameter>]>,
    params: &[Node<TypeFunctionParameter>],
    return_type: Option<&Node<TypeExpr>>,
  ) -> HirTypeSignature {
    let type_params = self.lower_type_params(type_params);
    let params = params
      .iter()
      .map(|p| self.lower_function_param(p))
      .collect();
    let return_type = return_type.map(|ret| self.lower_type_expr(ret));
    HirTypeSignature {
      type_params,
      params,
      return_type,
    }
  }

  fn lower_index_signature(&mut self, sig: &Node<TypeIndexSignature>) -> HirTypeIndexSignature {
    HirTypeIndexSignature {
      readonly: sig.stx.readonly,
      parameter_name: self.names.intern(&sig.stx.parameter_name),
      parameter_type: self.lower_type_expr(&sig.stx.parameter_type),
      type_annotation: self.lower_type_expr(&sig.stx.type_annotation),
    }
  }

  fn lower_get_accessor(&mut self, sig: &Node<TypeGetAccessor>) -> TypeGetterSignature {
    TypeGetterSignature {
      name: self.lower_property_name(&sig.stx.key),
      return_type: sig
        .stx
        .return_type
        .as_ref()
        .map(|t| self.lower_type_expr(t)),
    }
  }

  fn lower_set_accessor(&mut self, sig: &Node<TypeSetAccessor>) -> TypeSetterSignature {
    TypeSetterSignature {
      name: self.lower_property_name(&sig.stx.key),
      parameter: self.lower_function_param(&sig.stx.parameter),
    }
  }

  fn lower_property_name(&mut self, key: &TypePropertyKey) -> PropertyName {
    match key {
      TypePropertyKey::Identifier(id) => PropertyName::Ident(self.names.intern(id)),
      TypePropertyKey::String(s) => PropertyName::String(s.clone()),
      TypePropertyKey::Number(n) => PropertyName::Number(n.clone()),
      TypePropertyKey::Computed(_) => PropertyName::Computed,
    }
  }

  fn lower_mapped_type(&mut self, mapped: &Node<TypeMapped>) -> HirTypeMapped {
    let constraint = self.lower_type_expr(&mapped.stx.constraint);
    let type_param_name = self.names.intern(&mapped.stx.type_parameter);
    let type_param_span = self.ctx.to_range(mapped.loc);
    let type_param = self.alloc_type_param(TypeParam {
      span: type_param_span,
      name: type_param_name,
      constraint: Some(constraint),
      default: None,
      variance: None,
      const_: false,
      is_infer: false,
    });
    let name_type = mapped
      .stx
      .name_type
      .as_ref()
      .map(|n| self.lower_type_expr(n));
    let value_type = self.lower_type_expr(&mapped.stx.type_expr);
    HirTypeMapped {
      type_param,
      constraint,
      name_type,
      value_type,
      readonly: mapped
        .stx
        .readonly_modifier
        .map(Self::lower_mapped_modifier),
      optional: mapped
        .stx
        .optional_modifier
        .map(Self::lower_mapped_modifier),
    }
  }

  fn lower_mapped_modifier(modifier: MappedTypeModifier) -> TypeMappedModifier {
    match modifier {
      MappedTypeModifier::Plus => TypeMappedModifier::Plus,
      MappedTypeModifier::Minus => TypeMappedModifier::Minus,
      MappedTypeModifier::None => TypeMappedModifier::None,
    }
  }

  fn lower_template_literal(&mut self, tmpl: &Node<TypeTemplateLiteral>) -> HirTypeTemplateLiteral {
    let spans = tmpl
      .stx
      .spans
      .iter()
      .map(|span| HirTypeTemplateLiteralSpan {
        type_expr: self.lower_type_expr(&span.stx.type_expr),
        literal: span.stx.literal.clone(),
      })
      .collect();
    HirTypeTemplateLiteral {
      head: tmpl.stx.head.clone(),
      spans,
    }
  }

  fn lower_type_predicate(&mut self, pred: &Node<TypePredicate>) -> HirTypePredicate {
    HirTypePredicate {
      asserts: pred.stx.asserts,
      parameter: self.names.intern(&pred.stx.parameter_name),
      type_annotation: pred
        .stx
        .type_annotation
        .as_ref()
        .map(|t| self.lower_type_expr(t)),
    }
  }

  fn lower_import_type(&mut self, import: &Node<TypeImport>) -> HirTypeImport {
    let type_args = import
      .stx
      .type_arguments
      .as_ref()
      .map(|args| args.iter().map(|a| self.lower_type_expr(a)).collect())
      .unwrap_or_default();
    HirTypeImport {
      module: import.stx.module_specifier.clone(),
      qualifier: import
        .stx
        .qualifier
        .as_ref()
        .map(|q| self.lower_entity_name(q)),
      type_args,
    }
  }

  fn canonicalize_union(&self, members: Vec<TypeExprId>) -> Vec<TypeExprId> {
    self.canonicalize_type_set(members, |kind| match kind {
      TypeExprKind::Union(inner) => Some(inner),
      _ => None,
    })
  }

  fn canonicalize_intersection(&self, members: Vec<TypeExprId>) -> Vec<TypeExprId> {
    self.canonicalize_type_set(members, |kind| match kind {
      TypeExprKind::Intersection(inner) => Some(inner),
      _ => None,
    })
  }

  // Canonicalize a set of type expressions (union or intersection) with a stable,
  // semantic sort key so ordering does not depend on allocation order and obvious
  // duplicates can be removed.
  fn canonicalize_type_set(
    &self,
    members: Vec<TypeExprId>,
    nested: impl Fn(&TypeExprKind) -> Option<&Vec<TypeExprId>>,
  ) -> Vec<TypeExprId> {
    let mut flat = Vec::new();
    self.flatten_type_members(&members, &nested, &mut flat);

    let mut key_cache = HashMap::new();
    let mut in_progress = HashSet::new();
    let mut keyed: Vec<(TypeSortKey, TypeExprId)> = flat
      .into_iter()
      .map(|id| {
        (
          self.type_expr_sort_key(id, &mut key_cache, &mut in_progress),
          id,
        )
      })
      .collect();

    keyed.sort_by(|(ka, _), (kb, _)| ka.cmp(kb));
    keyed.dedup_by(|(ka, _), (kb, _)| ka == kb);
    keyed.into_iter().map(|(_, id)| id).collect()
  }

  fn flatten_type_members(
    &self,
    members: &[TypeExprId],
    nested: &impl Fn(&TypeExprKind) -> Option<&Vec<TypeExprId>>,
    out: &mut Vec<TypeExprId>,
  ) {
    for &member in members {
      if let Some(inner) = nested(&self.arenas.type_exprs[member.0 as usize].kind) {
        self.flatten_type_members(inner, nested, out);
      } else {
        out.push(member);
      }
    }
  }

  fn type_expr_sort_key(
    &self,
    id: TypeExprId,
    cache: &mut HashMap<TypeExprId, TypeSortKey>,
    in_progress: &mut HashSet<TypeExprId>,
  ) -> TypeSortKey {
    if let Some(cached) = cache.get(&id) {
      return cached.clone();
    }

    if !in_progress.insert(id) {
      let expr = &self.arenas.type_exprs[id.0 as usize];
      return TypeSortKey::Cycle {
        discriminant: self.type_kind_discriminant(&expr.kind),
        id: id.0,
      };
    }

    let expr = &self.arenas.type_exprs[id.0 as usize];
    let key = match &expr.kind {
      TypeExprKind::Any => TypeSortKey::Primitive("any"),
      TypeExprKind::Unknown => TypeSortKey::Primitive("unknown"),
      TypeExprKind::Never => TypeSortKey::Primitive("never"),
      TypeExprKind::Void => TypeSortKey::Primitive("void"),
      TypeExprKind::String => TypeSortKey::Primitive("string"),
      TypeExprKind::Number => TypeSortKey::Primitive("number"),
      TypeExprKind::Boolean => TypeSortKey::Primitive("boolean"),
      TypeExprKind::BigInt => TypeSortKey::Primitive("bigint"),
      TypeExprKind::Symbol => TypeSortKey::Primitive("symbol"),
      TypeExprKind::UniqueSymbol => TypeSortKey::Primitive("unique symbol"),
      TypeExprKind::Object => TypeSortKey::Primitive("object"),
      TypeExprKind::Null => TypeSortKey::Primitive("null"),
      TypeExprKind::Undefined => TypeSortKey::Primitive("undefined"),
      TypeExprKind::This => TypeSortKey::Primitive("this"),
      TypeExprKind::Literal(lit) => TypeSortKey::Literal(self.literal_sort_key(lit)),
      TypeExprKind::TypeRef(r) => TypeSortKey::TypeRef {
        name: self.type_name_sort_key(&r.name),
        type_args: r
          .type_args
          .iter()
          .map(|arg| self.type_expr_sort_key(*arg, cache, in_progress))
          .collect(),
      },
      TypeExprKind::Array(arr) => TypeSortKey::Array {
        readonly: arr.readonly,
        element: Box::new(self.type_expr_sort_key(arr.element, cache, in_progress)),
      },
      TypeExprKind::Tuple(tuple) => TypeSortKey::Tuple {
        readonly: tuple.readonly,
        elements: tuple
          .elements
          .iter()
          .map(|el| TupleElementKey {
            optional: el.optional,
            rest: el.rest,
            ty: self.type_expr_sort_key(el.ty, cache, in_progress),
          })
          .collect(),
      },
      TypeExprKind::Union(members) => {
        let mut member_keys: Vec<_> = members
          .iter()
          .map(|id| self.type_expr_sort_key(*id, cache, in_progress))
          .collect();
        member_keys.sort();
        member_keys.dedup();
        TypeSortKey::Union(member_keys)
      }
      TypeExprKind::Intersection(members) => {
        let mut member_keys: Vec<_> = members
          .iter()
          .map(|id| self.type_expr_sort_key(*id, cache, in_progress))
          .collect();
        member_keys.sort();
        member_keys.dedup();
        TypeSortKey::Intersection(member_keys)
      }
      TypeExprKind::Function(func) => TypeSortKey::Function(self.signature_sort_key(
        &func.type_params,
        &func.params,
        Some(func.ret),
        cache,
        in_progress,
      )),
      TypeExprKind::Constructor(func) => TypeSortKey::Constructor(self.signature_sort_key(
        &func.type_params,
        &func.params,
        Some(func.ret),
        cache,
        in_progress,
      )),
      TypeExprKind::TypeLiteral(lit) => TypeSortKey::TypeLiteral(
        lit
          .members
          .iter()
          .map(|id| self.type_member_sort_key(*id, cache, in_progress))
          .collect(),
      ),
      TypeExprKind::Parenthesized(inner) => self.type_expr_sort_key(*inner, cache, in_progress),
      TypeExprKind::TypeQuery(name) => TypeSortKey::TypeQuery(self.type_name_sort_key(name)),
      TypeExprKind::KeyOf(inner) => {
        TypeSortKey::KeyOf(Box::new(self.type_expr_sort_key(*inner, cache, in_progress)))
      }
      TypeExprKind::IndexedAccess {
        object_type,
        index_type,
      } => TypeSortKey::IndexedAccess {
        object_type: Box::new(self.type_expr_sort_key(*object_type, cache, in_progress)),
        index_type: Box::new(self.type_expr_sort_key(*index_type, cache, in_progress)),
      },
      TypeExprKind::Conditional(cond) => TypeSortKey::Conditional {
        check_type: Box::new(self.type_expr_sort_key(cond.check_type, cache, in_progress)),
        extends_type: Box::new(self.type_expr_sort_key(cond.extends_type, cache, in_progress)),
        true_type: Box::new(self.type_expr_sort_key(cond.true_type, cache, in_progress)),
        false_type: Box::new(self.type_expr_sort_key(cond.false_type, cache, in_progress)),
      },
      TypeExprKind::Infer(type_param) => {
        TypeSortKey::Infer(self.type_param_sort_key(*type_param, cache, in_progress))
      }
      TypeExprKind::Mapped(mapped) => TypeSortKey::Mapped(self.mapped_sort_key(mapped, cache, in_progress)),
      TypeExprKind::TemplateLiteral(tmpl) => TypeSortKey::TemplateLiteral(TemplateLiteralKey {
        head: tmpl.head.clone(),
        spans: tmpl
          .spans
          .iter()
          .map(|span| TemplateLiteralSpanKey {
            type_expr: self.type_expr_sort_key(span.type_expr, cache, in_progress),
            literal: span.literal.clone(),
          })
          .collect(),
      }),
      TypeExprKind::TypePredicate(pred) => TypeSortKey::TypePredicate(TypePredicateKey {
        asserts: pred.asserts,
        parameter: self.name_id_to_string(pred.parameter),
        type_annotation: pred
          .type_annotation
          .map(|ty| Box::new(self.type_expr_sort_key(ty, cache, in_progress))),
      }),
      TypeExprKind::Import(import) => TypeSortKey::Import(ImportKey {
        module: import.module.clone(),
        qualifier: import
          .qualifier
          .as_ref()
          .map(|name| self.type_name_sort_key(name)),
        type_args: import
          .type_args
          .iter()
          .map(|arg| self.type_expr_sort_key(*arg, cache, in_progress))
          .collect(),
      }),
    };

    in_progress.remove(&id);
    cache.insert(id, key.clone());
    key
  }

  fn signature_sort_key(
    &self,
    type_params: &[TypeParamId],
    params: &[TypeFnParam],
    return_type: Option<TypeExprId>,
    cache: &mut HashMap<TypeExprId, TypeSortKey>,
    in_progress: &mut HashSet<TypeExprId>,
  ) -> SignatureKey {
    SignatureKey {
      type_params: type_params
        .iter()
        .map(|id| self.type_param_sort_key(*id, cache, in_progress))
        .collect(),
      params: params
        .iter()
        .map(|param| self.fn_param_sort_key(param, cache, in_progress))
        .collect(),
      return_type: return_type.map(|id| Box::new(self.type_expr_sort_key(id, cache, in_progress))),
    }
  }

  fn fn_param_sort_key(
    &self,
    param: &TypeFnParam,
    cache: &mut HashMap<TypeExprId, TypeSortKey>,
    in_progress: &mut HashSet<TypeExprId>,
  ) -> FnParamKey {
    FnParamKey {
      ty: self.type_expr_sort_key(param.ty, cache, in_progress),
      optional: param.optional,
      rest: param.rest,
    }
  }

  fn type_param_sort_key(
    &self,
    id: TypeParamId,
    cache: &mut HashMap<TypeExprId, TypeSortKey>,
    in_progress: &mut HashSet<TypeExprId>,
  ) -> TypeParamKey {
    let param = &self.arenas.type_params[id.0 as usize];
    TypeParamKey {
      name: self.name_id_to_string(param.name),
      constraint: param
        .constraint
        .map(|id| Box::new(self.type_expr_sort_key(id, cache, in_progress))),
      default: param
        .default
        .map(|id| Box::new(self.type_expr_sort_key(id, cache, in_progress))),
      variance: param.variance.map(Self::variance_sort_key),
      const_: param.const_,
      is_infer: param.is_infer,
    }
  }

  fn variance_sort_key(variance: TypeVariance) -> VarianceKey {
    match variance {
      TypeVariance::In => VarianceKey::In,
      TypeVariance::Out => VarianceKey::Out,
      TypeVariance::InOut => VarianceKey::InOut,
    }
  }

  fn mapped_sort_key(
    &self,
    mapped: &HirTypeMapped,
    cache: &mut HashMap<TypeExprId, TypeSortKey>,
    in_progress: &mut HashSet<TypeExprId>,
  ) -> MappedKey {
    MappedKey {
      type_param: self.type_param_sort_key(mapped.type_param, cache, in_progress),
      constraint: Box::new(self.type_expr_sort_key(mapped.constraint, cache, in_progress)),
      name_type: mapped
        .name_type
        .map(|id| Box::new(self.type_expr_sort_key(id, cache, in_progress))),
      value_type: Box::new(self.type_expr_sort_key(mapped.value_type, cache, in_progress)),
      readonly: mapped.readonly.map(Self::mapped_modifier_sort_key),
      optional: mapped.optional.map(Self::mapped_modifier_sort_key),
    }
  }

  fn mapped_modifier_sort_key(modifier: TypeMappedModifier) -> MappedModifierKey {
    match modifier {
      TypeMappedModifier::Plus => MappedModifierKey::Plus,
      TypeMappedModifier::Minus => MappedModifierKey::Minus,
      TypeMappedModifier::None => MappedModifierKey::None,
    }
  }

  fn type_member_sort_key(
    &self,
    id: TypeMemberId,
    cache: &mut HashMap<TypeExprId, TypeSortKey>,
    in_progress: &mut HashSet<TypeExprId>,
  ) -> TypeMemberKey {
    let member = &self.arenas.type_members[id.0 as usize];
    match &member.kind {
      TypeMemberKind::Property(prop) => TypeMemberKey::Property {
        readonly: prop.readonly,
        optional: prop.optional,
        name: self.property_name_key(&prop.name),
        type_annotation: prop
          .type_annotation
          .map(|id| self.type_expr_sort_key(id, cache, in_progress)),
      },
      TypeMemberKind::Method(method) => TypeMemberKey::Method {
        optional: method.optional,
        name: self.property_name_key(&method.name),
        signature: self.signature_sort_key(
          &method.type_params,
          &method.params,
          method.return_type,
          cache,
          in_progress,
        ),
      },
      TypeMemberKind::Constructor(signature) => TypeMemberKey::Constructor(self.signature_sort_key(
        &signature.type_params,
        &signature.params,
        signature.return_type,
        cache,
        in_progress,
      )),
      TypeMemberKind::CallSignature(signature) => TypeMemberKey::CallSignature(self.signature_sort_key(
        &signature.type_params,
        &signature.params,
        signature.return_type,
        cache,
        in_progress,
      )),
      TypeMemberKind::IndexSignature(signature) => TypeMemberKey::IndexSignature(IndexSignatureKey {
        readonly: signature.readonly,
        parameter_type: self.type_expr_sort_key(signature.parameter_type, cache, in_progress),
        type_annotation: self.type_expr_sort_key(signature.type_annotation, cache, in_progress),
      }),
      TypeMemberKind::Getter(getter) => TypeMemberKey::Getter {
        name: self.property_name_key(&getter.name),
        return_type: getter
          .return_type
          .map(|id| self.type_expr_sort_key(id, cache, in_progress)),
      },
      TypeMemberKind::Setter(setter) => TypeMemberKey::Setter {
        name: self.property_name_key(&setter.name),
        parameter: self.fn_param_sort_key(&setter.parameter, cache, in_progress),
      },
      TypeMemberKind::Mapped(mapped) => {
        TypeMemberKey::Mapped(self.mapped_sort_key(mapped, cache, in_progress))
      }
    }
  }

  fn literal_sort_key(&self, literal: &HirTypeLiteral) -> LiteralKey {
    match literal {
      HirTypeLiteral::String(s) => LiteralKey::String(s.clone()),
      HirTypeLiteral::Number(n) => LiteralKey::Number(n.clone()),
      HirTypeLiteral::BigInt(n) => LiteralKey::BigInt(n.clone()),
      HirTypeLiteral::Boolean(b) => LiteralKey::Boolean(*b),
      HirTypeLiteral::Null => LiteralKey::Null,
    }
  }

  fn type_name_sort_key(&self, name: &TypeName) -> TypeNameKey {
    match name {
      TypeName::Ident(id) => TypeNameKey::Ident(self.name_id_to_string(*id)),
      TypeName::Qualified(path) => {
        TypeNameKey::Qualified(path.iter().map(|id| self.name_id_to_string(*id)).collect())
      }
      TypeName::Import(import) => TypeNameKey::Import {
        module: import.module.clone(),
        qualifier: import.qualifier.as_ref().map(|qualifier| {
          qualifier
            .iter()
            .map(|id| self.name_id_to_string(*id))
            .collect()
        }),
      },
      TypeName::ImportExpr => TypeNameKey::ImportExpr,
    }
  }

  fn name_id_to_string(&self, id: NameId) -> String {
    self.names.resolve(id).unwrap_or("").to_string()
  }

  fn type_kind_discriminant(&self, kind: &TypeExprKind) -> u8 {
    match kind {
      TypeExprKind::Any => 0,
      TypeExprKind::Unknown => 1,
      TypeExprKind::Never => 2,
      TypeExprKind::Void => 3,
      TypeExprKind::String => 4,
      TypeExprKind::Number => 5,
      TypeExprKind::Boolean => 6,
      TypeExprKind::BigInt => 7,
      TypeExprKind::Symbol => 8,
      TypeExprKind::UniqueSymbol => 9,
      TypeExprKind::Object => 10,
      TypeExprKind::Null => 11,
      TypeExprKind::Undefined => 12,
      TypeExprKind::This => 13,
      TypeExprKind::Literal(_) => 14,
      TypeExprKind::TypeRef(_) => 15,
      TypeExprKind::Array(_) => 16,
      TypeExprKind::Tuple(_) => 17,
      TypeExprKind::Union(_) => 18,
      TypeExprKind::Intersection(_) => 19,
      TypeExprKind::Function(_) => 20,
      TypeExprKind::Constructor(_) => 21,
      TypeExprKind::TypeLiteral(_) => 22,
      TypeExprKind::Parenthesized(_) => 23,
      TypeExprKind::TypeQuery(_) => 24,
      TypeExprKind::KeyOf(_) => 25,
      TypeExprKind::IndexedAccess { .. } => 26,
      TypeExprKind::Conditional(_) => 27,
      TypeExprKind::Infer(_) => 28,
      TypeExprKind::Mapped(_) => 29,
      TypeExprKind::TemplateLiteral(_) => 30,
      TypeExprKind::TypePredicate(_) => 31,
      TypeExprKind::Import(_) => 32,
    }
  }
}

enum LoweredEntityName {
  Path(Vec<NameId>),
  Import(TypeImportName),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TypeSortKey {
  Primitive(&'static str),
  Literal(LiteralKey),
  TypeRef {
    name: TypeNameKey,
    type_args: Vec<TypeSortKey>,
  },
  Array {
    readonly: bool,
    element: Box<TypeSortKey>,
  },
  Tuple {
    readonly: bool,
    elements: Vec<TupleElementKey>,
  },
  Union(Vec<TypeSortKey>),
  Intersection(Vec<TypeSortKey>),
  Function(SignatureKey),
  Constructor(SignatureKey),
  TypeLiteral(Vec<TypeMemberKey>),
  TypeQuery(TypeNameKey),
  KeyOf(Box<TypeSortKey>),
  IndexedAccess {
    object_type: Box<TypeSortKey>,
    index_type: Box<TypeSortKey>,
  },
  Conditional {
    check_type: Box<TypeSortKey>,
    extends_type: Box<TypeSortKey>,
    true_type: Box<TypeSortKey>,
    false_type: Box<TypeSortKey>,
  },
  Infer(TypeParamKey),
  Mapped(MappedKey),
  TemplateLiteral(TemplateLiteralKey),
  TypePredicate(TypePredicateKey),
  Import(ImportKey),
  Cycle {
    discriminant: u8,
    id: u32,
  },
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct SignatureKey {
  type_params: Vec<TypeParamKey>,
  params: Vec<FnParamKey>,
  return_type: Option<Box<TypeSortKey>>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FnParamKey {
  ty: TypeSortKey,
  optional: bool,
  rest: bool,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TypeParamKey {
  name: String,
  constraint: Option<Box<TypeSortKey>>,
  default: Option<Box<TypeSortKey>>,
  variance: Option<VarianceKey>,
  const_: bool,
  is_infer: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum VarianceKey {
  In,
  Out,
  InOut,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct MappedKey {
  type_param: TypeParamKey,
  constraint: Box<TypeSortKey>,
  name_type: Option<Box<TypeSortKey>>,
  value_type: Box<TypeSortKey>,
  readonly: Option<MappedModifierKey>,
  optional: Option<MappedModifierKey>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum MappedModifierKey {
  Plus,
  Minus,
  None,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TemplateLiteralKey {
  head: String,
  spans: Vec<TemplateLiteralSpanKey>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TemplateLiteralSpanKey {
  type_expr: TypeSortKey,
  literal: String,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TypePredicateKey {
  asserts: bool,
  parameter: String,
  type_annotation: Option<Box<TypeSortKey>>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ImportKey {
  module: String,
  qualifier: Option<TypeNameKey>,
  type_args: Vec<TypeSortKey>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TypeMemberKey {
  Property {
    readonly: bool,
    optional: bool,
    name: String,
    type_annotation: Option<TypeSortKey>,
  },
  Method {
    optional: bool,
    name: String,
    signature: SignatureKey,
  },
  Constructor(SignatureKey),
  CallSignature(SignatureKey),
  IndexSignature(IndexSignatureKey),
  Getter {
    name: String,
    return_type: Option<TypeSortKey>,
  },
  Setter {
    name: String,
    parameter: FnParamKey,
  },
  Mapped(MappedKey),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct IndexSignatureKey {
  readonly: bool,
  parameter_type: TypeSortKey,
  type_annotation: TypeSortKey,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TupleElementKey {
  optional: bool,
  rest: bool,
  ty: TypeSortKey,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum LiteralKey {
  String(String),
  Number(String),
  BigInt(String),
  Boolean(bool),
  Null,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TypeNameKey {
  Ident(String),
  Qualified(Vec<String>),
  Import {
    module: Option<String>,
    qualifier: Option<Vec<String>>,
  },
  ImportExpr,
}
