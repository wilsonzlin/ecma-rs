use crate::hir::ConditionalType;
use crate::hir::DefTypeInfo;
use crate::hir::PropertyName;
use crate::hir::TypeArenas;
use crate::hir::TypeArray;
use crate::hir::TypeExpr as HirTypeExpr;
use crate::hir::TypeExprKind;
use crate::hir::TypeFnParam;
use crate::hir::TypeFunction as HirTypeFunction;
use crate::hir::TypeGetterSignature;
use crate::hir::TypeImport as HirTypeImport;
use crate::hir::TypeIndexSignature as HirTypeIndexSignature;
use crate::hir::TypeLiteral as HirTypeLiteral;
use crate::hir::TypeLiteralType;
use crate::hir::TypeMapped as HirTypeMapped;
use crate::hir::TypeMappedModifier;
use crate::hir::TypeMember as HirTypeMember;
use crate::hir::TypeMemberKind;
use crate::hir::TypeMethodSignature as HirTypeMethodSignature;
use crate::hir::TypeName;
use crate::hir::TypeImportName;
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
use crate::ids::NameId;
use crate::ids::TypeExprId;
use crate::ids::TypeMemberId;
use crate::ids::TypeParamId;
use crate::intern::NameInterner;
use crate::lower::LoweringContext;
use crate::span_map::SpanMap;
use diagnostics::TextRange;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::ImportExpr;
use parse_js::ast::node::Node;
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::ast::type_expr::*;

pub(crate) struct TypeLowerer<'a> {
  pub type_exprs: Vec<HirTypeExpr>,
  pub type_members: Vec<HirTypeMember>,
  pub type_params: Vec<TypeParam>,
  names: &'a mut NameInterner,
  span_map: &'a mut SpanMap,
  ctx: &'a mut LoweringContext,
}

impl<'a> TypeLowerer<'a> {
  pub fn new(
    names: &'a mut NameInterner,
    span_map: &'a mut SpanMap,
    ctx: &'a mut LoweringContext,
  ) -> Self {
    Self {
      type_exprs: Vec::new(),
      type_members: Vec::new(),
      type_params: Vec::new(),
      names,
      span_map,
      ctx,
    }
  }

  pub fn finish(self) -> TypeArenas {
    TypeArenas {
      type_exprs: self.type_exprs,
      type_members: self.type_members,
      type_params: self.type_params,
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
    let id = TypeExprId(self.type_exprs.len() as u32);
    self.type_exprs.push(HirTypeExpr { span, kind });
    self.span_map.add_type_expr(span, id);
    id
  }

  fn alloc_type_member(&mut self, span: TextRange, kind: TypeMemberKind) -> TypeMemberId {
    let id = TypeMemberId(self.type_members.len() as u32);
    self.type_members.push(HirTypeMember { span, kind });
    id
  }

  fn alloc_type_param(&mut self, param: TypeParam) -> TypeParamId {
    let id = TypeParamId(self.type_params.len() as u32);
    self.type_params.push(param);
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
      let a_member = &self.type_members[a.0 as usize];
      let b_member = &self.type_members[b.0 as usize];
      self
        .member_sort_key(a_member)
        .cmp(&self.member_sort_key(b_member))
    });
    lowered
  }

  fn member_sort_key(&self, member: &HirTypeMember) -> (String, u8, u32) {
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
    (name, variant, member.span.start)
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
        .map(Self::lower_mapped_modifier)
        .unwrap_or(TypeMappedModifier::None),
      optional: mapped
        .stx
        .optional_modifier
        .map(Self::lower_mapped_modifier)
        .unwrap_or(TypeMappedModifier::None),
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
    let mut flat = Vec::new();
    for m in members {
      match &self.type_exprs[m.0 as usize].kind {
        TypeExprKind::Union(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(m),
      }
    }
    flat.sort_by_key(|m| m.0);
    flat.dedup();
    flat
  }

  fn canonicalize_intersection(&self, members: Vec<TypeExprId>) -> Vec<TypeExprId> {
    let mut flat = Vec::new();
    for m in members {
      match &self.type_exprs[m.0 as usize].kind {
        TypeExprKind::Intersection(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(m),
      }
    }
    flat.sort_by_key(|m| m.0);
    flat.dedup();
    flat
  }
}

enum LoweredEntityName {
  Path(Vec<NameId>),
  Import(TypeImportName),
}
