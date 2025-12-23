//! Lowering from `parse-js` AST into a strict subset supported by `optimize-js` today.
//!
//! Supported statements:
//! - `Block`
//! - `Break`
//! - `Expr`
//! - `ForTriple`
//! - `If`
//! - `VarDecl` (modes: `Var`, `Let`, `Const`)
//! - `While`
//!
//! Supported expressions:
//! - `ArrowFunc` (with block bodies only)
//! - `Binary` with operators: `Assignment`, `AssignmentAddition`, `AssignmentSubtraction`,
//!   `AssignmentMultiplication`, `AssignmentDivision`, `LogicalAnd`, `LogicalOr`, `Addition`,
//!   `Subtraction`, `Multiplication`, `Division`, `LessThan`, `GreaterThan`, `StrictEquality`
//! - `Call`
//! - `ComputedMember`
//! - `Cond`
//! - `Id`
//! - `LitBool`
//! - `LitNum`
//! - `LitStr`
//! - `Member`
//! - `Unary` with operators: `PrefixIncrement`, `PrefixDecrement`, `UnaryNegation`
//! - `UnaryPostfix` with operators: `PostfixIncrement`, `PostfixDecrement`
//!
//! Supported patterns:
//! - `Id`
//! - `Arr` (without rest bindings)
//! - `Obj` (without rest bindings)
//!
//! Literals are limited to bool/number/string. All other constructs/operators are rejected
//! with [`LowerError::Unsupported`].

use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::ArrPat;
use parse_js::ast::expr::pat::ArrPatElem;
use parse_js::ast::expr::pat::ObjPat;
use parse_js::ast::expr::pat::ObjPatProp;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::BinaryExpr;
use parse_js::ast::expr::CallArg;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::ComputedMemberExpr;
use parse_js::ast::expr::CondExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::expr::UnaryExpr;
use parse_js::ast::expr::UnaryPostfixExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ParamDecl;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::decl::VarDeclarator;
use parse_js::ast::stmt::BlockStmt;
use parse_js::ast::stmt::ExprStmt;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForTripleStmt;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::IfStmt;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::WhileStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use std::error::Error;
use std::fmt;

/// A lowered program. This currently reuses the parsed AST but guarantees that only the supported
/// subset is present.
pub type Program = Node<TopLevel>;

/// Result alias for lowering operations.
pub type LowerResult<T> = Result<T, LowerError>;

/// Errors that can occur during lowering.
#[derive(Debug, PartialEq, Eq)]
pub enum LowerError {
  /// The input contains a construct we do not currently lower/optimize.
  Unsupported { loc: Loc, what: String },
}

impl LowerError {
  fn unsupported(loc: Loc, what: impl Into<String>) -> Self {
    LowerError::Unsupported {
      loc,
      what: what.into(),
    }
  }
}

impl fmt::Display for LowerError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LowerError::Unsupported { what, .. } => write!(f, "unsupported: {what}"),
    }
  }
}

impl Error for LowerError {}

/// Lower a parsed `TopLevel`, enforcing the supported subset.
pub fn lower(program: Program) -> LowerResult<Program> {
  validate_top_level(&program)?;
  Ok(program)
}

fn validate_top_level(program: &Program) -> LowerResult<()> {
  validate_stmt_list(&program.stx.body)
}

fn validate_stmt_list(stmts: &[Node<Stmt>]) -> LowerResult<()> {
  for stmt in stmts {
    validate_stmt(stmt)?;
  }
  Ok(())
}

fn validate_stmt(stmt: &Node<Stmt>) -> LowerResult<()> {
  match stmt.stx.as_ref() {
    Stmt::Block(block) => validate_block_stmt(&block.stx),
    Stmt::Break(_) => Ok(()),
    Stmt::Expr(expr) => validate_expr_stmt(&expr.stx),
    Stmt::ForTriple(for_triple) => validate_for_triple_stmt(&for_triple.stx),
    Stmt::If(if_stmt) => validate_if_stmt(&if_stmt.stx),
    Stmt::VarDecl(var_decl) => validate_var_decl(&var_decl.stx, stmt.loc),
    Stmt::While(while_stmt) => validate_while_stmt(&while_stmt.stx),
    _ => Err(LowerError::unsupported(
      stmt.loc,
      format!("statement {}", stmt_variant_name(stmt.stx.as_ref())),
    )),
  }
}

fn validate_block_stmt(stmt: &BlockStmt) -> LowerResult<()> {
  validate_stmt_list(&stmt.body)
}

fn validate_if_stmt(stmt: &IfStmt) -> LowerResult<()> {
  validate_expr(&stmt.test)?;
  validate_stmt(&stmt.consequent)?;
  if let Some(alt) = &stmt.alternate {
    validate_stmt(alt)?;
  }
  Ok(())
}

fn validate_for_triple_stmt(stmt: &ForTripleStmt) -> LowerResult<()> {
  match &stmt.init {
    ForTripleStmtInit::None => {}
    ForTripleStmtInit::Expr(expr) => validate_expr(expr)?,
    ForTripleStmtInit::Decl(decl) => validate_var_decl(&decl.stx, decl.loc)?,
  }
  if let Some(cond) = &stmt.cond {
    validate_expr(cond)?;
  }
  if let Some(post) = &stmt.post {
    validate_expr(post)?;
  }
  validate_for_body(&stmt.body)
}

fn validate_for_body(body: &Node<ForBody>) -> LowerResult<()> {
  validate_stmt_list(&body.stx.body)
}

fn validate_var_decl(decl: &VarDecl, loc: Loc) -> LowerResult<()> {
  match decl.mode {
    VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Var => {}
    VarDeclMode::Using => {
      return Err(LowerError::unsupported(
        loc,
        "variable declaration mode using",
      ));
    }
    VarDeclMode::AwaitUsing => {
      return Err(LowerError::unsupported(
        loc,
        "variable declaration mode await using",
      ));
    }
  }

  for VarDeclarator {
    pattern,
    initializer,
    ..
  } in &decl.declarators
  {
    validate_pat_decl(pattern)?;
    if let Some(init) = initializer {
      validate_expr(init)?;
    }
  }
  Ok(())
}

fn validate_while_stmt(stmt: &WhileStmt) -> LowerResult<()> {
  validate_expr(&stmt.condition)?;
  validate_stmt(&stmt.body)
}

fn validate_expr_stmt(stmt: &ExprStmt) -> LowerResult<()> {
  validate_expr(&stmt.expr)
}

fn validate_expr(expr: &Node<Expr>) -> LowerResult<()> {
  match expr.stx.as_ref() {
    Expr::ArrowFunc(func) => validate_func(&func.stx.func),
    Expr::Binary(binary) => validate_binary_expr(expr.loc, &binary.stx),
    Expr::Call(call) => validate_call_expr(&call.stx),
    Expr::ComputedMember(member) => validate_computed_member_expr(&member.stx),
    Expr::Cond(cond) => validate_cond_expr(&cond.stx),
    Expr::Id(_) => Ok(()),
    Expr::IdPat(_) => Ok(()),
    Expr::LitBool(_) => Ok(()),
    Expr::LitNum(_) => Ok(()),
    Expr::LitStr(_) => Ok(()),
    Expr::Member(member) => validate_member_expr(&member.stx),
    Expr::Unary(unary) => validate_unary_expr(expr.loc, &unary.stx),
    Expr::UnaryPostfix(unary) => validate_unary_postfix_expr(expr.loc, &unary.stx),
    Expr::ArrPat(pat) => validate_arr_pat(&pat.stx),
    Expr::ObjPat(pat) => validate_obj_pat(&pat.stx),
    Expr::LitNull(_) => Err(LowerError::unsupported(expr.loc, "literal null")),
    Expr::LitArr(_) => Err(LowerError::unsupported(expr.loc, "array literal")),
    Expr::LitObj(_) => Err(LowerError::unsupported(expr.loc, "object literal")),
    Expr::LitTemplate(_) => Err(LowerError::unsupported(expr.loc, "template literal")),
    Expr::LitRegex(_) => Err(LowerError::unsupported(expr.loc, "regex literal")),
    Expr::LitBigInt(_) => Err(LowerError::unsupported(expr.loc, "bigint literal")),
    _ => Err(LowerError::unsupported(
      expr.loc,
      format!("expression {}", expr_variant_name(expr.stx.as_ref())),
    )),
  }
}

fn validate_binary_expr(loc: Loc, expr: &BinaryExpr) -> LowerResult<()> {
  ensure_supported_binary_operator(loc, expr.operator)?;
  validate_expr(&expr.left)?;
  validate_expr(&expr.right)
}

const SUPPORTED_BINARY_OPERATORS: &[OperatorName] = &[
  OperatorName::Assignment,
  OperatorName::AssignmentAddition,
  OperatorName::AssignmentDivision,
  OperatorName::AssignmentMultiplication,
  OperatorName::AssignmentSubtraction,
  OperatorName::LogicalAnd,
  OperatorName::LogicalOr,
  OperatorName::Addition,
  OperatorName::Subtraction,
  OperatorName::Multiplication,
  OperatorName::Division,
  OperatorName::LessThan,
  OperatorName::GreaterThan,
  OperatorName::StrictEquality,
];

fn ensure_supported_binary_operator(loc: Loc, op: OperatorName) -> LowerResult<()> {
  if SUPPORTED_BINARY_OPERATORS.contains(&op) {
    Ok(())
  } else {
    Err(LowerError::unsupported(
      loc,
      format!("binary operator {op:?}"),
    ))
  }
}

fn validate_unary_expr(loc: Loc, expr: &UnaryExpr) -> LowerResult<()> {
  ensure_supported_unary_operator(loc, expr.operator)?;
  validate_expr(&expr.argument)
}

const SUPPORTED_UNARY_OPERATORS: &[OperatorName] = &[
  OperatorName::PrefixIncrement,
  OperatorName::PrefixDecrement,
  OperatorName::UnaryNegation,
];

fn ensure_supported_unary_operator(loc: Loc, op: OperatorName) -> LowerResult<()> {
  if SUPPORTED_UNARY_OPERATORS.contains(&op) {
    Ok(())
  } else {
    Err(LowerError::unsupported(
      loc,
      format!("unary operator {op:?}"),
    ))
  }
}

fn validate_unary_postfix_expr(loc: Loc, expr: &UnaryPostfixExpr) -> LowerResult<()> {
  ensure_supported_unary_postfix_operator(loc, expr.operator)?;
  validate_expr(&expr.argument)
}

const SUPPORTED_UNARY_POSTFIX_OPERATORS: &[OperatorName] = &[
  OperatorName::PostfixDecrement,
  OperatorName::PostfixIncrement,
];

fn ensure_supported_unary_postfix_operator(loc: Loc, op: OperatorName) -> LowerResult<()> {
  if SUPPORTED_UNARY_POSTFIX_OPERATORS.contains(&op) {
    Ok(())
  } else {
    Err(LowerError::unsupported(
      loc,
      format!("unary operator {op:?}"),
    ))
  }
}

fn validate_cond_expr(expr: &CondExpr) -> LowerResult<()> {
  validate_expr(&expr.test)?;
  validate_expr(&expr.consequent)?;
  validate_expr(&expr.alternate)
}

fn validate_call_expr(expr: &CallExpr) -> LowerResult<()> {
  validate_expr(&expr.callee)?;
  for arg in &expr.arguments {
    validate_call_arg(&arg.stx)?;
  }
  Ok(())
}

fn validate_call_arg(arg: &CallArg) -> LowerResult<()> {
  validate_expr(&arg.value)
}

fn validate_member_expr(expr: &MemberExpr) -> LowerResult<()> {
  validate_expr(&expr.left)
}

fn validate_computed_member_expr(expr: &ComputedMemberExpr) -> LowerResult<()> {
  validate_expr(&expr.object)?;
  validate_expr(&expr.member)
}

fn validate_func(func: &Node<Func>) -> LowerResult<()> {
  for param in &func.stx.parameters {
    validate_param_decl(&param.stx)?;
  }

  match &func.stx.body {
    Some(FuncBody::Block(stmts)) => validate_stmt_list(stmts),
    Some(FuncBody::Expression(expr)) => Err(LowerError::unsupported(
      expr.loc,
      "arrow function expression body",
    )),
    None => Ok(()),
  }
}

fn validate_param_decl(param: &ParamDecl) -> LowerResult<()> {
  validate_pat_decl(&param.pattern)?;
  if let Some(default) = &param.default_value {
    validate_expr(default)?;
  }
  Ok(())
}

fn validate_pat_decl(pat: &Node<PatDecl>) -> LowerResult<()> {
  validate_pat(&pat.stx.pat)
}

fn validate_pat(pat: &Node<Pat>) -> LowerResult<()> {
  match pat.stx.as_ref() {
    Pat::Arr(arr) => validate_arr_pat(&arr.stx),
    Pat::Id(_) => Ok(()),
    Pat::Obj(obj) => validate_obj_pat(&obj.stx),
    Pat::AssignTarget(_) => Err(LowerError::unsupported(
      pat.loc,
      format!("pattern {}", pat_variant_name(pat.stx.as_ref())),
    )),
  }
}

fn validate_arr_pat(pat: &ArrPat) -> LowerResult<()> {
  for ArrPatElem {
    target,
    default_value,
  } in pat.elements.iter().flatten()
  {
    validate_pat(target)?;
    if let Some(default) = default_value {
      validate_expr(default)?;
    }
  }

  if let Some(rest) = &pat.rest {
    return Err(LowerError::unsupported(
      rest.loc,
      "rest pattern in array destructuring",
    ));
  }
  Ok(())
}

fn validate_obj_pat(pat: &ObjPat) -> LowerResult<()> {
  for prop in &pat.properties {
    validate_obj_pat_prop(&prop.stx)?;
  }

  if let Some(rest) = &pat.rest {
    return Err(LowerError::unsupported(
      rest.loc,
      "rest pattern in object destructuring",
    ));
  }
  Ok(())
}

fn validate_obj_pat_prop(prop: &ObjPatProp) -> LowerResult<()> {
  match &prop.key {
    ClassOrObjKey::Direct(_) => {}
    ClassOrObjKey::Computed(expr) => validate_expr(expr)?,
  }
  validate_pat(&prop.target)?;
  if let Some(default) = &prop.default_value {
    validate_expr(default)?;
  }
  Ok(())
}

fn stmt_variant_name(stmt: &Stmt) -> &'static str {
  match stmt {
    Stmt::Block(_) => "Block",
    Stmt::Break(_) => "Break",
    Stmt::Continue(_) => "Continue",
    Stmt::Debugger(_) => "Debugger",
    Stmt::DoWhile(_) => "DoWhile",
    Stmt::Empty(_) => "Empty",
    Stmt::ExportDefaultExpr(_) => "ExportDefaultExpr",
    Stmt::ExportList(_) => "ExportList",
    Stmt::Expr(_) => "Expr",
    Stmt::ForIn(_) => "ForIn",
    Stmt::ForOf(_) => "ForOf",
    Stmt::ForTriple(_) => "ForTriple",
    Stmt::If(_) => "If",
    Stmt::Import(_) => "Import",
    Stmt::Label(_) => "Label",
    Stmt::Return(_) => "Return",
    Stmt::Switch(_) => "Switch",
    Stmt::Throw(_) => "Throw",
    Stmt::Try(_) => "Try",
    Stmt::While(_) => "While",
    Stmt::With(_) => "With",
    Stmt::ClassDecl(_) => "ClassDecl",
    Stmt::FunctionDecl(_) => "FunctionDecl",
    Stmt::VarDecl(_) => "VarDecl",
    Stmt::InterfaceDecl(_) => "InterfaceDecl",
    Stmt::TypeAliasDecl(_) => "TypeAliasDecl",
    Stmt::EnumDecl(_) => "EnumDecl",
    Stmt::NamespaceDecl(_) => "NamespaceDecl",
    Stmt::ModuleDecl(_) => "ModuleDecl",
    Stmt::GlobalDecl(_) => "GlobalDecl",
    Stmt::AmbientVarDecl(_) => "AmbientVarDecl",
    Stmt::AmbientFunctionDecl(_) => "AmbientFunctionDecl",
    Stmt::AmbientClassDecl(_) => "AmbientClassDecl",
    Stmt::ImportTypeDecl(_) => "ImportTypeDecl",
    Stmt::ExportTypeDecl(_) => "ExportTypeDecl",
    Stmt::ImportEqualsDecl(_) => "ImportEqualsDecl",
    Stmt::ExportAssignmentDecl(_) => "ExportAssignmentDecl",
  }
}

fn expr_variant_name(expr: &Expr) -> &'static str {
  match expr {
    Expr::ArrowFunc(_) => "ArrowFunc",
    Expr::Binary(_) => "Binary",
    Expr::Call(_) => "Call",
    Expr::Class(_) => "Class",
    Expr::ComputedMember(_) => "ComputedMember",
    Expr::Cond(_) => "Cond",
    Expr::Func(_) => "Func",
    Expr::Id(_) => "Id",
    Expr::Import(_) => "Import",
    Expr::ImportMeta(_) => "ImportMeta",
    Expr::Member(_) => "Member",
    Expr::NewTarget(_) => "NewTarget",
    Expr::Super(_) => "Super",
    Expr::TaggedTemplate(_) => "TaggedTemplate",
    Expr::This(_) => "This",
    Expr::Unary(_) => "Unary",
    Expr::UnaryPostfix(_) => "UnaryPostfix",
    Expr::JsxElem(_) => "JsxElem",
    Expr::JsxExprContainer(_) => "JsxExprContainer",
    Expr::JsxMember(_) => "JsxMember",
    Expr::JsxName(_) => "JsxName",
    Expr::JsxSpreadAttr(_) => "JsxSpreadAttr",
    Expr::JsxText(_) => "JsxText",
    Expr::LitArr(_) => "LitArr",
    Expr::LitBigInt(_) => "LitBigInt",
    Expr::LitBool(_) => "LitBool",
    Expr::LitNull(_) => "LitNull",
    Expr::LitNum(_) => "LitNum",
    Expr::LitObj(_) => "LitObj",
    Expr::LitRegex(_) => "LitRegex",
    Expr::LitStr(_) => "LitStr",
    Expr::LitTemplate(_) => "LitTemplate",
    Expr::ArrPat(_) => "ArrPat",
    Expr::IdPat(_) => "IdPat",
    Expr::ObjPat(_) => "ObjPat",
    Expr::TypeAssertion(_) => "TypeAssertion",
    Expr::NonNullAssertion(_) => "NonNullAssertion",
    Expr::SatisfiesExpr(_) => "SatisfiesExpr",
  }
}

fn pat_variant_name(pat: &Pat) -> &'static str {
  match pat {
    Pat::Arr(_) => "Arr",
    Pat::Id(_) => "Id",
    Pat::Obj(_) => "Obj",
    Pat::AssignTarget(_) => "AssignTarget",
  }
}
