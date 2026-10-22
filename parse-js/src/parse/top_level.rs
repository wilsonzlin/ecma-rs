use super::expr::pat::ParsePatternRules;
use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ObjMember;
use crate::ast::node::CoverInitializedName;
use crate::ast::node::Node;
use crate::ast::stx::TopLevel;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::token::TT;
use derive_visitor::Drive;
use derive_visitor::Visitor;

impl<'a> Parser<'a> {
  pub fn parse_top_level(&mut self) -> SyntaxResult<Node<TopLevel>> {
    let is_module = self.is_module();
    if self.is_strict_ecmascript() && !is_module {
      if self.has_use_strict_directive_in_prologue(TT::EOF)? {
        self.strict_mode += 1;
      }
    }
    let ctx = ParseCtx {
      rules: ParsePatternRules {
        await_allowed: !is_module,
        yield_allowed: !is_module,
        await_expr_allowed: is_module,
        yield_expr_allowed: false,
      },
      top_level: true,
      in_namespace: false,
      asi: super::AsiContext::Statements,
    };
    let body = self.stmts(ctx, TT::EOF)?;
    self.require(TT::EOF)?;
    let top_level_node = Node::new(self.source_range(), TopLevel { body });
    if self.is_strict_ecmascript() {
      reject_dangling_cover_initialized_name(&top_level_node)?;
    }
    Ok(top_level_node)
  }
}

/// Early error: CoverInitializedName may only appear when the covering ObjectLiteral
/// is reinterpreted as an ObjectAssignmentPattern / binding pattern. Any remaining
/// `LitObjExpr` member still marked [`CoverInitializedName`] is a SyntaxError
/// (ECMA-262 ObjectLiteral early errors; e.g. `({a = 1});`).
fn reject_dangling_cover_initialized_name(top: &Node<TopLevel>) -> SyntaxResult<()> {
  type ObjMemberNode = Node<ObjMember>;

  #[derive(Default, Visitor)]
  #[visitor(ObjMemberNode(enter))]
  struct Checker {
    error_loc: Option<crate::loc::Loc>,
  }

  impl Checker {
    fn enter_obj_member_node(&mut self, member: &ObjMemberNode) {
      if self.error_loc.is_none() && member.assoc.get::<CoverInitializedName>().is_some() {
        self.error_loc = Some(member.loc);
      }
    }
  }

  let mut checker = Checker::default();
  top.drive(&mut checker);
  if let Some(loc) = checker.error_loc {
    return Err(loc.error(
      SyntaxErrorType::ExpectedSyntax(
        "object literal property (CoverInitializedName is only valid in destructuring patterns)",
      ),
      None,
    ));
  }
  Ok(())
}
