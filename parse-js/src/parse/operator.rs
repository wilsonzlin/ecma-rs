use crate::operator::Operator;
use crate::operator::OperatorName;
use crate::operator::OPERATORS;
use crate::token::TT;
use ahash::HashMap;
use ahash::HashMapExt;
use once_cell::sync::Lazy;

#[rustfmt::skip]
pub static MULTARY_OPERATOR_MAPPING: Lazy<HashMap<TT, &'static Operator>> = Lazy::new(|| {
  let mut map = HashMap::<TT, &'static Operator>::new();
  map.insert(TT::Plus, &OPERATORS[&OperatorName::Addition]);
  map.insert(TT::Equals, &OPERATORS[&OperatorName::Assignment]);
  map.insert(TT::PlusEquals, &OPERATORS[&OperatorName::AssignmentAddition]);
  map.insert(TT::AmpersandEquals, &OPERATORS[&OperatorName::AssignmentBitwiseAnd]);
  map.insert(TT::ChevronLeftChevronLeftEquals, &OPERATORS[&OperatorName::AssignmentBitwiseLeftShift]);
  map.insert(TT::BarEquals, &OPERATORS[&OperatorName::AssignmentBitwiseOr]);
  map.insert(TT::ChevronRightChevronRightEquals, &OPERATORS[&OperatorName::AssignmentBitwiseRightShift]);
  map.insert(TT::ChevronRightChevronRightChevronRightEquals, &OPERATORS[&OperatorName::AssignmentBitwiseUnsignedRightShift]);
  map.insert(TT::CaretEquals, &OPERATORS[&OperatorName::AssignmentBitwiseXor]);
  map.insert(TT::SlashEquals, &OPERATORS[&OperatorName::AssignmentDivision]);
  map.insert(TT::AsteriskAsteriskEquals, &OPERATORS[&OperatorName::AssignmentExponentiation]);
  map.insert(TT::AmpersandAmpersandEquals, &OPERATORS[&OperatorName::AssignmentLogicalAnd]);
  map.insert(TT::BarBarEquals, &OPERATORS[&OperatorName::AssignmentLogicalOr]);
  map.insert(TT::AsteriskEquals, &OPERATORS[&OperatorName::AssignmentMultiplication]);
  map.insert(TT::QuestionQuestionEquals, &OPERATORS[&OperatorName::AssignmentNullishCoalescing]);
  map.insert(TT::PercentEquals, &OPERATORS[&OperatorName::AssignmentRemainder]);
  map.insert(TT::HyphenEquals, &OPERATORS[&OperatorName::AssignmentSubtraction]);
  map.insert(TT::Ampersand, &OPERATORS[&OperatorName::BitwiseAnd]);
  map.insert(TT::ChevronLeftChevronLeft, &OPERATORS[&OperatorName::BitwiseLeftShift]);
  map.insert(TT::Bar, &OPERATORS[&OperatorName::BitwiseOr]);
  map.insert(TT::ChevronRightChevronRight, &OPERATORS[&OperatorName::BitwiseRightShift]);
  map.insert(TT::ChevronRightChevronRightChevronRight, &OPERATORS[&OperatorName::BitwiseUnsignedRightShift]);
  map.insert(TT::Caret, &OPERATORS[&OperatorName::BitwiseXor]);
  map.insert(TT::ParenthesisOpen, &OPERATORS[&OperatorName::Call]);
  map.insert(TT::Comma, &OPERATORS[&OperatorName::Comma]);
  map.insert(TT::BracketOpen, &OPERATORS[&OperatorName::ComputedMemberAccess]);
  map.insert(TT::Question, &OPERATORS[&OperatorName::Conditional]);
  map.insert(TT::Slash, &OPERATORS[&OperatorName::Division]);
  map.insert(TT::EqualsEquals, &OPERATORS[&OperatorName::Equality]);
  map.insert(TT::AsteriskAsterisk, &OPERATORS[&OperatorName::Exponentiation]);
  map.insert(TT::ChevronRight, &OPERATORS[&OperatorName::GreaterThan]);
  map.insert(TT::ChevronRightEquals, &OPERATORS[&OperatorName::GreaterThanOrEqual]);
  map.insert(TT::KeywordIn, &OPERATORS[&OperatorName::In]);
  map.insert(TT::ExclamationEquals, &OPERATORS[&OperatorName::Inequality]);
  map.insert(TT::KeywordInstanceof, &OPERATORS[&OperatorName::Instanceof]);
  map.insert(TT::ChevronLeft, &OPERATORS[&OperatorName::LessThan]);
  map.insert(TT::ChevronLeftEquals, &OPERATORS[&OperatorName::LessThanOrEqual]);
  map.insert(TT::AmpersandAmpersand, &OPERATORS[&OperatorName::LogicalAnd]);
  map.insert(TT::BarBar, &OPERATORS[&OperatorName::LogicalOr]);
  map.insert(TT::Dot, &OPERATORS[&OperatorName::MemberAccess]);
  map.insert(TT::Asterisk, &OPERATORS[&OperatorName::Multiplication]);
  map.insert(TT::QuestionQuestion, &OPERATORS[&OperatorName::NullishCoalescing]);
  map.insert(TT::QuestionDot, &OPERATORS[&OperatorName::OptionalChainingMemberAccess]);
  map.insert(TT::QuestionDotBracketOpen, &OPERATORS[&OperatorName::OptionalChainingComputedMemberAccess]);
  map.insert(TT::QuestionDotParenthesisOpen, &OPERATORS[&OperatorName::OptionalChainingCall]);
  map.insert(TT::Percent, &OPERATORS[&OperatorName::Remainder]);
  map.insert(TT::EqualsEqualsEquals, &OPERATORS[&OperatorName::StrictEquality]);
  map.insert(TT::ExclamationEqualsEquals, &OPERATORS[&OperatorName::StrictInequality]);
  map.insert(TT::Hyphen, &OPERATORS[&OperatorName::Subtraction]);
  map.insert(TT::KeywordTypeof, &OPERATORS[&OperatorName::Typeof]);
  map
});

#[rustfmt::skip]
pub static UNARY_OPERATOR_MAPPING: Lazy<HashMap<TT, &'static Operator>> = Lazy::new(|| {
  let mut map = HashMap::<TT, &'static Operator>::new();
  // Postfix{Increment,Decrement} and YieldDelegated omitted and handled manually.
  map.insert(TT::KeywordAwait, &OPERATORS[&OperatorName::Await]);
  map.insert(TT::Tilde, &OPERATORS[&OperatorName::BitwiseNot]);
  map.insert(TT::KeywordDelete, &OPERATORS[&OperatorName::Delete]);
  map.insert(TT::Exclamation, &OPERATORS[&OperatorName::LogicalNot]);
  map.insert(TT::KeywordNew, &OPERATORS[&OperatorName::New]);
  map.insert(TT::HyphenHyphen, &OPERATORS[&OperatorName::PrefixDecrement]);
  map.insert(TT::PlusPlus, &OPERATORS[&OperatorName::PrefixIncrement]);
  map.insert(TT::Hyphen, &OPERATORS[&OperatorName::UnaryNegation]);
  map.insert(TT::Plus, &OPERATORS[&OperatorName::UnaryPlus]);
  map.insert(TT::KeywordTypeof, &OPERATORS[&OperatorName::Typeof]);
  map.insert(TT::KeywordVoid, &OPERATORS[&OperatorName::Void]);
  map.insert(TT::KeywordYield, &OPERATORS[&OperatorName::Yield]);
  map
});
