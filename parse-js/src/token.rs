use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::lex::KEYWORDS_MAPPING;
use crate::loc::Loc;
use ahash::HashMap;
use ahash::HashSet;
use ahash::HashSetExt;
use once_cell::sync::Lazy;
use serde::Serialize;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Serialize)]
pub enum TT {
  // Used to represent a type that should never be seen in actual code. Similar to 0xFF from UTF-8
  // bytes perspective. Often used to represent an omitted value without having to use `Option`.
  _Dummy,
  // Special token used to represent the end of the source code. Easier than using and handling Option everywhere.
  EOF,
  // Special token used to represent invalid source code. Easier than having to propagate SyntaxError from the lexer level, which means even peeking during parsing requires error handling (e.g. can't use Option/Result fluent callbacks without excessive wrapping in OK and then transposing).
  Invalid,
  // These are only used by lexer.
  CommentMultilineEnd,
  LineTerminator,
  LiteralNumberBin,
  LiteralNumberHex,
  LiteralNumberOct,
  Whitespace,

  At,
  Ampersand,
  AmpersandAmpersand,
  AmpersandAmpersandEquals,
  AmpersandEquals,
  Asterisk,
  AsteriskAsterisk,
  AsteriskAsteriskEquals,
  AsteriskEquals,
  Bar,
  BarBar,
  BarBarEquals,
  BarEquals,
  BraceClose,
  BraceOpen,
  BracketClose,
  BracketOpen,
  Caret,
  CaretEquals,
  ChevronLeft,
  ChevronLeftChevronLeft,
  ChevronLeftChevronLeftEquals,
  ChevronLeftEquals,
  ChevronLeftSlash,
  ChevronRight,
  ChevronRightChevronRight,
  ChevronRightChevronRightChevronRight,
  ChevronRightChevronRightChevronRightEquals,
  ChevronRightChevronRightEquals,
  ChevronRightEquals,
  Colon,
  Comma,
  CommentMultiline,
  CommentSingle,
  Dot,
  DotDotDot,
  Equals,
  EqualsChevronRight,
  EqualsEquals,
  EqualsEqualsEquals,
  Exclamation,
  ExclamationEquals,
  ExclamationEqualsEquals,
  Hyphen,
  HyphenEquals,
  HyphenHyphen,
  Identifier,
  JsxTextContent,
  KeywordAs,
  KeywordAsync,
  KeywordAwait,
  KeywordBreak,
  KeywordCase,
  KeywordCatch,
  KeywordClass,
  KeywordConst,
  KeywordConstructor,
  KeywordContinue,
  KeywordDebugger,
  KeywordDefault,
  KeywordDelete,
  KeywordDo,
  KeywordElse,
  KeywordEnum,
  KeywordExport,
  KeywordExtends,
  KeywordFinally,
  KeywordFor,
  KeywordFrom,
  KeywordFunction,
  KeywordGet,
  KeywordIf,
  KeywordImport,
  KeywordIn,
  KeywordInstanceof,
  KeywordLet,
  KeywordNew,
  KeywordOf,
  KeywordOut,
  KeywordReturn,
  KeywordSet,
  KeywordStatic,
  KeywordSuper,
  KeywordSwitch,
  KeywordThis,
  KeywordThrow,
  KeywordTry,
  KeywordTypeof,
  KeywordUsing,
  KeywordVar,
  KeywordVoid,
  KeywordWhile,
  KeywordWith,
  KeywordYield,
  // TypeScript keywords
  KeywordAbstract,
  KeywordAccessor,
  KeywordAny,
  KeywordAsserts,
  KeywordBigIntType,
  KeywordBooleanType,
  KeywordDeclare,
  KeywordImplements,
  KeywordInfer,
  KeywordInterface,
  KeywordIs,
  KeywordKeyof,
  KeywordModule,
  KeywordNamespace,
  KeywordNever,
  KeywordNumberType,
  KeywordObjectType,
  KeywordOverride,
  KeywordPrivate,
  KeywordProtected,
  KeywordPublic,
  KeywordReadonly,
  KeywordSatisfies,
  KeywordStringType,
  KeywordSymbolType,
  KeywordType,
  KeywordUndefinedType,
  KeywordUnique,
  KeywordUnknown,
  LiteralBigInt,
  LiteralFalse,
  LiteralNull,
  LiteralNumber,
  LiteralRegex,
  LiteralString,
  LiteralTemplatePartString,
  LiteralTemplatePartStringEnd,
  LiteralTrue,
  ParenthesisClose,
  ParenthesisOpen,
  Percent,
  PercentEquals,
  Plus,
  PlusEquals,
  PlusPlus,
  PrivateMember,
  Question,
  QuestionDot,
  QuestionDotBracketOpen,
  QuestionDotParenthesisOpen,
  QuestionQuestion,
  QuestionQuestionEquals,
  Semicolon,
  Slash,
  SlashEquals,
  Tilde,
}

/// Map of keyword strings to their corresponding token type.
pub static KEYWORDS_BY_STR: Lazy<HashMap<&'static str, TT>> =
  Lazy::new(|| HashMap::from_iter(KEYWORDS_MAPPING.iter().map(|(&tt, &name)| (name, tt))));

// These can be used as parameter and variable names.
pub static UNRESERVED_KEYWORDS: Lazy<HashSet<TT>> = Lazy::new(|| {
  let mut set = HashSet::<TT>::new();
  set.insert(TT::KeywordAs);
  set.insert(TT::KeywordAsync);
  set.insert(TT::KeywordConstructor);
  set.insert(TT::KeywordFrom);
  set.insert(TT::KeywordGet);
  set.insert(TT::KeywordLet);
  set.insert(TT::KeywordOf);
  set.insert(TT::KeywordOut);
  set.insert(TT::KeywordSet);
  set.insert(TT::KeywordStatic);
  set.insert(TT::KeywordUsing);
  // TypeScript contextual keywords
  set.insert(TT::KeywordAbstract);
  set.insert(TT::KeywordAny);
  set.insert(TT::KeywordAsserts);
  set.insert(TT::KeywordBigIntType);
  set.insert(TT::KeywordBooleanType);
  set.insert(TT::KeywordDeclare);
  set.insert(TT::KeywordImplements);
  set.insert(TT::KeywordInfer);
  set.insert(TT::KeywordInterface);
  set.insert(TT::KeywordIs);
  set.insert(TT::KeywordKeyof);
  set.insert(TT::KeywordModule);
  set.insert(TT::KeywordNamespace);
  set.insert(TT::KeywordNever);
  set.insert(TT::KeywordVoid);
  set.insert(TT::KeywordNumberType);
  set.insert(TT::KeywordObjectType);
  set.insert(TT::KeywordOverride);
  set.insert(TT::KeywordPrivate);
  set.insert(TT::KeywordProtected);
  set.insert(TT::KeywordPublic);
  set.insert(TT::KeywordReadonly);
  set.insert(TT::KeywordSatisfies);
  set.insert(TT::KeywordStringType);
  set.insert(TT::KeywordSymbolType);
  set.insert(TT::KeywordType);
  set.insert(TT::KeywordUndefinedType);
  set.insert(TT::KeywordUnique);
  set.insert(TT::KeywordUnknown);
  set
});
pub static UNRESERVED_KEYWORD_STRS: Lazy<HashSet<&'static str>> = Lazy::new(|| {
  UNRESERVED_KEYWORDS
    .iter()
    .map(|tt| *KEYWORDS_MAPPING.get(tt).unwrap())
    .collect()
});

/// Returns the keyword token type for the given identifier string, if it is a keyword.
/// Escape sequences are handled by the lexer; callers should only pass raw identifier text.
pub fn keyword_from_str(ident: &str) -> Option<TT> {
  KEYWORDS_BY_STR.get(ident).copied()
}

#[derive(Clone, Debug)]
pub struct Token {
  pub loc: Loc,
  // Whether one or more whitespace characters appear immediately before this token, and at least
  // one of those whitespace characters is a line terminator.
  pub preceded_by_line_terminator: bool,
  pub typ: TT,
}

impl TT {
  /// Returns true if this token is any keyword (JavaScript or TypeScript).
  pub fn is_keyword(self) -> bool {
    matches!(
      self,
      TT::KeywordAs
        | TT::KeywordAsync
        | TT::KeywordAwait
        | TT::KeywordBreak
        | TT::KeywordCase
        | TT::KeywordCatch
        | TT::KeywordClass
        | TT::KeywordConst
        | TT::KeywordConstructor
        | TT::KeywordContinue
        | TT::KeywordDebugger
        | TT::KeywordDefault
        | TT::KeywordDelete
        | TT::KeywordDo
        | TT::KeywordElse
        | TT::KeywordEnum
        | TT::KeywordExport
        | TT::KeywordExtends
        | TT::KeywordFinally
        | TT::KeywordFor
        | TT::KeywordFrom
        | TT::KeywordFunction
        | TT::KeywordGet
        | TT::KeywordIf
        | TT::KeywordImport
        | TT::KeywordIn
        | TT::KeywordInstanceof
        | TT::KeywordLet
        | TT::KeywordNew
        | TT::KeywordOf
        | TT::KeywordOut
        | TT::KeywordReturn
        | TT::KeywordSet
        | TT::KeywordStatic
        | TT::KeywordSuper
        | TT::KeywordSwitch
        | TT::KeywordThis
        | TT::KeywordThrow
        | TT::KeywordTry
        | TT::KeywordTypeof
        | TT::KeywordUsing
        | TT::KeywordVar
        | TT::KeywordVoid
        | TT::KeywordWhile
        | TT::KeywordWith
        | TT::KeywordYield
        | TT::KeywordAbstract
        | TT::KeywordAccessor
        | TT::KeywordAny
        | TT::KeywordAsserts
        | TT::KeywordBigIntType
        | TT::KeywordBooleanType
        | TT::KeywordDeclare
        | TT::KeywordImplements
        | TT::KeywordInfer
        | TT::KeywordInterface
        | TT::KeywordIs
        | TT::KeywordKeyof
        | TT::KeywordModule
        | TT::KeywordNamespace
        | TT::KeywordNever
        | TT::KeywordNumberType
        | TT::KeywordObjectType
        | TT::KeywordOverride
        | TT::KeywordPrivate
        | TT::KeywordProtected
        | TT::KeywordPublic
        | TT::KeywordReadonly
        | TT::KeywordSatisfies
        | TT::KeywordStringType
        | TT::KeywordSymbolType
        | TT::KeywordType
        | TT::KeywordUndefinedType
        | TT::KeywordUnique
        | TT::KeywordUnknown
    )
  }
}

impl Token {
  pub fn error(&self, typ: SyntaxErrorType) -> SyntaxError {
    self.loc.error(typ, Some(self.typ))
  }
}
