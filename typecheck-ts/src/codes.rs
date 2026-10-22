//! Registry of diagnostic codes emitted by `typecheck-ts`.
//!
//! Each [`Code`] documents the expected shape of diagnostics the checker emits:
//! the short description, where the primary span should point, and any
//! additional labels or notes that accompany the diagnostic.

use diagnostics::{sort_diagnostics, sort_labels, Diagnostic, Span};

/// Metadata describing a diagnostic code.
#[derive(Clone, Copy, Debug)]
pub struct Code {
  /// Stable string identifier, e.g. `TC0005`.
  pub id: &'static str,
  /// Short description of what the diagnostic reports.
  pub description: &'static str,
  /// Guidance for where the primary span should be anchored.
  pub primary_span: &'static str,
  /// Expected labels attached to the diagnostic (primary and secondary).
  pub labels: &'static [&'static str],
  /// Expected notes automatically added to the diagnostic.
  pub notes: &'static [&'static str],
}

impl Code {
  pub const fn new(
    id: &'static str,
    description: &'static str,
    primary_span: &'static str,
    labels: &'static [&'static str],
    notes: &'static [&'static str],
  ) -> Self {
    Code {
      id,
      description,
      primary_span,
      labels,
      notes,
    }
  }

  /// Identifier as a plain string (useful for comparisons in tests).
  pub const fn as_str(&self) -> &'static str {
    self.id
  }

  /// Construct an error diagnostic tagged with this code and its expected notes.
  pub fn error(&self, message: impl Into<String>, primary: Span) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(self.id, message, primary);
    for note in self.notes {
      diagnostic.push_note(*note);
    }
    diagnostic
  }

  /// Construct a warning diagnostic tagged with this code and its expected
  /// notes.
  pub fn warning(&self, message: impl Into<String>, primary: Span) -> Diagnostic {
    let mut diagnostic = Diagnostic::warning(self.id, message, primary);
    for note in self.notes {
      diagnostic.push_note(*note);
    }
    diagnostic
  }
}

/// Sort labels inside each diagnostic and then the diagnostics themselves to
/// keep outputs deterministic regardless of traversal order.
pub fn normalize_diagnostics(diagnostics: &mut Vec<Diagnostic>) {
  for diagnostic in diagnostics.iter_mut() {
    normalize_diagnostic(diagnostic);
  }
  sort_diagnostics(diagnostics);
}

/// Canonicalize label and note ordering within a single diagnostic.
pub fn normalize_diagnostic(diagnostic: &mut Diagnostic) {
  sort_labels(&mut diagnostic.labels);
  diagnostic.notes.sort();
}

/// Helper to format the checker message for implicit-`any` diagnostics.
///
/// The checker may discover implicit `any` types in multiple phases (signature
/// lowering, body checking, and global var typing). Keeping the message
/// identical across those phases allows [`normalize_diagnostics`] to
/// de-duplicate repeats deterministically.
pub fn implicit_any_message(name: Option<&str>) -> String {
  match name {
    Some(name) => format!("`{name}` implicitly has an `any` type"),
    None => "implicitly has an `any` type".to_string(),
  }
}

/// TC0001: No libraries were loaded.
///
/// - Primary span: zero-length span at the start of the checked file if known,
///   otherwise [`FileId(u32::MAX)`] as a placeholder.
/// - Labels: primary only.
/// - Notes: none.
pub const NO_LIBS_LOADED: Code = Code::new(
  "TC0001",
  "no default libraries loaded",
  "file start placeholder when no libs are available",
  &["primary: placeholder at start of file"],
  &[],
);

/// TC0002: Global augmentations are only partially supported by the legacy lib
/// checker.
///
/// - Primary span: zero-length span at the start of the library file that
///   contains `declare global`.
/// - Labels: primary only.
/// - Notes: none.
pub const PARTIAL_GLOBAL_AUGMENTATION: Code = Code::new(
  "TC0002",
  "global augmentations are only partially supported",
  "start of the lib file containing `declare global`",
  &["primary: start of offending lib"],
  &[],
);

/// TC0003: Unsupported global augmentation merging into an `any` global.
///
/// - Primary span: zero-length span at the start of the library file that
///   attempted the augmentation.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_GLOBAL_AUGMENTATION: Code = Code::new(
  "TC0003",
  "unsupported global augmentation",
  "start of the lib file performing the augmentation",
  &["primary: start of offending lib"],
  &[],
);

/// TC0004: A library file is not a `.d.ts` and is ignored for globals.
///
/// - Primary span: zero-length span at the start of the library file.
/// - Labels: primary only.
/// - Notes: none.
pub const NON_DTS_LIB: Code = Code::new(
  "TC0004",
  ".d.ts library expected",
  "start of the non-.d.ts library file",
  &["primary: start of non-.d.ts lib"],
  &[],
);

/// TC0005: Identifier could not be resolved (legacy / internal).
///
/// Prefer [`CANNOT_FIND_NAME`] (`TS2304`) for user-facing unresolved-name
/// diagnostics so codes match `tsc`. Keep this code for intentional internal
/// or legacy emitters that still key off `TC0005`.
///
/// - Primary span: the identifier token (or a zero-length placeholder for the
///   legacy lib checker which does not track offsets).
/// - Labels: primary only.
/// - Notes: none.
pub const UNKNOWN_IDENTIFIER: Code = Code::new(
  "TC0005",
  "unknown identifier",
  "identifier being resolved; legacy lib checker uses a zero-length placeholder",
  &["primary: identifier reference"],
  &[],
);

/// TS2304: Cannot find name '{0}'.
///
/// User-facing unresolved identifier / type-name diagnostic (tsc parity).
///
/// - Primary span: the identifier token (or a zero-length placeholder when the
///   emitter does not track offsets).
/// - Labels: primary only.
/// - Notes: none.
pub const CANNOT_FIND_NAME: Code = Code::new(
  "TS2304",
  "cannot find name",
  "identifier or type name being resolved",
  &["primary: identifier reference"],
  &[],
);

/// Format the standard tsc-shaped message for [`CANNOT_FIND_NAME`].
pub fn cannot_find_name_message(name: &str) -> String {
  format!("Cannot find name '{name}'.")
}

/// TS2694: Namespace '{0}' has no exported member '{1}'.
///
/// Emitted for unresolved qualified JSDoc type references such as
/// `@type {exports.SomeName}` when `SomeName` was not bound as a typedef export
/// (e.g. nameless `@typedef` on a bare `exports.SomeName;` expression).
///
/// - Primary span: the rightmost name segment (`SomeName`).
/// - Labels: primary only.
/// - Notes: none.
pub const NAMESPACE_NO_EXPORTED_MEMBER: Code = Code::new(
  "TS2694",
  "namespace has no exported member",
  "rightmost segment of the qualified type name",
  &["primary: exported member name"],
  &[],
);

/// Format the standard tsc-shaped message for [`NAMESPACE_NO_EXPORTED_MEMBER`].
pub fn namespace_no_exported_member_message(namespace: &str, member: &str) -> String {
  format!("Namespace '{namespace}' has no exported member '{member}'.")
}

/// TS8024: JSDoc '@param' tag has name '{0}', but there is no parameter with that name.
///
/// Emitted under checkJs when a root `@param {T} name` does not match any
/// identifier parameter on the host function (and is not positionally tied to a
/// binding-pattern parameter, and did not absorb nested `name.prop` children).
///
/// - Primary span: the `@param` name (`unrelated`).
/// - Labels: primary only.
/// - Notes: none.
pub const JSDOC_PARAM_TAG_UNUSED: Code = Code::new(
  "TS8024",
  "JSDoc @param tag name does not match any parameter",
  "unmatched @param name",
  &["primary: @param name"],
  &[],
);

/// Format the standard tsc-shaped message for [`JSDOC_PARAM_TAG_UNUSED`].
pub fn jsdoc_param_tag_unused_message(name: &str) -> String {
  format!("JSDoc '@param' tag has name '{name}', but there is no parameter with that name.")
}

/// TS8032: Qualified name '{0}' is not allowed without a leading '@param {object} {1}'.
///
/// Emitted under checkJs when a nested `@param {T} opts.x` (or deeper path) appears
/// without an immediate parent `@param {object} opts` / `@param {object} opts.mid`
/// to attach the property to.
///
/// - Primary span: the qualified parameter name (`opts.x`).
/// - Labels: primary only.
/// - Notes: none.
pub const JSDOC_QUALIFIED_PARAM_MISSING_PARENT: Code = Code::new(
  "TS8032",
  "qualified JSDoc @param name missing leading object parent",
  "qualified @param name",
  &["primary: qualified parameter name"],
  &[],
);

/// Format the standard tsc-shaped message for [`JSDOC_QUALIFIED_PARAM_MISSING_PARENT`].
pub fn jsdoc_qualified_param_missing_parent_message(qualified: &str, parent: &str) -> String {
  format!(
    "Qualified name '{qualified}' is not allowed without a leading '@param {{object}} {parent}'."
  )
}

/// TS2353: Fresh object literal has an excess property not present in the
/// target type (`Object literal may only specify known properties...`).
///
/// - Primary span: the excess property key (tsc-aligned), falling back to the
///   object literal / JSX attributes span when a key loc is unavailable.
/// - Labels: primary only.
/// - Notes: none.
pub const EXCESS_PROPERTY: Code = Code::new(
  "TS2353",
  "excess property in object literal",
  "excess property key in the fresh object literal",
  &["primary: excess property key"],
  &[],
);

/// Format the standard tsc-shaped message for [`EXCESS_PROPERTY`].
pub fn excess_property_message(prop: &str, target: &str) -> String {
  format!(
    "Object literal may only specify known properties, and '{prop}' does not exist in type '{target}'."
  )
}

/// TS2322: Source type is not assignable to the target type.
///
/// - Primary span: the source expression being assigned.
/// - Labels: primary only.
/// - Notes: none.
pub const TYPE_MISMATCH: Code = Code::new(
  "TS2322",
  "type mismatch",
  "source expression being assigned",
  &["primary: source expression"],
  &[],
);

/// TS2352: Type assertion between insufficiently overlapping types.
///
/// Emitted for `<T>e` / `e as T` when neither type is assignable to the other
/// (tsc `checkTypeAssertionExpression`), e.g. `<Derived>null` under
/// `strictNullChecks`.
///
/// - Primary span: the assertion expression.
/// - Labels: primary only.
/// - Notes: none.
pub const TYPE_ASSERTION_NO_OVERLAP: Code = Code::new(
  "TS2352",
  "type assertion does not sufficiently overlap",
  "type assertion expression",
  &["primary: type assertion expression"],
  &[],
);

/// TS2539: Cannot assign to '{0}' because it is not a variable.
///
/// Emitted for assignments to the ambient globals `undefined` / `NaN` /
/// `Infinity` (`nullAssignedToUndefined.ts`).
///
/// - Primary span: the LHS identifier.
/// - Labels: primary only.
/// - Notes: none.
pub const CANNOT_ASSIGN_NON_VARIABLE: Code = Code::new(
  "TS2539",
  "cannot assign to non-variable",
  "left-hand side identifier that is not a variable",
  &["primary: left-hand side identifier"],
  &[],
);

/// Format the standard tsc-shaped message for [`CANNOT_ASSIGN_NON_VARIABLE`].
pub fn cannot_assign_non_variable_message(name: &str) -> String {
  format!("Cannot assign to '{name}' because it is not a variable.")
}

/// TS2741: A single required property is missing from the source type.
///
/// Prefer this over [`TYPE_MISMATCH`] when assignability fails solely because
/// the target has one required property absent from the source (tsc
/// `reportUnmatchedProperty` with `props.length === 1`).
///
/// - Primary span: the source expression / binding being assigned (same as TS2322).
/// - Labels: primary only.
/// - Notes: none.
pub const MISSING_REQUIRED_PROPERTY: Code = Code::new(
  "TS2741",
  "missing required property",
  "source expression being assigned",
  &["primary: source expression"],
  &[],
);

/// TS2739: Multiple required properties are missing from the source type.
///
/// Sibling of [`MISSING_REQUIRED_PROPERTY`] for `props.length > 1`.
///
/// - Primary span: the source expression / binding being assigned (same as TS2322).
/// - Labels: primary only.
/// - Notes: none.
pub const MISSING_PROPERTIES: Code = Code::new(
  "TS2739",
  "missing required properties",
  "source expression being assigned",
  &["primary: source expression"],
  &[],
);

/// TS18010: An accessibility modifier cannot be used with a private identifier.
///
/// - Primary span: the private identifier (modifier span not retained in AST).
/// - Labels: primary only.
/// - Notes: none.
pub const ACCESSIBILITY_WITH_PRIVATE_IDENTIFIER: Code = Code::new(
  "TS18010",
  "an accessibility modifier cannot be used with a private identifier",
  "private identifier class member with public/private/protected",
  &["primary: private identifier"],
  &[],
);

/// TS18019: `'{0}'` modifier cannot be used with a private identifier.
///
/// Used for `declare` / `abstract` (and similar) on `#` members.
///
/// - Primary span: the private identifier.
/// - Labels: primary only.
/// - Notes: none.
pub const MODIFIER_WITH_PRIVATE_IDENTIFIER: Code = Code::new(
  "TS18019",
  "modifier cannot be used with a private identifier",
  "private identifier class member with an illegal modifier",
  &["primary: private identifier"],
  &[],
);

/// TS1024: `'readonly'` modifier can only appear on a property declaration or
/// index signature.
///
/// - Primary span: the member name (readonly keyword span not retained).
/// - Labels: primary only.
/// - Notes: none.
pub const READONLY_MODIFIER_INVALID: Code = Code::new(
  "TS1024",
  "readonly modifier can only appear on a property declaration or index signature",
  "readonly on a method or accessor",
  &["primary: member name"],
  &[],
);

/// TS1031: `'{0}'` modifier cannot appear on class elements of this kind.
///
/// Used for `declare` on methods / accessors (fields allow `declare` except
/// with private identifiers, which use TS18019).
///
/// - Primary span: the member name.
/// - Labels: primary only.
/// - Notes: none.
pub const MODIFIER_ON_WRONG_CLASS_ELEMENT: Code = Code::new(
  "TS1031",
  "modifier cannot appear on class elements of this kind",
  "declare (or similar) on a non-field class element",
  &["primary: member name"],
  &[],
);

/// TS1042: `'{0}'` modifier cannot be used here.
///
/// Used for `async` on getters / setters.
///
/// - Primary span: the member name.
/// - Labels: primary only.
/// - Notes: none.
pub const MODIFIER_CANNOT_BE_USED_HERE: Code = Code::new(
  "TS1042",
  "modifier cannot be used here",
  "async on a getter or setter",
  &["primary: member name"],
  &[],
);

/// TS1029: `'{0}' modifier must precede '{1}' modifier.`
///
/// Used for wrong-order class member modifiers (e.g. `async static` →
/// `'static' modifier must precede 'async' modifier`).
///
/// - Primary span: the later (mis-ordered) modifier keyword.
/// - Labels: primary only.
/// - Notes: none.
pub const MODIFIER_MUST_PRECEDE: Code = Code::new(
  "TS1029",
  "modifier must precede another modifier",
  "the later modifier keyword (e.g. static in `async static`)",
  &["primary: later modifier keyword"],
  &[],
);

/// TS2350: Only a void function can be called with the 'new' keyword.
///
/// Emitted when `new` is applied to a callable with call signatures but no
/// construct signatures, and the call return type is not `void`.
///
/// - Primary span: the `new` call expression.
/// - Labels: primary only.
/// - Notes: none.
pub const ONLY_VOID_NEW: Code = Code::new(
  "TS2350",
  "only a void function can be called with the 'new' keyword",
  "new expression on a non-void callable",
  &["primary: new expression"],
  &[],
);

/// TS18046: `'{0}' is of type 'unknown'`.
///
/// Emitted by tsc `checkNonNullType` under `strictNullChecks` when an
/// entity-name expression of type `unknown` is used as a property-access
/// receiver (including private-identifier access). Sibling of
/// [`OBJECT_IS_OF_TYPE_UNKNOWN`] (TS2571) for non-entity-name expressions.
///
/// - Primary span: the unknown-typed receiver expression (`thing` in
///   `thing.#foo`).
/// - Labels: primary only.
/// - Notes: none.
pub const IS_OF_TYPE_UNKNOWN: Code = Code::new(
  "TS18046",
  "is of type unknown",
  "entity-name expression whose type is unknown",
  &["primary: unknown-typed entity-name expression"],
  &[],
);

/// TS18047: Identifier is possibly `null`.
///
/// Emitted under `strictNullChecks` when an identifier whose flow type still
/// includes `null` is used where a non-null value is required (e.g. the RHS of
/// `in` / property access). Sibling of [`POSSIBLY_UNDEFINED`] (TS18048).
///
/// - Primary span: the identifier expression being accessed.
/// - Labels: primary only.
/// - Notes: none.
pub const POSSIBLY_NULL: Code = Code::new(
  "TS18047",
  "possibly null",
  "identifier expression that might still be null",
  &["primary: identifier expression"],
  &[],
);

/// TS18048: Identifier is possibly `undefined`.
///
/// TypeScript emits this diagnostic when an identifier is used without
/// optional chaining / a non-null assertion but its flow type still includes
/// `undefined`.
///
/// - Primary span: the identifier expression being accessed.
/// - Labels: primary only.
/// - Notes: none.
pub const POSSIBLY_UNDEFINED: Code = Code::new(
  "TS18048",
  "possibly undefined",
  "identifier expression that might still be undefined",
  &["primary: identifier expression"],
  &[],
);

/// TS2571: Object is of type `unknown`.
///
/// Emitted by tsc `checkNonNullType` when the operand type is `unknown`
/// (notably the RHS of `in` / private-identifier-in). Distinct from
/// [`POSSIBLY_NULL`] / [`POSSIBLY_UNDEFINED`].
///
/// - Primary span: the expression of type `unknown`.
/// - Labels: primary only.
/// - Notes: none.
pub const OBJECT_IS_OF_TYPE_UNKNOWN: Code = Code::new(
  "TS2571",
  "object is of type unknown",
  "expression whose type is unknown",
  &["primary: unknown-typed expression"],
  &[],
);

/// TS1451: Private identifiers are only allowed in class bodies and may only
/// be used as part of a class member declaration, property access, or on the
/// left-hand-side of an `in` expression.
///
/// Emitted for bare / parenthesized private identifiers that are not in a
/// legal `#id in expr` or `obj.#id` position (e.g. `(#field) in v`).
///
/// - Primary span: the private identifier.
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_IDENTIFIER_BAD_POSITION: Code = Code::new(
  "TS1451",
  "private identifiers are only allowed in class bodies as member declaration, property access, or left-hand-side of in",
  "private identifier expression",
  &["primary: private identifier"],
  &[],
);

/// TS2406: The left-hand side of a `for...in` statement must be a variable or
/// a property access.
///
/// - Primary span: the illegal left-hand side (e.g. a bare private identifier).
/// - Labels: primary only.
/// - Notes: none.
pub const FOR_IN_LHS_INVALID: Code = Code::new(
  "TS2406",
  "the left-hand side of a for...in statement must be a variable or a property access",
  "for-in left-hand side",
  &["primary: for-in LHS"],
  &[],
);

/// TS2407: The right-hand side of a `for...in` statement must be of type
/// `any`, an object type or a type parameter.
///
/// - Primary span: the for-in RHS expression.
/// - Labels: primary only.
/// - Notes: none.
pub const FOR_IN_RHS_INVALID: Code = Code::new(
  "TS2407",
  "the right-hand side of a for...in statement must be of type any, an object type or a type parameter",
  "for-in right-hand side",
  &["primary: for-in RHS"],
  &[],
);

/// TS2345: Argument of type is not assignable to parameter of type.
///
/// `typecheck-ts` reports the more specific TS2345 code for call/new argument
/// checks, matching `tsc`'s behavior. The underlying message is still a general
/// "type mismatch" and is normalized by the harness, but the numeric code is
/// used by difftsc to track parity.
///
/// - Primary span: the argument expression being checked.
/// - Labels: primary only.
/// - Notes: none.
pub const ARGUMENT_TYPE_MISMATCH: Code = Code::new(
  "TS2345",
  "argument type mismatch",
  "argument expression being checked",
  &["primary: argument expression"],
  &[],
);

/// TS2558: Expected N type arguments, but got M.
///
/// - Primary span: the instantiation expression carrying explicit type arguments.
/// - Labels: primary only.
/// - Notes: none.
pub const WRONG_TYPE_ARGUMENT_COUNT: Code = Code::new(
  "TS2558",
  "wrong number of type arguments",
  "instantiation expression type argument list",
  &["primary: instantiation expression"],
  &[],
);

/// TS2344: Type argument does not satisfy constraint.
///
/// - Primary span: the instantiation expression carrying explicit type arguments.
/// - Labels: primary only.
/// - Notes: none.
pub const TYPE_ARGUMENT_CONSTRAINT_VIOLATION: Code = Code::new(
  "TS2344",
  "type argument does not satisfy constraint",
  "instantiation expression type argument list",
  &["primary: instantiation expression"],
  &[],
);

/// TC0008: Property access on a global that does not declare the property.
///
/// - Primary span: zero-length placeholder at the start of the file flagged by
///   the legacy lib checker.
/// - Labels: primary only.
/// - Notes: none.
pub const MISSING_GLOBAL_PROPERTY: Code = Code::new(
  "TC0008",
  "property does not exist on global",
  "file start placeholder when a global property is missing",
  &["primary: placeholder at start of file"],
  &[],
);

/// TS2339: Property does not exist on type.
///
/// - Primary span: the property name being accessed.
/// - Labels: primary only.
/// - Notes: none.
pub const PROPERTY_DOES_NOT_EXIST: Code = Code::new(
  "TS2339",
  "property does not exist on type",
  "property name within a member expression",
  &["primary: property name"],
  &[],
);

/// TS2540: Cannot assign to a read-only property.
///
/// Emitted for assignments to `readonly` fields (outside constructor `this`
/// init), getter-only accessors (including in constructors), and other
/// readonly object properties.
///
/// - Primary span: the property name on the left-hand side.
/// - Labels: primary only.
/// - Notes: none.
pub const CANNOT_ASSIGN_READONLY: Code = Code::new(
  "TS2540",
  "cannot assign to a read-only property",
  "property name within an assignment left-hand side",
  &["primary: property name"],
  &[],
);

/// TS18016: Private identifiers are not allowed outside class bodies.
///
/// Emitted for:
/// - private-name *declarations* outside a class element list (object-literal
///   properties/methods/accessors; type/interface/object-type property or
///   method signatures, including nested ambient type literals)
/// - private-name *access* outside a class when the receiver is any-like
///   (`any` / `never` / error-recovery `any`, e.g. `exports.#x`, or
///   `A.prototype.#no` where bare callables expose `prototype: any`) and
///   there is no lexically scoped private of that name
///
/// - Primary span: the private identifier for object-literal members, type
///   property signatures, and any-like access; the full method signature for
///   type method signatures (matching tsc baselines).
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_IDENTIFIERS_OUTSIDE_CLASS: Code = Code::new(
  "TS18016",
  "private identifiers are not allowed outside class bodies",
  "private name declaration/access outside a class body",
  &["primary: private identifier or method signature"],
  &[],
);

/// TS18009: Private identifiers cannot be used as parameters.
///
/// Emitted when a binding name in a parameter list is a private identifier
/// (tsc parser `parseIdentifierOrPattern` with this diagnostic; we recover in
/// parse-js and report from the checker).
///
/// - Primary span: the private identifier (`#foo`).
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_IDENTIFIERS_AS_PARAMETERS: Code = Code::new(
  "TS18009",
  "private identifiers cannot be used as parameters",
  "private identifier in a parameter binding",
  &["primary: private identifier"],
  &[],
);

/// TS18012: `#constructor` is a reserved word.
///
/// Emitted for a class member named `#constructor` (tsc binder
/// `checkPrivateIdentifier`).
///
/// - Primary span: the private identifier (`#constructor`).
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_CONSTRUCTOR_RESERVED: Code = Code::new(
  "TS18012",
  "'#constructor' is a reserved word",
  "private identifier `#constructor` on a class member",
  &["primary: private identifier"],
  &[],
);

/// TS18024: An enum member cannot be named with a private identifier.
///
/// - Primary span: the private identifier (`#x`).
/// - Labels: primary only.
/// - Notes: none.
pub const ENUM_MEMBER_PRIVATE_IDENTIFIER: Code = Code::new(
  "TS18024",
  "an enum member cannot be named with a private identifier",
  "private identifier enum member name",
  &["primary: private identifier"],
  &[],
);

/// TS18028: Private identifiers are only available when targeting ES2015+.
///
/// Emitted for each private class member declaration when
/// `compilerOptions.target` is below ES2015 (ES3/ES5).
///
/// - Primary span: the private identifier on the member.
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_IDENTIFIERS_REQUIRE_ES2015: Code = Code::new(
  "TS18028",
  "private identifiers are only available when targeting ECMAScript 2015 and higher",
  "private identifier class member under ES5/ES3 target",
  &["primary: private identifier"],
  &[],
);

/// TS18029: Private identifiers are not allowed in variable declarations.
///
/// Emitted when a `var`/`let`/`const`/`using` binding name is a private
/// identifier (tsc parser diagnostic; parse-js recovers and we report here).
///
/// - Primary span: the private identifier (`#foo`).
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_IDENTIFIERS_IN_VARIABLE_DECLARATIONS: Code = Code::new(
  "TS18029",
  "private identifiers are not allowed in variable declarations",
  "private identifier in a variable binding",
  &["primary: private identifier"],
  &[],
);

/// TS18030: An optional chain cannot contain private identifiers.
///
/// Emitted for `obj?.#x` / `obj?.#x()` (tsc parser
/// `parsePropertyAccessExpressionRest`). Takes precedence over TS2339 /
/// visibility diagnostics on the same access.
///
/// - Primary span: the private identifier (`#x`).
/// - Labels: primary only.
/// - Notes: none.
pub const OPTIONAL_CHAIN_PRIVATE_IDENTIFIER: Code = Code::new(
  "TS18030",
  "an optional chain cannot contain private identifiers",
  "private identifier in an optional chain property access",
  &["primary: private identifier"],
  &[],
);

/// TS2376: A `super` call must be the first statement in the constructor to
/// refer to `super` or `this` when a derived class contains initialized
/// properties, parameter properties, or private identifiers.
///
/// Suppressed under native class-field semantics (`useDefineForClassFields`
/// with `target` ES2022/ESNext); TS17009 still applies for bare `this` access.
///
/// - Primary span: the `constructor` keyword.
/// - Labels: primary only.
/// - Notes: none.
pub const SUPER_MUST_BE_FIRST_IN_CONSTRUCTOR: Code = Code::new(
  "TS2376",
  "super call must be first statement when referring to this/super with initialized properties or private identifiers",
  "constructor keyword",
  &["primary: constructor keyword"],
  &[],
);

/// TS17009: `super` must be called before accessing `this` in the constructor
/// of a derived class.
///
/// - Primary span: the `this` expression.
/// - Labels: primary only.
/// - Notes: none.
pub const SUPER_MUST_BE_CALLED_BEFORE_THIS: Code = Code::new(
  "TS17009",
  "super must be called before accessing this in a derived class constructor",
  "this expression before super()",
  &["primary: this expression"],
  &[],
);

/// TS2803: Cannot assign to a private method. Private methods are not writable.
///
/// Emitted for any write to a lexically declared private method (`#m`), including
/// definite assignment, destructuring targets, and `++`/`--`. Unlike TS2540,
/// this does **not** suppress ordinary assignability diagnostics (TS2322) —
/// tsc reports both when the RHS is also mistyped.
///
/// - Primary span: the private identifier (`#m`) on the left-hand side.
/// - Labels: primary only.
/// - Notes: none.
pub const CANNOT_ASSIGN_PRIVATE_METHOD: Code = Code::new(
  "TS2803",
  "cannot assign to a private method",
  "private method name within an assignment left-hand side",
  &["primary: private method name"],
  &[],
);

/// TS2300: Duplicate identifier.
///
/// For private names, emitted by class-body uniqueness checking when two
/// same-side (both instance or both static) private elements collide — fields,
/// methods vs non-methods, and same-kind accessors. Method/method pairs are
/// deferred to overload checking (TS2393); getter+setter pairs are allowed.
///
/// - Primary span: the private identifier (`#foo`).
/// - Labels: primary only.
/// - Notes: none.
pub const DUPLICATE_IDENTIFIER: Code = Code::new(
  "TS2300",
  "duplicate identifier",
  "duplicate private identifier name",
  &["primary: private identifier"],
  &[],
);

/// TS2393: Duplicate function implementation.
///
/// Emitted for class methods when two or more declarations of the same name on
/// the same side (instance vs static) have implementation bodies. All method
/// declarations in that overload group (including body-less signatures) receive
/// the diagnostic, matching tsc `checkFunctionOrMethodDeclaration`.
///
/// - Primary span: the method name.
/// - Labels: primary only.
/// - Notes: none.
pub const DUPLICATE_FUNCTION_IMPLEMENTATION: Code = Code::new(
  "TS2393",
  "duplicate function implementation",
  "method name of a duplicate implementation",
  &["primary: method name"],
  &[],
);

/// TS2403: Subsequent variable declarations must have the same type.
///
/// Emitted when a later `var` declarator merges with an earlier one of the same
/// name and the declared/inferred types are not identical (tsc var merging).
///
/// - Primary span: the later binding name.
/// - Labels: primary only.
/// - Notes: none (related TS6203 "also declared here" is deferred).
pub const SUBSEQUENT_VARIABLE_DECLARATIONS: Code = Code::new(
  "TS2403",
  "subsequent variable declarations must have the same type",
  "later variable name with a mismatched type",
  &["primary: variable name"],
  &[],
);

/// TS2717: Subsequent property declarations must have the same type.
///
/// Emitted when a later class field shares a name with an earlier value-side
/// declaration (method or field) on the same side, and the declared/inferred
/// types are not identical.
///
/// - Primary span: the later property name.
/// - Labels: primary only.
/// - Notes: none (related "also declared here" is deferred).
pub const SUBSEQUENT_PROPERTY_DECLARATIONS: Code = Code::new(
  "TS2717",
  "subsequent property declarations must have the same type",
  "later property name with a mismatched type",
  &["primary: property name"],
  &[],
);

/// TS2804: Duplicate private identifier shared by static and instance elements.
///
/// Private names share one lexical scope across static and instance sides
/// (tc39 class fields). Emitting when a later declaration differs in staticness
/// from an earlier one with the same spelling.
///
/// - Primary span: the later private identifier (`#foo`).
/// - Labels: primary only.
/// - Notes: none.
pub const DUPLICATE_PRIVATE_STATIC_INSTANCE: Code = Code::new(
  "TS2804",
  "duplicate private identifier across static and instance elements",
  "later private identifier that conflicts with the other side",
  &["primary: private identifier"],
  &[],
);

/// TS2806: Private accessor was defined without a getter.
///
/// Emitted when a setter-only private accessor (`set #x`) is read — including
/// plain reads, compound assignments (`+=`), and nested reads
/// (`this.#x.prop = …`). Definite writes (`this.#x = …`, destructuring
/// assignment targets) do not emit this diagnostic.
///
/// - Primary span: the full private property access expression (`this.#x`).
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_ACCESSOR_NO_GETTER: Code = Code::new(
  "TS2806",
  "private accessor was defined without a getter",
  "full private property access expression",
  &["primary: private property access"],
  &[],
);

/// TS18011: The operand of a `delete` operator cannot be a private identifier.
///
/// Emitted for `delete obj.#x` / `delete this.#x` (tsc `checkDeleteExpression`).
/// Often paired with [`DELETE_MUST_BE_OPTIONAL`] (TS2790) when the private
/// field type is not optional under `strictNullChecks`.
///
/// - Primary span: the full property access expression (`this.#x`).
/// - Labels: primary only.
/// - Notes: none.
pub const DELETE_PRIVATE_IDENTIFIER: Code = Code::new(
  "TS18011",
  "the operand of a delete operator cannot be a private identifier",
  "full private property access expression",
  &["primary: private property access"],
  &[],
);

/// TS2790: The operand of a `delete` operator must be optional.
///
/// Emitted under `strictNullChecks` when deleting a property whose type is not
/// optional / does not include `undefined` (and is not `any`/`unknown`/`never`).
///
/// - Primary span: the property access / element access expression.
/// - Labels: primary only.
/// - Notes: none.
pub const DELETE_MUST_BE_OPTIONAL: Code = Code::new(
  "TS2790",
  "the operand of a delete operator must be optional",
  "property access / element access expression",
  &["primary: delete operand access expression"],
  &[],
);

/// TS18013: Property is not accessible outside its declaring class because it
/// has a private identifier.
///
/// Emitted when a private-name access (`obj.#x`) resolves to a private member
/// on the left operand's type, but the access site is not in the lexical scope
/// of that declaring class (including derived-class and cross-class access).
///
/// - Primary span: the private identifier (`#x`).
/// - Labels: primary only.
/// - Notes: none.
pub const PRIVATE_IDENTIFIER_NOT_ACCESSIBLE: Code = Code::new(
  "TS18013",
  "property is not accessible outside class because it has a private identifier",
  "private identifier in a property access",
  &["primary: private identifier"],
  &[],
);

/// TS18014: Private identifier is shadowed by another private with the same
/// spelling in a nested class.
///
/// Emitted when a nested class declares `#x` and an access on an outer-class
/// typed receiver uses that spelling (the outer declaration is shadowed).
///
/// - Primary span: the private identifier (`#x`).
/// - Labels: primary only (related-info notes deferred).
/// - Notes: none.
pub const PRIVATE_IDENTIFIER_SHADOWED: Code = Code::new(
  "TS18014",
  "property cannot be accessed because it is shadowed by another private identifier",
  "private identifier in a property access",
  &["primary: private identifier"],
  &[],
);

/// TS2395: Merged declarations must be all exported or all local.
///
/// - Primary span: the identifier name of the declaration participating in the merge.
/// - Labels: primary only.
/// - Notes: none.
pub const MERGED_DECLARATIONS_EXPORT_MISMATCH: Code = Code::new(
  "TS2395",
  "merged declarations must be all exported or all local",
  "declaration name participating in the merge",
  &["primary: declaration name"],
  &[],
);

/// TS2434: Namespace declaration cannot appear before the class/function it merges with.
///
/// - Primary span: the namespace name being merged.
/// - Labels: primary only.
/// - Notes: none.
pub const NAMESPACE_BEFORE_MERGE_TARGET: Code = Code::new(
  "TS2434",
  "namespace declaration cannot appear before the class/function it merges with",
  "namespace name participating in the merge",
  &["primary: namespace name"],
  &[],
);

/// TS2318: Cannot find global type.
///
/// TypeScript reports this diagnostic when the default library set is disabled
/// (for example via `/// <reference no-default-lib="true" />` or `--noLib`) and
/// the program does not provide the core global type declarations required by
/// the checker (e.g. `Array`, `String`).
///
/// - Primary span: placeholder span (tsc reports `file: null` with `0..0` range).
/// - Labels: primary only.
/// - Notes: none.
pub const CANNOT_FIND_GLOBAL_TYPE: Code = Code::new(
  "TS2318",
  "cannot find global type",
  "placeholder span when core global types are missing",
  &["primary: placeholder span"],
  &[],
);

/// TS2448: Block-scoped variable used before its declaration (TDZ).
///
/// Emitted when a `let`/`const` binding is referenced in its own initializer or
/// in the RHS of a `for`/`for-in`/`for-of` that declares it (e.g.
/// `for (let v of v)`). Distinct from [`USE_BEFORE_ASSIGNMENT`] (TS2454).
///
/// - Primary span: the identifier token being read.
/// - Labels: primary only (tsc also attaches a related “declared here” note;
///   we may add that later).
/// - Notes: none.
pub const BLOCK_SCOPED_USED_BEFORE_DECLARATION: Code = Code::new(
  "TS2448",
  "block-scoped variable used before its declaration",
  "identifier reference in TDZ of its own binding",
  &["primary: identifier reference"],
  &[],
);

/// TS2454: Variable is used before it has been assigned.
///
/// - Primary span: the identifier token being read.
/// - Labels: primary only.
/// - Notes: none.
pub const USE_BEFORE_ASSIGNMENT: Code = Code::new(
  "TS2454",
  "variable used before assignment",
  "identifier reference that might not be assigned",
  &["primary: identifier reference"],
  &[],
);

/// TS2493: Tuple type of length N has no element at index K.
///
/// Emitted for a numeric literal element access on a fixed-length tuple when
/// the index is out of range (open-ended / rest tuples are exempt).
///
/// - Primary span: the index expression.
/// - Labels: primary only.
/// - Notes: none.
pub const TUPLE_INDEX_OUT_OF_BOUNDS: Code = Code::new(
  "TS2493",
  "tuple index out of bounds",
  "numeric index expression on a fixed-length tuple",
  &["primary: index expression"],
  &[],
);

/// TS2416: Property in type is not assignable to the same property in base type.
///
/// TypeScript emits this diagnostic when a class member conflicts with the
/// corresponding property declared in an implemented interface or base class.
///
/// - Primary span: the property name in the derived type declaration.
/// - Labels: primary only.
/// - Notes: none.
pub const PROPERTY_IN_TYPE_NOT_ASSIGNABLE_TO_BASE: Code = Code::new(
  "TS2416",
  "property not assignable to base type",
  "property name in the derived type declaration",
  &["primary: property name"],
  &[],
);

/// TS2430: Interface incorrectly extends interface.
///
/// Emitted when an interface `extends` a base but an owned member is not
/// assignable to the corresponding base member (so the derived interface would
/// not be a subtype of the base). Interface types are represented as
/// intersections for merging, which always subtype each base — this diagnostic
/// is checked separately against own members only.
///
/// - Primary span: the derived interface name.
/// - Labels: primary only.
/// - Notes: none.
pub const INTERFACE_INCORRECTLY_EXTENDS: Code = Code::new(
  "TS2430",
  "interface incorrectly extends interface",
  "derived interface name",
  &["primary: interface name"],
  &[],
);

/// TS1202: Import assignment cannot be used when targeting ECMAScript modules.
///
/// - Primary span: the full `import x = require("...")` statement.
/// - Labels: primary only.
/// - Notes: none.
pub const IMPORT_ASSIGNMENT_IN_ESM: Code = Code::new(
  "TS1202",
  "import assignment not allowed for ECMAScript module targets",
  "import assignment statement",
  &["primary: import assignment statement"],
  &[],
);

/// TS1203: Export assignment cannot be used when targeting ECMAScript modules.
///
/// - Primary span: the full `export = <expr>` statement.
/// - Labels: primary only.
/// - Notes: none.
pub const EXPORT_ASSIGNMENT_IN_ESM: Code = Code::new(
  "TS1203",
  "export assignment not allowed for ECMAScript module targets",
  "export assignment statement",
  &["primary: export assignment statement"],
  &[],
);

/// TS2729: Property is used before it has been initialized.
///
/// - Primary span: the property name within a `this.x` access in a class field initializer.
/// - Labels: primary only.
/// - Notes: none.
pub const PROPERTY_USED_BEFORE_INITIALIZATION: Code = Code::new(
  "TS2729",
  "property used before initialization",
  "property name within a class field initializer",
  &["primary: property name"],
  &[],
);

/// TS2715: Abstract property cannot be accessed in the constructor.
///
/// TypeScript forbids reading/writing abstract instance properties (fields /
/// accessors — not methods) via `this` during class initialization (constructor
/// body or instance field initializer), including inherited abstract props that
/// the current class has not yet implemented.
///
/// - Primary span: the property name (`this.x` / binding element).
/// - Labels: primary only.
/// - Notes: none.
pub const ABSTRACT_PROPERTY_IN_CONSTRUCTOR: Code = Code::new(
  "TS2715",
  "abstract property cannot be accessed in the constructor",
  "property name in a this-access during class initialization",
  &["primary: property name"],
  &[],
);

/// TS1267: Property cannot have an initializer because it is marked abstract.
///
/// - Primary span: the abstract property name.
/// - Labels: primary only.
/// - Notes: none.
pub const ABSTRACT_PROPERTY_INITIALIZER: Code = Code::new(
  "TS1267",
  "abstract property cannot have an initializer",
  "abstract property name with an initializer",
  &["primary: property name"],
  &[],
);

/// TS2564: Property has no initializer and is not definitely assigned in the
/// constructor (`strictPropertyInitialization` + `strictNullChecks`).
///
/// - Primary span: the property name in the class declaration.
/// - Labels: primary only.
/// - Notes: none.
pub const PROPERTY_NOT_DEFINITELY_ASSIGNED: Code = Code::new(
  "TS2564",
  "property has no initializer and is not definitely assigned in the constructor",
  "class instance property name",
  &["primary: property name"],
  &[],
);

/// TS2565: Property is used before being assigned in the constructor
/// (`strictPropertyInitialization` + `strictNullChecks`).
///
/// - Primary span: the property name in a `this.x` / `this.#x` access.
/// - Labels: primary only.
/// - Notes: none.
pub const PROPERTY_USED_BEFORE_ASSIGNED: Code = Code::new(
  "TS2565",
  "property is used before being assigned",
  "property name within a constructor this-access",
  &["primary: property name"],
  &[],
);

/// TS2612: Property will overwrite the base property in a derived class.
///
/// - Primary span: the property name in the derived class declaration.
/// - Labels: primary only.
/// - Notes: none.
pub const PROPERTY_WILL_OVERWRITE_BASE_PROPERTY: Code = Code::new(
  "TS2612",
  "property will overwrite base property",
  "property name in the derived class declaration",
  &["primary: property name"],
  &[],
);

/// TC1001: Module specifier could not be resolved.
///
/// - Primary span: the module specifier in an import/export statement or a
///   type-only `import("...")` / `typeof import("...")` reference.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_MODULE: Code = Code::new(
  "TC1001",
  "unresolved module specifier",
  "module specifier in an import/export statement or type-only import() reference",
  &["primary: module specifier span"],
  &[],
);

/// TS6053: Triple-slash `reference path` target could not be found.
///
/// - Primary span: the path string inside the triple-slash directive (excluding quotes).
/// - Labels: primary only.
/// - Notes: none.
pub const FILE_NOT_FOUND: Code = Code::new(
  "TS6053",
  "file not found",
  "reference path value",
  &["primary: reference path"],
  &[],
);

/// TS2688: Triple-slash `reference types` package could not be resolved.
///
/// - Primary span: the package name inside the triple-slash directive (excluding quotes).
/// - Labels: primary only.
/// - Notes: none.
pub const TYPE_DEFINITION_FILE_NOT_FOUND: Code = Code::new(
  "TS2688",
  "cannot find type definition file",
  "reference types value",
  &["primary: reference types package"],
  &[],
);

/// TS2726: Triple-slash `reference lib` target could not be found.
///
/// - Primary span: the lib name inside the triple-slash directive (excluding quotes).
/// - Labels: primary only.
/// - Notes: none.
pub const LIB_DEFINITION_FILE_NOT_FOUND: Code = Code::new(
  "TS2726",
  "cannot find lib definition file",
  "reference lib value",
  &["primary: reference lib name"],
  &[],
);

/// TC1007: Triple-slash `/// <reference lib="..." />` directive refers to an
/// unknown or unsupported library name.
///
/// - Primary span: the lib name inside the triple-slash directive.
/// - Labels: primary only.
/// - Notes: none.
pub const UNKNOWN_LIB_REFERENCE: Code = Code::new(
  "TC1007",
  "unknown lib reference",
  "lib name in a triple-slash reference directive",
  &["primary: lib name span"],
  &[],
);

/// TC1002: Export refers to a symbol that is not available.
///
/// - Primary span: the named export specifier or `export * as ...` alias.
/// - Labels: primary only.
/// - Notes: none.
pub const UNKNOWN_EXPORT: Code = Code::new(
  "TC1002",
  "unknown export",
  "export specifier that could not be resolved",
  &["primary: export specifier"],
  &[],
);

/// TC1003: Destructuring import pattern is not yet supported.
///
/// - Primary span: the pattern expression used in the import clause.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_IMPORT_PATTERN: Code = Code::new(
  "TC1003",
  "unsupported import pattern",
  "import clause pattern",
  &["primary: unsupported import pattern"],
  &[],
);

/// TC1004: Binding pattern is not yet supported in this context.
///
/// - Primary span: the unsupported binding pattern (variable, export, or type-only pattern).
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_PATTERN: Code = Code::new(
  "TC1004",
  "unsupported binding pattern",
  "binding pattern in the variable declaration",
  &["primary: unsupported binding pattern"],
  &[],
);

/// TC1005: Parameter binding pattern is not yet supported.
///
/// - Primary span: the parameter pattern.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_PARAM_PATTERN: Code = Code::new(
  "TC1005",
  "unsupported parameter pattern",
  "unsupported parameter binding pattern",
  &["primary: parameter pattern"],
  &[],
);

/// TS2554: Expected N arguments, but got M.
///
/// - Primary span: the callee name (e.g. `#method` / `foo`), matching tsc.
/// - Labels: primary only.
/// - Notes: none.
pub const ARGUMENT_COUNT_MISMATCH: Code = Code::new(
  "TS2554",
  "argument count mismatch",
  "callee name when the call supplies the wrong number of arguments",
  &["primary: callee identifier / private name"],
  &[],
);

/// TC2000: The callee is not callable / not constructable (no call or construct
/// signatures), or a single-signature call failed in a way that has not yet been
/// rewritten to a more specific tsc code (e.g. TS2345 / TS2554).
///
/// - Primary span: the call expression (or argument when available).
/// - Labels: primary only.
/// - Notes: may include the callee type.
pub const NO_OVERLOAD: Code = Code::new(
  "TC2000",
  "expression is not callable",
  "call expression when the callee has no applicable signatures",
  &["primary: call expression"],
  &[],
);

/// TS2769: No overload matches this call.
///
/// Emitted when a callable has multiple overload signatures and none apply.
/// Matches `tsc` code and argument-anchored primary span when the failure is an
/// argument type mismatch.
///
/// - Primary span: the first mismatched argument expression when known; otherwise
///   the call expression.
/// - Labels: primary only.
/// - Notes: may include candidate signatures and rejection reasons.
pub const NO_OVERLOAD_MATCHES: Code = Code::new(
  "TS2769",
  "no overload matches this call",
  "first mismatched argument (or call expression)",
  &["primary: mismatched argument expression"],
  &[],
);

/// TC2001: Multiple overloads were applicable for a call expression and the
/// checker could not select a best candidate.
///
/// - Primary span: the call expression.
/// - Labels: primary only.
/// - Notes: lists candidate signatures (truncated when many are present).
pub const AMBIGUOUS_OVERLOAD: Code = Code::new(
  "TC2001",
  "call is ambiguous",
  "call expression when multiple overloads apply",
  &["primary: call expression"],
  &[],
);

/// TC2008: Type reference could not be resolved or used incorrectly.
///
/// - Primary span: the referenced type name.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_TYPE_REFERENCE: Code = Code::new(
  "TC2008",
  "unresolved type reference",
  "type reference that could not be resolved",
  &["primary: type reference span"],
  &[],
);

/// TC2009: Qualified type reference could not be resolved or is unsupported.
///
/// - Primary span: the qualified type reference.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_QUALIFIED_NAME: Code = Code::new(
  "TC2009",
  "unsupported qualified type name",
  "qualified type reference that cannot be resolved",
  &["primary: qualified type reference"],
  &[],
);

/// TC2010: `import()` type could not be resolved.
///
/// - Primary span: the entire `import()` type expression.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_IMPORT_TYPE: Code = Code::new(
  "TC2010",
  "unresolved import type",
  "import() type expression that could not be resolved",
  &["primary: import() type expression"],
  &[],
);

/// TC2011: `typeof` type query could not resolve the referenced symbol.
///
/// - Primary span: the `typeof` query expression.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_TYPE_QUERY: Code = Code::new(
  "TC2011",
  "unresolved type query",
  "typeof query that could not be resolved",
  &["primary: typeof query span"],
  &[],
);

/// TC2012: `using` / `await using` initializer is not disposable.
///
/// - Primary span: the initializer expression for the `using` declarator.
/// - Labels: primary only.
/// - Notes: none.
pub const INVALID_USING_INITIALIZER: Code = Code::new(
  "TC2012",
  "invalid using initializer",
  "initializer expression in the using declarator",
  &["primary: using initializer expression"],
  &[],
);

/// TS1492: `using` declarations may not have binding patterns.
///
/// TypeScript currently restricts `using` / `await using` declarations to simple
/// identifiers (no destructuring patterns). Emit the same diagnostic so difftsc
/// can track parity.
///
/// - Primary span: the binding pattern.
/// - Labels: primary only.
/// - Notes: none.
pub const USING_BINDING_PATTERN: Code = Code::new(
  "TS1492",
  "using binding patterns are not allowed",
  "binding pattern in the using declaration",
  &["primary: using binding pattern"],
  &[],
);

/// TS2852: `await using` statements are only allowed in async contexts.
///
/// This aligns with the TypeScript compiler diagnostic emitted when an `await using`
/// declaration appears outside an async function and outside the top level of a module.
///
/// - Primary span: the `await` keyword of the `await using` declaration.
/// - Labels: primary only.
/// - Notes: none.
pub const AWAIT_USING_REQUIRES_ASYNC_CONTEXT: Code = Code::new(
  "TS2852",
  "await using requires async context",
  "`await` keyword of the `await using` declaration",
  &["primary: await keyword"],
  &[],
);

/// TC3000: Implicit `any` type (TypeScript `--noImplicitAny`).
///
/// This diagnostic is emitted when the checker would otherwise fall back to
/// `any` due to a missing annotation and lack of contextual typing.
///
/// - Primary span: the identifier (preferred) or binding pattern that receives
///   the implicit `any` type.
/// - Labels: primary only.
/// - Notes: none.
pub const IMPLICIT_ANY: Code = Code::new(
  "TC3000",
  "implicit any type",
  "identifier or binding pattern receiving the implicit any type",
  &["primary: identifier/pattern with implicit any"],
  &[],
);

/// TS7008: Member `'{0}'` implicitly has an `'{1}'` type.
///
/// Emitted under `--noImplicitAny` for unannotated class fields (including
/// private `#prop`) that cannot be inferred. Ambient / `declare class` fields
/// are exempt (tsc does not emit TS7008 there). Distinct from [`IMPLICIT_ANY`]
/// (TC3000), which covers parameters / bindings that lack a stable tsc code in
/// our surface yet.
///
/// - Primary span: the member name (`#prop` / `prop`).
/// - Labels: primary only.
/// - Notes: none.
pub const MEMBER_IMPLICIT_ANY: Code = Code::new(
  "TS7008",
  "member implicitly has an any type",
  "unannotated class member receiving the implicit any type",
  &["primary: class member name"],
  &[],
);

/// TS7022: `'{0}'` implicitly has type `'any'` because it does not have a type
/// annotation and is referenced directly or indirectly in its own initializer.
///
/// Emitted under `--noImplicitAny` when computing a variable/field type hits a
/// circularity (self-referential or mutually recursive initializers), including
/// computed property names like `["#bar"] = this["#bar"]`. Prefer this over
/// [`MEMBER_IMPLICIT_ANY`] (TS7008) whenever circularity is the reason inference
/// collapsed.
///
/// - Primary span: the binding / member name (`#foo`, `["#bar"]`, …).
/// - Labels: primary only.
/// - Notes: none.
pub const CIRCULAR_INITIALIZER_IMPLICIT_ANY: Code = Code::new(
  "TS7022",
  "implicit any due to circular initializer",
  "unannotated binding/member referenced in its own initializer",
  &["primary: binding or member name"],
  &[],
);

/// TC3001: JSX syntax is present but the compiler is not configured to allow it.
///
/// - Primary span: the JSX element expression.
/// - Labels: primary only.
/// - Notes: none.
pub const JSX_DISABLED: Code = Code::new(
  "TC3001",
  "jsx is disabled",
  "JSX element expression",
  &["primary: JSX element expression"],
  &[],
);

/// TC3002: JSX intrinsic element name is not present in `JSX.IntrinsicElements`.
///
/// - Primary span: the intrinsic JSX tag name in the opening element.
/// - Labels: primary only.
/// - Notes: none.
pub const JSX_UNKNOWN_INTRINSIC_ELEMENT: Code = Code::new(
  "TC3002",
  "unknown intrinsic JSX element",
  "JSX opening tag name",
  &["primary: JSX element tag name"],
  &[],
);

/// TC3003: JSX is enabled but required `JSX.*` namespace typings cannot be
/// resolved.
///
/// - Primary span: the JSX element span that required missing typings.
/// - Labels: primary only.
/// - Notes: none.
pub const JSX_NAMESPACE_MISSING: Code = Code::new(
  "TC3003",
  "missing JSX namespace typings",
  "JSX element span when JSX namespace types cannot be resolved",
  &["primary: JSX element span"],
  &[],
);

/// TC3004: Variance annotation on a type parameter does not match its usage
/// within the declaring type.
///
/// - Primary span: the type parameter declaration carrying the variance
///   annotation.
/// - Labels: primary only.
/// - Notes: none.
pub const INVALID_VARIANCE_ANNOTATION: Code = Code::new(
  "TC3004",
  "invalid variance annotation",
  "type parameter declaration with a variance annotation",
  &["primary: type parameter declaration"],
  &[],
);

/// HOST0001: Host environment failed to provide required input.
///
/// - Primary span: zero-length placeholder when no source span is available.
/// - Labels: primary only.
/// - Notes: may include an additional note when no span is known.
pub const HOST_ERROR: Code = Code::new(
  "HOST0001",
  "host error",
  "placeholder span when host errors are not tied to a file",
  &["primary: placeholder span"],
  &[],
);

/// ICE0001: Unexpected internal compiler error surfaced from a panic.
///
/// - Primary span: placeholder or the file referenced in [`IceContext`].
/// - Labels: primary only.
/// - Notes: includes a help note asking users to file an issue.
pub const INTERNAL_COMPILER_ERROR: Code = Code::new(
  "ICE0001",
  "internal compiler error",
  "placeholder or context-derived span when an ICE occurs",
  &["primary: placeholder span"],
  &["internal compiler error: this is a bug in the tool; please file an issue with a reproduction"],
);

/// ICE0002: Type checker expected a body but could not find one.
///
/// - Primary span: zero-length placeholder because no body span exists.
/// - Labels: primary only.
/// - Notes: none.
pub const MISSING_BODY: Code = Code::new(
  "ICE0002",
  "missing body",
  "placeholder span when a body entry is missing",
  &["primary: placeholder span"],
  &[],
);

/// TC4000: A type-system engine budget was exceeded (relation steps,
/// evaluation steps, or instantiation depth/size).
///
/// - Primary span: the expression/decl that triggered the bounded work, or a
///   placeholder when the budget trip is observed at body granularity.
/// - Labels: primary only.
/// - Notes: explain that checking was cut short to protect resources.
pub const ENGINE_BUDGET_EXCEEDED: Code = Code::new(
  "TC4000",
  "engine budget exceeded",
  "expression or declaration that triggered unbounded type-system work",
  &["primary: triggering construct, or placeholder at body scope"],
  &["type checking hit an internal work budget; the program may be too complex or pathological for the current limits"],
);

/// CANCEL0001: Type checking was cancelled by the host.
///
/// - Primary span: zero-length placeholder span.
/// - Labels: primary only.
/// - Notes: explains that the operation was cancelled by the host.
pub const CANCELLED: Code = Code::new(
  "CANCEL0001",
  "operation cancelled",
  "placeholder span when cancellation is requested",
  &["primary: placeholder span"],
  &["operation was cancelled by the host"],
);

/// OOM0001: Checker ran out of memory while processing a program.
///
/// - Primary span: zero-length placeholder span.
/// - Labels: primary only.
/// - Notes: informs the user the checker exhausted memory.
pub const OUT_OF_MEMORY: Code = Code::new(
  "OOM0001",
  "out of memory",
  "placeholder span when the checker exhausts memory",
  &["primary: placeholder span"],
  &["the checker ran out of memory while processing this program"],
);
