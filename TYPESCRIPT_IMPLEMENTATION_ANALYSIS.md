# TypeScript Parsing Support - Comprehensive Analysis & Implementation Plan

**Date:** 2025-11-09
**Branch:** `claude/add-typescript-parsing-011CUy6xGrXbPREwcB728pDY`
**Status:** Planning Phase - NO CHANGES MADE YET

---

## Executive Summary

This document provides a thorough analysis of adding complete TypeScript parsing support to the ecma-rs project. The goal is to **parse and erase TypeScript syntax** during minification, enabling the minifier to process TypeScript source files directly.

**Key Insight:** The project already has a solid foundation with:
- Well-architected recursive descent parser
- Arena-allocated AST with visitor pattern
- SIMD-accelerated lexer
- Comprehensive JavaScript ES2023+ support including JSX

**Challenge:** TypeScript adds ~50+ new syntax constructs and significant parsing complexity, particularly around:
- Type annotations in expressions
- Generic syntax disambiguation (especially with JSX)
- Namespace and module declarations
- Decorators
- Enum declarations
- Interface and type alias declarations

---

## Table of Contents

1. [Current State Analysis](#current-state-analysis)
2. [TypeScript Feature Requirements](#typescript-feature-requirements)
3. [Implementation Strategy](#implementation-strategy)
4. [Detailed Component Breakdown](#detailed-component-breakdown)
5. [Parsing Challenges & Solutions](#parsing-challenges--solutions)
6. [Testing Strategy](#testing-strategy)
7. [Implementation Phases](#implementation-phases)

---

## Current State Analysis

### Existing Architecture

#### **Parser Structure** (`parse-js/`)
- **Hand-written recursive descent parser** (NOT generated)
- **Two-phase**: Lexer → Parser
- **Checkpoint-based backtracking** for lookahead
- **Arena allocation** for AST nodes (`&'bump mut Node<S>`)
- **Visitor pattern** via `#[derive(Drive, DriveMut)]`
- **Error recovery** using `Invalid` token type

#### **Current JavaScript Support**
✅ ES2023+ complete support:
- Classes, async/await, generators
- Destructuring, spread operators
- Template literals
- Optional chaining (`?.`) and nullish coalescing (`??`)
- JSX syntax
- BigInt, dynamic imports
- Private class members (`#field`)

#### **Existing TypeScript-Related Tokens**
Currently in `token.rs`:
- `KeywordAs` (line 76) - Used for imports and type assertions
- `KeywordEnum` (line 91) - Reserved but not parsed
- `Colon` - Already exists for ternary operator

**MISSING TypeScript Tokens:**
- `interface`, `type`, `namespace`, `module`
- `readonly`, `abstract`, `public`, `private`, `protected`
- `declare`, `implements`
- `is` (type guard), `infer`, `keyof`, `satisfies`
- `asserts`, `unique`, `never`, `unknown`, `any`, `boolean`, `number`, `string`, `symbol`, `bigint`, `object`
- `@` (decorator prefix - currently exists as `AtToken` but not used)

#### **AST Structure**
- **61 expression variants** in `Expr` enum
- **18 statement types**
- **Node wrapper**: `Node<S>` containing `{ loc: Loc, stx: Box<S>, assoc: NodeAssocData }`
- **JSX support**: Already has JSX-specific expression types

---

## TypeScript Feature Requirements

Based on analysis of TypeScript compiler source and real-world usage, here's what needs to be supported:

### 1. **Type Annotations** (Core Feature)

TypeScript's most fundamental feature - annotating values with types.

#### Function/Method Parameters
```typescript
function greet(name: string, age: number): void {}
method(x: number, y?: string): boolean {}
```

#### Variable Declarations
```typescript
let x: number = 5;
const arr: Array<string> = [];
const obj: { name: string; age: number } = { name: "Alice", age: 30 };
```

#### Class Members
```typescript
class Person {
  name: string;
  age: number = 0;
  readonly id: string;
  private secret?: string;
}
```

#### Arrow Functions
```typescript
const add = (a: number, b: number): number => a + b;
```

**Parser Requirements:**
- Parse `:` followed by type expression after identifiers
- Support optional `?` modifier before `:`
- Handle return type annotations after `)` in functions
- Parse type expressions (see Type Expressions below)

---

### 2. **Type Expressions** (Type Syntax)

Types themselves are a mini-language within TypeScript:

#### Primitive Types
```typescript
string | number | boolean | null | undefined | void | any | never | unknown | bigint | symbol
```

#### Object Types
```typescript
{ name: string; age: number }
{ readonly x: number; optional?: string }
{ [key: string]: any } // Index signature
```

#### Array & Tuple Types
```typescript
string[]
Array<number>
[string, number, boolean]
[string, ...number[]] // Rest element in tuple
```

#### Function Types
```typescript
(x: number, y: string) => boolean
new (x: string) => Person // Constructor type
```

#### Union & Intersection Types
```typescript
string | number | boolean
{ x: number } & { y: string }
```

#### Generic Types
```typescript
Array<T>
Map<K, V>
Promise<Result<T, E>>
```

#### Utility Types
```typescript
keyof T
typeof x
T[K] // Indexed access
T extends U ? X : Y // Conditional type
{ [K in keyof T]: T[K] } // Mapped type
infer R // Type inference
```

#### Type Guards
```typescript
x is string
asserts x is number
```

**Parser Requirements:**
- New AST node types for all type constructs
- Separate type expression parser (parallel to value expressions)
- Handle operator precedence in types (`&` binds tighter than `|`)
- Parse generics with proper bracket matching

---

### 3. **Generic Parameters** (Type Parameters)

#### Function Generics
```typescript
function identity<T>(x: T): T { return x; }
function map<T, U>(arr: T[], fn: (x: T) => U): U[] {}
```

#### Class Generics
```typescript
class Box<T> {
  value: T;
  constructor(value: T) {}
}
```

#### Generic Constraints
```typescript
function getProperty<T, K extends keyof T>(obj: T, key: K): T[K] {}
```

#### Default Type Parameters
```typescript
class Container<T = string> {}
```

**Parser Requirements:**
- Parse `<...>` after function/class/interface names
- Handle `extends` keyword in type parameter constraints
- Disambiguate `<` from comparison operator (challenging!)
- Handle default type parameters with `=`

---

### 4. **Interfaces**

```typescript
interface Person {
  name: string;
  age: number;
  greet(): void;
}

interface Employee extends Person, Worker {
  employeeId: string;
}

// Generic interface
interface Collection<T> {
  add(item: T): void;
  get(index: number): T;
}
```

**Parser Requirements:**
- New `InterfaceDecl` statement type
- Parse interface body (similar to object type)
- Handle `extends` clause with multiple types
- Support call signatures, index signatures, method signatures

---

### 5. **Type Aliases**

```typescript
type Point = { x: number; y: number };
type Callback = (error: Error | null, data: any) => void;
type StringOrNumber = string | number;
type Nullable<T> = T | null;
```

**Parser Requirements:**
- New `TypeAliasDecl` statement type
- Parse `type Name<Params> = TypeExpr`

---

### 6. **Enums**

```typescript
enum Color {
  Red,
  Green,
  Blue
}

enum Direction {
  Up = 1,
  Down = 2,
  Left = "LEFT",
  Right = "RIGHT"
}

const enum Status { // Const enums are fully inlined
  Active,
  Inactive
}
```

**Parser Requirements:**
- New `EnumDecl` statement type
- Parse enum members with optional initializers
- Handle `const enum` modifier
- Members can have string or number literals

---

### 7. **Namespaces & Modules**

```typescript
namespace Utils {
  export function helper() {}
  export class Tool {}
}

module Legacy {
  export var x = 1;
}

// Nested namespaces
namespace App {
  export namespace Models {
    export class User {}
  }
}
```

**Parser Requirements:**
- New `NamespaceDecl` statement type
- Parse nested block with exports
- Handle both `namespace` and `module` keywords (synonyms)
- Support ambient declarations (`declare namespace`)

---

### 8. **Type Assertions & Casts**

```typescript
// Angle-bracket syntax (conflicts with JSX!)
let x = <string>someValue;

// As syntax (JSX-safe)
let y = someValue as string;

// Const assertions
let z = { x: 1 } as const;

// Non-null assertion
let elem = document.getElementById("id")!;

// Satisfies operator (TypeScript 4.9+)
const config = { x: 1 } satisfies Config;
```

**Parser Requirements:**
- Parse `as` keyword followed by type
- Parse `!` postfix operator (non-null assertion)
- Parse `satisfies` keyword
- Handle `<Type>expr` syntax (only when not in JSX mode)

---

### 9. **Decorators**

```typescript
@sealed
class BugReport {
  @property
  title: string;

  @validate
  @required
  submit(@required data: string) {}
}
```

**Parser Requirements:**
- Parse `@` followed by identifier or call expression
- Attach decorators to classes, methods, properties, parameters
- Support decorator factories (function calls)
- Multiple decorators on same target

---

### 10. **Class Modifiers**

```typescript
class Animal {
  public name: string; // Default
  private age: number;
  protected species: string;
  readonly id: string;
  static count: number = 0;
  abstract makeSound(): void; // In abstract class
}

abstract class Shape {
  abstract area(): number;
}
```

**Parser Requirements:**
- Parse access modifiers: `public`, `private`, `protected`
- Handle `readonly` modifier
- Support `abstract` keyword for classes and members
- Allow parameter properties: `constructor(public name: string) {}`

---

### 11. **Ambient Declarations**

```typescript
declare var jQuery: JQueryStatic;
declare function require(module: string): any;
declare class Buffer {}
declare namespace NodeJS {
  interface Global {}
}
declare module "module-name" {
  export function fn(): void;
}
```

**Parser Requirements:**
- Parse `declare` keyword before declarations
- Support ambient modules (`declare module "name"`)
- No implementation bodies required
- Used in `.d.ts` declaration files

---

### 12. **Import/Export Type Syntax**

```typescript
// Import types only (erased at runtime)
import type { Person } from "./types";
import { type User, createUser } from "./api";

// Export types
export type { Person };
export { type User, createUser };
```

**Parser Requirements:**
- Parse `type` keyword in import/export clauses
- Track which imports are type-only for erasure

---

### 13. **JSX with Generics** (Disambiguation Challenge!)

```typescript
// This is a generic call, not JSX!
const x = <T,>(props: Props<T>) => {};

// This is JSX!
const y = <Component />;

// Generic JSX component
<List<string> items={["a", "b"]} />
```

**Parser Requirements:**
- Disambiguate `<` as generic vs. JSX opening
- Look ahead for `,` or `extends` to identify generics
- Handle generic parameters in JSX component references

---

### 14. **Index Signatures & Mapped Types**

```typescript
interface StringMap {
  [key: string]: string;
}

type Partial<T> = {
  [P in keyof T]?: T[P];
};

type Readonly<T> = {
  readonly [P in keyof T]: T[P];
};
```

**Parser Requirements:**
- Parse index signatures in interfaces/types
- Handle `in` keyword for mapped types
- Support modifiers (`readonly`, `?`) in mapped types

---

### 15. **Conditional Types**

```typescript
type IsString<T> = T extends string ? true : false;
type Unwrap<T> = T extends Promise<infer U> ? U : T;
```

**Parser Requirements:**
- Parse ternary-like type expressions
- Handle `infer` keyword for type inference
- Support nested conditional types

---

## Implementation Strategy

### **Core Principle: Parse and Erase**

The goal is NOT to type-check TypeScript, but to:
1. **Parse** TypeScript syntax without errors
2. **Erase** type information during minification
3. **Preserve** runtime JavaScript semantics

This is similar to how Babel's `@babel/preset-typescript` works.

### **High-Level Approach**

1. **Extend Lexer** with new TypeScript keywords
2. **Add Type Expression Parser** (parallel to value expression parser)
3. **Extend AST** with TypeScript-specific node types
4. **Modify Existing Parsers** to handle type annotations
5. **Update Minifier** to skip type nodes during serialization
6. **Add Tests** for all TypeScript features

---

## Detailed Component Breakdown

### **Phase 1: Lexer Extensions** (`parse-js/src/lex/mod.rs`)

#### New Token Types to Add to `TT` enum:

```rust
// TypeScript type keywords
KeywordAbstract,
KeywordAny,
KeywordAsserts,
KeywordBigIntType,  // 'bigint' as type, distinct from runtime
KeywordBooleanType, // 'boolean' as type
KeywordDeclare,
KeywordImplements,
KeywordInfer,
KeywordInterface,
KeywordIs,
KeywordKeyof,
KeywordModule,
KeywordNamespace,
KeywordNever,
KeywordNumber,      // 'number' type
KeywordObject,      // 'object' type
KeywordOverride,
KeywordPrivate,
KeywordProtected,
KeywordPublic,
KeywordReadonly,
KeywordSatisfies,
KeywordString,      // 'string' type
KeywordSymbol,      // 'symbol' type
KeywordType,
KeywordUndefinedType, // 'undefined' as type
KeywordUnique,
KeywordUnknown,

// Operators
At,                 // @ for decorators (might already exist as AtToken)
```

#### Updates to KEYWORDS_MAPPING:

```rust
map.insert(TT::KeywordAbstract, b"abstract");
map.insert(TT::KeywordAny, b"any");
// ... etc for all new keywords
```

#### Contextual Keywords

Some keywords are only keywords in specific contexts:
- `type`, `interface`, `namespace`, `module`, `declare` - Top-level or after `export`
- `abstract`, `readonly`, `public`, etc. - Class members
- `is`, `asserts`, `infer`, `keyof` - Type expressions

**Strategy:** Lex them as keywords always, parser decides context validity.

---

### **Phase 2: Type Expression AST** (`parse-js/src/ast/type_expr.rs` - NEW FILE)

Create comprehensive type expression AST:

```rust
use super::node::Node;
use serde::Serialize;
use derive_visitor::{Drive, DriveMut};

#[derive(Debug, Drive, DriveMut, Serialize)]
#[serde(tag = "$t")]
pub enum TypeExpr {
  // Primitive types
  Any(Node<AnyType>),
  Unknown(Node<UnknownType>),
  Never(Node<NeverType>),
  Void(Node<VoidType>),
  String(Node<StringType>),
  Number(Node<NumberType>),
  Boolean(Node<BooleanType>),
  BigInt(Node<BigIntType>),
  Symbol(Node<SymbolType>),
  Object(Node<ObjectType>),
  Null(Node<NullType>),
  Undefined(Node<UndefinedType>),

  // Reference types
  TypeReference(Node<TypeReference>),      // Foo, Foo<T>

  // Literal types
  LiteralType(Node<LiteralType>),          // "foo", 42, true

  // Complex types
  ArrayType(Node<ArrayType>),              // T[]
  TupleType(Node<TupleType>),              // [T, U, ...V[]]
  UnionType(Node<UnionType>),              // T | U
  IntersectionType(Node<IntersectionType>), // T & U
  FunctionType(Node<FunctionType>),        // (x: T) => U
  ConstructorType(Node<ConstructorType>),  // new (x: T) => U
  ObjectTypeExpr(Node<ObjectTypeExpr>),    // { x: T; y: U }
  ParenthesizedType(Node<ParenthesizedType>), // (T)

  // Type operators
  TypeQuery(Node<TypeQuery>),              // typeof x
  KeyOfType(Node<KeyOfType>),              // keyof T
  IndexedAccessType(Node<IndexedAccessType>), // T[K]
  ConditionalType(Node<ConditionalType>),  // T extends U ? X : Y
  InferType(Node<InferType>),              // infer R
  MappedType(Node<MappedType>),            // { [K in T]: U }

  // Type predicates
  TypePredicate(Node<TypePredicate>),      // x is T
  AssertsPredicate(Node<AssertsPredicate>), // asserts x is T

  // Template literal types
  TemplateLiteralType(Node<TemplateLiteralType>), // `foo${T}bar`
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TypeReference {
  pub name: String,  // Could be qualified: A.B.C
  pub type_arguments: Option<Vec<Node<TypeExpr>>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ArrayType {
  pub element_type: Node<TypeExpr>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TupleType {
  pub elements: Vec<Node<TupleElement>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TupleElement {
  pub name: Option<String>,  // Named tuple elements
  pub optional: bool,
  pub rest: bool,
  pub type_expr: Node<TypeExpr>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct UnionType {
  pub types: Vec<Node<TypeExpr>>,  // At least 2
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct IntersectionType {
  pub types: Vec<Node<TypeExpr>>,  // At least 2
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct FunctionType {
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<FunctionTypeParam>>,
  pub return_type: Node<TypeExpr>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ObjectTypeExpr {
  pub members: Vec<Node<TypeMember>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum TypeMember {
  Property(PropertySignature),
  Method(MethodSignature),
  Constructor(ConstructSignature),
  CallSignature(CallSignature),
  IndexSignature(IndexSignature),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct PropertySignature {
  pub readonly: bool,
  pub optional: bool,
  pub name: String,  // or computed
  pub type_annotation: Option<Node<TypeExpr>>,
}

// ... and many more type-related structs
```

---

### **Phase 3: Type Parser** (`parse-js/src/parse/type_expr.rs` - NEW FILE)

Implement type expression parsing:

```rust
impl<'a> Parser<'a> {
  /// Main entry point for parsing type expressions
  pub fn type_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.type_union_or_intersection(ctx)
  }

  /// Parse union/intersection types (lowest precedence)
  /// T | U | V
  /// T & U & V
  fn type_union_or_intersection(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let first = self.type_conditional(ctx)?;

    // Check for | or &
    let op = self.peek().typ;
    if op != TT::Bar && op != TT::Ampersand {
      return Ok(first);
    }

    // Collect all union or intersection members
    let mut types = vec![first];
    while self.consume_if(op).is_match() {
      types.push(self.type_conditional(ctx)?);
    }

    self.with_loc(|_| {
      Ok(if op == TT::Bar {
        TypeExpr::UnionType(UnionType { types })
      } else {
        TypeExpr::IntersectionType(IntersectionType { types })
      })
    })
  }

  /// Parse conditional types
  /// T extends U ? X : Y
  fn type_conditional(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let check_type = self.type_array_or_postfix(ctx)?;

    if !self.consume_if(TT::KeywordExtends).is_match() {
      return Ok(check_type);
    }

    let extends_type = self.type_array_or_postfix(ctx)?;
    self.require(TT::Question)?;
    let true_type = self.type_expr(ctx)?;
    self.require(TT::Colon)?;
    let false_type = self.type_expr(ctx)?;

    self.with_loc(|_| {
      Ok(TypeExpr::ConditionalType(ConditionalType {
        check_type,
        extends_type,
        true_type,
        false_type,
      }))
    })
  }

  /// Parse array types and postfix operators
  /// T[]
  /// T[K]
  fn type_array_or_postfix(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let mut base = self.type_primary(ctx)?;

    loop {
      match self.peek().typ {
        TT::BracketOpen => {
          self.consume();
          if self.consume_if(TT::BracketClose).is_match() {
            // Array type: T[]
            base = self.with_loc(|_| {
              Ok(TypeExpr::ArrayType(ArrayType { element_type: base }))
            })?;
          } else {
            // Indexed access: T[K]
            let index = self.type_expr(ctx)?;
            self.require(TT::BracketClose)?;
            base = self.with_loc(|_| {
              Ok(TypeExpr::IndexedAccessType(IndexedAccessType {
                object_type: base,
                index_type: index,
              }))
            })?;
          }
        }
        _ => break,
      }
    }

    Ok(base)
  }

  /// Parse primary type expressions
  fn type_primary(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let t = self.peek();

    match t.typ {
      // Keyword types
      TT::KeywordAny => { self.consume(); self.with_loc(|_| Ok(TypeExpr::Any)) }
      TT::KeywordUnknown => { self.consume(); self.with_loc(|_| Ok(TypeExpr::Unknown)) }
      TT::KeywordString => { self.consume(); self.with_loc(|_| Ok(TypeExpr::String)) }
      // ... etc for all keyword types

      // Type reference (identifier, possibly with generics)
      TT::Identifier => self.type_reference(ctx),

      // Object type literal
      TT::BraceOpen => self.object_type(ctx),

      // Tuple type
      TT::BracketOpen => self.tuple_type(ctx),

      // Parenthesized type or function type
      TT::ParenthesisOpen => self.paren_or_function_type(ctx),

      // typeof type query
      TT::KeywordTypeof => self.type_query(ctx),

      // keyof type operator
      TT::KeywordKeyof => self.keyof_type(ctx),

      // Literal types
      TT::LiteralString | TT::LiteralNumber | TT::LiteralTrue | TT::LiteralFalse => {
        self.literal_type(ctx)
      }

      _ => Err(t.error(SyntaxErrorType::ExpectedSyntax("type expression"))),
    }
  }

  /// Parse type reference with optional generic arguments
  /// Foo
  /// Foo<T, U>
  fn type_reference(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      let name = p.consume_as_string();

      // Check for type arguments
      let type_arguments = if p.is_start_of_type_arguments() {
        Some(p.type_arguments(ctx)?)
      } else {
        None
      };

      Ok(TypeExpr::TypeReference(TypeReference {
        name,
        type_arguments,
      }))
    })
  }

  /// Lookahead to check if we're at the start of type arguments
  /// This is tricky! Need to disambiguate < from comparison
  fn is_start_of_type_arguments(&mut self) -> bool {
    if self.peek().typ != TT::ChevronLeft {
      return false;
    }

    // Need sophisticated lookahead to disambiguate:
    // Foo<T>      - type arguments
    // foo < bar   - comparison
    //
    // Heuristics:
    // - After <, we expect an identifier or keyword type
    // - Look for: <T>, <T,>, <T extends>, etc.

    let checkpoint = self.checkpoint();
    self.consume(); // <

    let t = self.peek();
    let looks_like_type = matches!(
      t.typ,
      TT::Identifier | TT::KeywordAny | TT::KeywordString |
      TT::KeywordNumber | TT::BracketOpen | TT::BraceOpen
    );

    self.restore_checkpoint(checkpoint);
    looks_like_type
  }
}
```

**Key Challenges in Type Parsing:**

1. **Generic Disambiguation**: Distinguishing `<T>` (generic) from `<` (comparison)
2. **Operator Precedence**: `&` binds tighter than `|`
3. **Type vs. Value Context**: Some tokens mean different things in type vs. value context
4. **Ambiguous Constructs**: `(x) => y` could be arrow function OR function type

---

### **Phase 4: Extend Existing Parsers**

#### **Function Parameters** (`parse-js/src/parse/func.rs`)

```rust
pub struct FuncParam {
  pub decorators: Vec<Node<Decorator>>,  // NEW
  pub accessibility: Option<Accessibility>, // NEW: public/private/protected
  pub readonly: bool,  // NEW
  pub pattern: Node<Pat>,
  pub optional: bool,  // NEW: x?: Type
  pub type_annotation: Option<Node<TypeExpr>>,  // NEW
  pub initializer: Option<Node<Expr>>,
}

impl<'a> Parser<'a> {
  fn func_param(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<FuncParam>> {
    self.with_loc(|p| {
      // Parse decorators first
      let decorators = p.decorators()?;

      // Parse accessibility
      let accessibility = p.parse_accessibility()?;

      // Parse readonly
      let readonly = p.consume_if(TT::KeywordReadonly).is_match();

      // Parse pattern
      let pattern = p.pat(ctx)?;

      // Parse optional marker
      let optional = p.consume_if(TT::Question).is_match();

      // Parse type annotation
      let type_annotation = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr(ctx)?)
      } else {
        None
      };

      // Parse initializer
      let initializer = if p.consume_if(TT::Equals).is_match() {
        Some(p.expr(ctx, [TT::Comma, TT::ParenthesisClose])?)
      } else {
        None
      };

      Ok(FuncParam {
        decorators,
        accessibility,
        readonly,
        pattern,
        optional,
        type_annotation,
        initializer,
      })
    })
  }

  fn parse_accessibility(&mut self) -> SyntaxResult<Option<Accessibility>> {
    let t = self.peek().typ;
    Ok(match t {
      TT::KeywordPublic => { self.consume(); Some(Accessibility::Public) }
      TT::KeywordPrivate => { self.consume(); Some(Accessibility::Private) }
      TT::KeywordProtected => { self.consume(); Some(Accessibility::Protected) }
      _ => None,
    })
  }
}
```

#### **Variable Declarations** (`parse-js/src/parse/stmt/decl.rs`)

```rust
pub struct VarDeclarator {
  pub pattern: Node<PatDecl>,
  pub type_annotation: Option<Node<TypeExpr>>,  // NEW
  pub initializer: Option<Node<Expr>>,
}

impl<'a> Parser<'a> {
  fn var_declarator(&mut self, ctx: ParseCtx) -> SyntaxResult<VarDeclarator> {
    let pattern = self.pat_decl(ctx)?;

    // Parse optional type annotation
    let type_annotation = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr(ctx)?)
    } else {
      None
    };

    let initializer = self.consume_if(TT::Equals)
      .and_then(|| self.expr(ctx, [TT::Semicolon, TT::Comma]))?;

    Ok(VarDeclarator {
      pattern,
      type_annotation,
      initializer,
    })
  }
}
```

#### **Class Members** (`parse-js/src/parse/class_or_object.rs`)

```rust
pub struct ClassMember {
  pub decorators: Vec<Node<Decorator>>,  // NEW
  pub accessibility: Option<Accessibility>,  // NEW
  pub static_: bool,
  pub readonly: bool,  // NEW
  pub optional: bool,  // NEW
  pub abstract_: bool,  // NEW
  pub override_: bool,  // NEW
  pub key: ClassOrObjKey,
  pub type_annotation: Option<Node<TypeExpr>>,  // NEW (for properties)
  pub val: ClassOrObjVal,
}
```

---

### **Phase 5: New Statement Types**

#### **Interface Declaration** (`parse-js/src/ast/stmt/ts_decl.rs` - NEW FILE)

```rust
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct InterfaceDecl {
  pub export: bool,
  pub name: String,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub extends: Option<Vec<Node<TypeExpr>>>,
  pub members: Vec<Node<TypeMember>>,
}

impl<'a> Parser<'a> {
  pub fn interface_decl(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<InterfaceDecl>> {
    self.with_loc(|p| {
      let export = false; // Caller handles export
      p.require(TT::KeywordInterface)?;
      let name = p.require_identifier()?;

      // Type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      // Extends clause
      let extends = if p.consume_if(TT::KeywordExtends).is_match() {
        let mut types = vec![p.type_reference(ctx)?];
        while p.consume_if(TT::Comma).is_match() {
          types.push(p.type_reference(ctx)?);
        }
        Some(types)
      } else {
        None
      };

      // Body
      p.require(TT::BraceOpen)?;
      let members = p.type_members(ctx)?;
      p.require(TT::BraceClose)?;

      Ok(InterfaceDecl {
        export,
        name,
        type_parameters,
        extends,
        members,
      })
    })
  }
}
```

#### **Type Alias Declaration**

```rust
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TypeAliasDecl {
  pub export: bool,
  pub name: String,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub type_expr: Node<TypeExpr>,
}
```

#### **Enum Declaration**

```rust
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct EnumDecl {
  pub export: bool,
  pub const_: bool,  // const enum
  pub name: String,
  pub members: Vec<Node<EnumMember>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct EnumMember {
  pub name: String,
  pub initializer: Option<Node<Expr>>,  // Can be number or string literal
}
```

#### **Namespace Declaration**

```rust
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct NamespaceDecl {
  pub export: bool,
  pub declare: bool,  // ambient declaration
  pub name: String,
  pub body: Vec<Node<Stmt>>,  // Can contain more namespaces
}
```

---

### **Phase 6: Type Erasure in Minifier**

During serialization, skip all TypeScript-only constructs:

```rust
// In minify-js/src/serialize.rs or similar

impl Serialize for TypeScript {
  fn serialize(&self, output: &mut Vec<u8>) {
    // Type annotations: skip entirely
    // Example: `x: number` becomes `x`

    // Interfaces: skip entirely (don't emit)
    // Type aliases: skip entirely
    // Enums: emit as objects/constants (or skip if const enum)
    // Namespaces: emit as IIFE or objects
    // Decorators: skip (unless we support decorator metadata)
  }
}
```

**Enum Handling:**

Regular enums must be emitted as JavaScript:
```typescript
enum Color { Red, Green, Blue }
// Becomes:
var Color;
(function (Color) {
  Color[Color["Red"] = 0] = "Red";
  Color[Color["Green"] = 1] = "Green";
  Color[Color["Blue"] = 2] = "Blue";
})(Color || (Color = {}));
```

Const enums can be inlined or removed entirely.

---

## Parsing Challenges & Solutions

### Challenge 1: Generic Syntax Disambiguation

**Problem:** `<` can mean:
- Less-than operator: `a < b`
- Generic parameter: `Array<T>`
- JSX opening: `<Component>`

**Solution:** Sophisticated lookahead with heuristics:

```rust
fn is_start_of_type_arguments(&mut self) -> bool {
  if self.peek().typ != TT::ChevronLeft {
    return false;
  }

  // Save position
  let checkpoint = self.checkpoint();
  self.consume(); // <

  // Look for type-like patterns:
  // - Identifier followed by: >, ,, extends, =, |, &, [, (
  // - Primitive type keyword
  // - Opening bracket/brace (tuple/object type)

  let next = self.peek();
  let looks_like_type = match next.typ {
    TT::Identifier => {
      self.consume();
      matches!(
        self.peek().typ,
        TT::ChevronRight | TT::Comma | TT::KeywordExtends |
        TT::Equals | TT::Bar | TT::Ampersand
      )
    }
    TT::KeywordAny | TT::KeywordString | TT::KeywordNumber |
    TT::KeywordBoolean | TT::KeywordUnknown | TT::KeywordNever => true,
    TT::BracketOpen | TT::BraceOpen => true,
    _ => false,
  };

  self.restore_checkpoint(checkpoint);
  looks_like_type
}
```

### Challenge 2: JSX vs. Type Assertion

**Problem:**
```typescript
let x = <string>foo;    // Type assertion
let y = <Component />;  // JSX
```

**Solution:**
- If in `.tsx` file, prefer JSX interpretation
- Type assertions with `<` syntax should use angle bracket lookahead
- Recommend users use `as` syntax instead of `<>` in TSX files

### Challenge 3: Arrow Function vs. Function Type

**Problem:**
```typescript
(x: number) => x + 1           // Arrow function (has body)
(x: number) => number          // Function type (type annotation)
```

**Solution:**
Context-dependent parsing:
- In type annotation context (after `:`), parse as function type
- In expression context, parse as arrow function
- Arrow function must have valid expression/block after `=>`
- Function type just has another type expression after `=>`

### Challenge 4: Automatic Semicolon Insertion with Type Annotations

**Problem:**
```typescript
let x: number
[1, 2, 3].forEach(...)

// Is this:
let x: number[1, 2, 3].forEach(...)  // Indexed access type???
// Or:
let x: number;
[1, 2, 3].forEach(...)  // ASI
```

**Solution:**
- Apply ASI rules even in type annotations
- Line terminator after type annotation should trigger ASI

### Challenge 5: Optional Parameters vs. Ternary Operator

**Problem:**
```typescript
function f(x?) {}     // Optional parameter
x ? y : z            // Ternary operator
```

**Solution:**
- In parameter list context, `?` after identifier means optional
- Everywhere else, `?` is ternary operator

---

## Testing Strategy

### Unit Tests

Create comprehensive unit tests for each TypeScript feature:

```rust
#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_simple_type_annotation() {
    let src = b"let x: number = 5;";
    let ast = parse(src).unwrap();
    // Assert structure
  }

  #[test]
  fn test_generic_function() {
    let src = b"function id<T>(x: T): T { return x; }";
    let ast = parse(src).unwrap();
    // Assert structure
  }

  #[test]
  fn test_interface() {
    let src = b"interface Person { name: string; age: number; }";
    let ast = parse(src).unwrap();
    // Assert structure
  }

  // ... hundreds more tests
}
```

### Integration Tests

Test real-world TypeScript files:

```rust
#[test]
fn test_parse_typescript_stdlib() {
  let src = std::fs::read("/tmp/typescript-ref/src/lib/lib.d.ts").unwrap();
  let ast = parse(&src).unwrap();
  // Should parse without errors
}
```

### Minification Tests

Verify type erasure:

```rust
#[test]
fn test_erase_type_annotations() {
  let src = b"let x: number = 5; function f(y: string): void {}";
  let minified = minify(src).unwrap();
  assert_eq!(minified, b"let x=5;function f(y){}");
}
```

### Test Files from TypeScript Repo

Use TypeScript's own test suite:
- `/tmp/typescript-ref/tests/cases/compiler/*.ts`
- `/tmp/typescript-ref/tests/cases/conformance/*.ts`

---

## Implementation Phases

### **Phase 0: Preparation** (Current Phase)
- ✅ Deep understanding of current codebase
- ✅ Analysis of TypeScript grammar
- ✅ Comprehensive planning
- ⏳ Review and refinement of plan

### **Phase 1: Lexer & Tokens** (Est: 2-3 hours)
- Add all TypeScript keyword tokens to `TT` enum
- Update `KEYWORDS_MAPPING`
- Update `UNRESERVED_KEYWORDS` for contextual keywords
- Test lexer with TypeScript source

### **Phase 2: Type Expression AST** (Est: 4-5 hours)
- Create `ast/type_expr.rs` with all type node structures
- Add type parameter structures
- Add type member structures (for interfaces)
- Integrate with existing AST via `#[derive(Drive, DriveMut)]`

### **Phase 3: Type Expression Parser** (Est: 6-8 hours)
- Create `parse/type_expr.rs`
- Implement type expression parsing with proper precedence
- Handle generic type arguments
- Implement lookahead disambiguation
- Test extensively

### **Phase 4: Type Annotations in Existing Constructs** (Est: 5-6 hours)
- Extend function parameter parsing
- Extend variable declaration parsing
- Extend class member parsing
- Add type annotation fields to AST nodes
- Handle optional markers (`?`)

### **Phase 5: New Declaration Types** (Est: 8-10 hours)
- Interface declarations
- Type alias declarations
- Enum declarations (with JS emission logic)
- Namespace/module declarations
- Ambient declarations (`declare`)

### **Phase 6: Advanced Features** (Est: 6-8 hours)
- Decorators
- Type assertions (`as`, `<>`, `!`)
- Import/export type syntax
- Satisfies operator
- JSX with generics disambiguation

### **Phase 7: Type Erasure** (Est: 4-5 hours)
- Update minifier serialization to skip type nodes
- Handle enum emission
- Handle namespace emission
- Test that output is valid JavaScript

### **Phase 8: Testing & Validation** (Est: 8-10 hours)
- Write comprehensive unit tests
- Test against TypeScript stdlib files
- Test against real-world TypeScript projects
- Fuzz testing with random TypeScript
- Performance benchmarking

### **Phase 9: Documentation** (Est: 2-3 hours)
- Update README with TypeScript support
- Add examples
- Document limitations (no type checking, etc.)

### **Total Estimated Time: 45-58 hours**

---

## Known Limitations

### What We WILL Support:
✅ All TypeScript syntax parsing
✅ Type erasure for minification
✅ JSX + TypeScript (`.tsx`)
✅ Decorators (parsing, not evaluation)
✅ Enum emission
✅ Namespace emission

### What We WON'T Support:
❌ Type checking (not our goal)
❌ Type inference
❌ Compiler API
❌ `.d.ts` generation
❌ Module resolution
❌ Incremental compilation
❌ TypeScript transformers

---

## References

### TypeScript Grammar
- Official TypeScript Handbook: https://www.typescriptlang.org/docs/handbook/
- TypeScript Spec: https://github.com/microsoft/TypeScript/blob/main/doc/spec-ARCHIVED.md
- TypeScript Parser Source: `/tmp/typescript-ref/src/compiler/parser.ts`
- TypeScript Scanner Source: `/tmp/typescript-ref/src/compiler/scanner.ts`

### Similar Projects
- **@babel/preset-typescript**: Babel's TypeScript support (type erasure only)
- **SWC**: Rust-based JS/TS compiler with type erasure
- **esbuild**: Go-based bundler with TS support

### Testing Resources
- TypeScript Test Cases: `/tmp/typescript-ref/tests/cases/`
- DefinitelyTyped: https://github.com/DefinitelyTyped/DefinitelyTyped

---

## Next Steps

### Immediate Actions:
1. **Review this plan** with stakeholders
2. **Clarify ambiguities** in requirements
3. **Prioritize features** if scope needs reduction
4. **Set up branch** and development environment
5. **Begin Phase 1** (Lexer extensions)

### Questions to Answer:
- Do we need full decorator support or just parsing?
- Should const enums be inlined or emit warnings?
- Do we support all TypeScript versions or target specific version?
- Should we emit source maps for TypeScript?
- Do we need special handling for `.d.ts` files?

---

## Conclusion

Adding TypeScript support to ecma-rs is a **substantial but well-defined task**. The project's existing architecture is well-suited for this extension:

- ✅ Clean parser architecture
- ✅ Extensible AST via visitor pattern
- ✅ Proven high performance
- ✅ Strong test coverage culture

The main challenges are:
1. Generic syntax disambiguation
2. Comprehensive type expression grammar
3. Maintaining performance with larger AST
4. Thorough testing against real-world TS code

With careful implementation following this plan, we can achieve the goal of **parsing and erasing TypeScript syntax** to enable direct minification of TypeScript source files.

---

**END OF ANALYSIS DOCUMENT**
