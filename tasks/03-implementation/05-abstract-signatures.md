---
task_id: "03-implementation/05-abstract-signatures"
phase: "03-implementation"
title: "Implement Abstract Construct Signatures and This Type Predicates"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/type_expr.rs" (modified)
  - "parse-js/src/parse/type_expr.rs" (modified)
  - "parse-js/tests/abstract_signatures.rs"
  - "workspace/outputs/03-implementation/05-abstract-signatures/implementation-report.md"
estimated_duration: "3-4 hours"
complexity: "medium"
priority: "low"
---

# Task: Implement Abstract Construct Signatures and This Type Predicates

## Objective

Implement support for two advanced TypeScript signature features:
1. **Abstract construct signatures**: `abstract new (...args: any[]) => any`
2. **This-parameter type predicates**: `asserts this is T`

## Context

These features are less common but necessary for complete TypeScript parsing:

### Abstract Construct Signatures
Used in type definitions for abstract class constructors:
```typescript
type AbstractConstructor<T> = abstract new (...args: any[]) => T;

function mixin<T extends AbstractConstructor<{}>>(Base: T) {
    return class extends Base {};
}
```

### This-Parameter Type Predicates
Used in method signatures for type narrowing based on `this`:
```typescript
class Animal {
    isDog(): this is Dog {
        return this instanceof Dog;
    }

    assertDog(): asserts this is Dog {
        if (!(this instanceof Dog)) throw new Error();
    }
}
```

### Current State
- Regular construct signatures likely work: `new () => T`
- Regular type predicates likely work: `x is T`
- Assertion signatures likely work: `asserts x is T`
- `abstract` modifier and `this` parameter may not be supported

### Target Features

```typescript
// 1. Abstract construct signature
abstract new (...args: any[]) => any;
type Ctor = abstract new (x: number) => MyClass;

// 2. This-parameter type predicate (is)
this is Dog;
isDog(): this is Dog;

// 3. This-parameter assertion signature (asserts)
asserts this is Dog;
assertDog(): asserts this is Dog;

// 4. Combined with abstract
abstract class Base {
    abstract isSpecific(): this is Specific;
}
```

## Instructions

### Step 1: Check Current Support

Test current parsing:
```bash
# Test regular construct signature
cargo run --example parse_type -- 'type T = new () => any'

# Test abstract (likely fails)
cargo run --example parse_type -- 'type T = abstract new () => any'

# Test this type predicate (likely fails)
cargo run --example parse_type -- 'type T = (this: MyClass) => this is SubClass'
```

### Step 2: Extend AST

**File**: `parse-js/src/ast/type_expr.rs`

#### 2.1: Add Abstract Flag

```rust
#[derive(Debug, Clone, Serialize)]
pub struct ConstructSignature {
    pub type_params: Option<Vec<TypeParam>>,
    pub params: Vec<Parameter>,
    pub return_type: Option<Node<TypeExpr>>,
    pub abstract_: bool,  // ADD: for abstract construct signatures
}
```

#### 2.2: Support `this` in Type Predicates

```rust
#[derive(Debug, Clone, Serialize)]
pub enum TypePredicate {
    /// param is Type
    Is {
        param: PredicateParam,  // CHANGE: was String
        type_: Node<TypeExpr>,
    },
    /// asserts param
    Asserts {
        param: PredicateParam,  // CHANGE: was String
    },
    /// asserts param is Type
    AssertsIs {
        param: PredicateParam,  // CHANGE: was String
        type_: Node<TypeExpr>,
    },
}

#[derive(Debug, Clone, Serialize)]
pub enum PredicateParam {
    /// Regular parameter name: "x is T"
    Identifier(String),
    /// This parameter: "this is T"
    This,
}
```

### Step 3: Implement Parser - Abstract Construct Signatures

**File**: `parse-js/src/parse/type_expr.rs`

#### 3.1: Parse Abstract Modifier

```rust
impl<'a> Parser<'a> {
    fn construct_signature(&mut self, ctx: ParseCtx) -> SyntaxResult<ConstructSignature> {
        // Check for 'abstract' keyword
        let abstract_ = if self.peek().typ == TT::KeywordAbstract {
            self.consume();
            true
        } else {
            false
        };

        self.expect(TT::KeywordNew)?;

        // Parse type parameters
        let type_params = if self.peek().typ == TT::LessThan {
            Some(self.type_parameters(ctx)?)
        } else {
            None
        };

        // Parse parameters
        self.expect(TT::ParenOpen)?;
        let params = self.parameters(ctx)?;
        self.expect(TT::ParenClose)?;

        // Parse return type
        let return_type = if self.consume_if(TT::Arrow).is_match()
            || self.consume_if(TT::Colon).is_match()
        {
            Some(self.type_expr(ctx)?)
        } else {
            None
        };

        Ok(ConstructSignature {
            type_params,
            params,
            return_type,
            abstract_,
        })
    }

    /// Parse type member - could be call, construct, property, etc.
    fn type_member(&mut self, ctx: ParseCtx) -> SyntaxResult<TypeMember> {
        // Check for abstract keyword
        if self.peek().typ == TT::KeywordAbstract
            && self.peek_nth(1).typ == TT::KeywordNew
        {
            let sig = self.construct_signature(ctx)?;
            return Ok(TypeMember::ConstructSignature(sig));
        }

        // ... existing code for other member types
        todo!()
    }
}
```

### Step 4: Implement Parser - This Type Predicates

**File**: `parse-js/src/parse/type_expr.rs`

#### 4.1: Update Type Predicate Parser

```rust
impl<'a> Parser<'a> {
    /// Parse type predicate: "x is T" or "this is T" or "asserts x" or "asserts this is T"
    fn type_predicate(&mut self, ctx: ParseCtx) -> SyntaxResult<TypePredicate> {
        // Determine if it's an assertion signature
        let is_asserts = if self.peek().typ == TT::Identifier
            && self.peek().value == "asserts"
        {
            self.consume();
            true
        } else {
            false
        };

        // Parse parameter name or 'this'
        let param = if self.peek().typ == TT::KeywordThis {
            self.consume();
            PredicateParam::This
        } else {
            let name = self.expect_identifier()?;
            PredicateParam::Identifier(name)
        };

        // Check for 'is Type' clause
        if self.peek().typ == TT::Identifier && self.peek().value == "is" {
            self.consume();  // Consume 'is'

            let type_ = self.type_expr(ctx)?;

            if is_asserts {
                Ok(TypePredicate::AssertsIs { param, type_ })
            } else {
                Ok(TypePredicate::Is { param, type_ })
            }
        } else {
            // Just 'asserts param' without 'is Type'
            if is_asserts {
                Ok(TypePredicate::Asserts { param })
            } else {
                // Not a type predicate - this shouldn't happen in type context
                Err(SyntaxError::expected("is"))
            }
        }
    }

    /// Parse function return type, which could be a type or type predicate
    fn function_return_type(&mut self, ctx: ParseCtx) -> SyntaxResult<FunctionReturnType> {
        // Check if it's a type predicate
        // Lookahead: 'is' or 'asserts'
        let is_predicate = {
            let peek1 = self.peek();
            let peek2 = self.peek_nth(1);

            // "asserts ..."
            (peek1.typ == TT::Identifier && peek1.value == "asserts")
            // "this is ..."
            || (peek1.typ == TT::KeywordThis && peek2.typ == TT::Identifier && peek2.value == "is")
            // "param is ..."
            || (peek1.typ == TT::Identifier && peek2.typ == TT::Identifier && peek2.value == "is")
        };

        if is_predicate {
            let predicate = self.type_predicate(ctx)?;
            Ok(FunctionReturnType::Predicate(predicate))
        } else {
            let type_ = self.type_expr(ctx)?;
            Ok(FunctionReturnType::Type(type_))
        }
    }
}

/// Function return type can be a regular type or a type predicate
#[derive(Debug, Clone, Serialize)]
pub enum FunctionReturnType {
    Type(Node<TypeExpr>),
    Predicate(TypePredicate),
}
```

#### 4.2: Update Function Type Parser

```rust
fn function_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start = self.lexer.loc_start();

    // Type parameters
    let type_params = if self.peek().typ == TT::LessThan {
        Some(self.type_parameters(ctx)?)
    } else {
        None
    };

    // Parameters
    self.expect(TT::ParenOpen)?;
    let params = self.parameters(ctx)?;
    self.expect(TT::ParenClose)?;

    // Arrow
    self.expect(TT::Arrow)?;

    // Return type or type predicate
    let return_type = self.function_return_type(ctx)?;

    Ok(Node::new(
        self.loc_range(start),
        TypeExpr::Function(FunctionType {
            type_params,
            params,
            return_type,
        }),
    ))
}
```

### Step 5: Update Method Signature Parser

**File**: `parse-js/src/parse/class.rs` or wherever method signatures are parsed

```rust
fn method_signature(&mut self, ctx: ParseCtx) -> SyntaxResult<MethodSignature> {
    // ... parse name, type params, params ...

    // Parse return type annotation
    if self.consume_if(TT::Colon).is_match() {
        let return_type = self.function_return_type(ctx)?;

        return Ok(MethodSignature {
            // ...
            return_type: Some(return_type),
        });
    }

    Ok(MethodSignature { /* ... */ })
}
```

### Step 6: Write Tests

**File**: `parse-js/tests/abstract_signatures.rs`

```rust
use parse_js::*;

// Abstract Construct Signatures

#[test]
fn test_abstract_construct_signature_simple() {
    let src = r#"type T = abstract new () => any;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_abstract_construct_signature_with_params() {
    let src = r#"type Ctor<T> = abstract new (x: number) => T;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_abstract_construct_signature_in_interface() {
    let src = r#"
        interface AbstractFactory {
            abstract new (): Product;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_regular_construct_signature_still_works() {
    let src = r#"type Ctor = new () => any;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

// This Type Predicates

#[test]
fn test_this_is_type_predicate() {
    let src = r#"
        class Animal {
            isDog(): this is Dog {
                return true;
            }
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_this_asserts_type_predicate() {
    let src = r#"
        class Animal {
            assertDog(): asserts this is Dog {
                if (false) throw new Error();
            }
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_this_type_predicate_in_interface() {
    let src = r#"
        interface Checkable {
            check(): this is Valid;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_this_asserts_without_type() {
    let src = r#"
        function assertThis(): asserts this {
            if (!this) throw new Error();
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_this_in_function_type() {
    let src = r#"type Fn = (this: MyClass) => this is SubClass;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_regular_type_predicate_still_works() {
    let src = r#"
        function isDog(x: Animal): x is Dog {
            return true;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

// Combined Tests

#[test]
fn test_abstract_class_with_this_predicate() {
    let src = r#"
        abstract class Base {
            abstract isSpecific(): this is Specific;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}
```

### Step 7: Run Tests

```bash
cargo test abstract_signatures
cargo test
cargo test --release conformance_runner -- --filter "abstract"
cargo test --release conformance_runner -- --filter "this"
```

### Step 8: Create Implementation Report

**File**: `workspace/outputs/03-implementation/05-abstract-signatures/implementation-report.md`

[Standard format with summary, changes, results, examples]

## Verification Commands

```bash
cargo check
cargo test abstract_signatures

# Manual tests
echo 'type T = abstract new () => any' | cargo run --example parse_type
echo 'type T = (x: any) => this is Dog' | cargo run --example parse_type
```

## Common Issues

### Issue 1: Abstract vs Identifier
**Problem**: `abstract` could be property name in some contexts

**Solution**: Context-aware parsing - `abstract new` is always abstract construct signature in type context

### Issue 2: This Parameter vs This Type
**Problem**: Distinguish `(this: T)` from `this is T`

**Solution**:
- `(this: T)` appears in parameter list
- `this is T` appears after `=>` in return type position

### Issue 3: Asserts Lookahead
**Problem**: Determining if `asserts` is keyword or identifier

**Solution**: Check if followed by identifier or `this`, then optionally `is`

```rust
if self.peek().value == "asserts" {
    let next = self.peek_nth(1).typ;
    if matches!(next, TT::Identifier | TT::KeywordThis) {
        // It's assertion signature
    } else {
        // It's identifier 'asserts'
    }
}
```

## Acceptance Criteria

- [ ] `abstract new` construct signatures parse
- [ ] `this is T` type predicates parse
- [ ] `asserts this is T` assertion signatures parse
- [ ] Works in classes, interfaces, and type literals
- [ ] All tests pass
- [ ] Conformance tests improve
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- Conformance tests: +1-3% (these are rare features)
- Zero regressions

## Resources

- TypeScript Handbook: Classes - Abstract Classes
- TypeScript Handbook: Narrowing - Using type predicates
- TypeScript 3.7 Release Notes: Assertion Signatures
- TypeScript source: `src/compiler/parser.ts` - search for "abstract" and "asserts"
