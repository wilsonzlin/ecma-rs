---
task_id: "03-implementation/07-const-type-parameters"
phase: "03-implementation"
title: "Implement const Type Parameters"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/type_expr.rs" (modified)
  - "parse-js/src/parse/type_expr.rs" (modified)
  - "parse-js/tests/const_type_parameters.rs"
  - "workspace/outputs/03-implementation/07-const-type-parameters/implementation-report.md"
estimated_duration: "2-3 hours"
complexity: "low"
priority: "medium"
---

# Task: Implement const Type Parameters

## Objective

Implement TypeScript 5.0+ `const` type parameters which allow type parameters to infer literal types by default:
- `<const T>` in function type parameters
- Enforces inference of literal types rather than widened types

## Context

TypeScript 5.0 introduced `const` type parameters to simplify working with literal types without requiring `as const` everywhere.

### Use Case

```typescript
// Before TypeScript 5.0
function makeArray<T>(arr: readonly T[]) {
    return arr;
}
const arr1 = makeArray([1, 2, 3] as const);  // Type: readonly [1, 2, 3]
const arr2 = makeArray([1, 2, 3]);           // Type: readonly number[]

// With const type parameters (TypeScript 5.0+)
function makeArray<const T>(arr: readonly T[]) {
    return arr;
}
const arr1 = makeArray([1, 2, 3]);  // Type: readonly [1, 2, 3]  (automatic!)
const arr2 = makeArray([1, 2, 3]);  // Type: readonly [1, 2, 3]
```

### Current State
Type parameters likely already parse but without `const` modifier support.

### Target Features

```typescript
// 1. Function with const type parameter
function identity<const T>(value: T): T {
    return value;
}

// 2. Multiple type parameters with const
function tuple<const T, const U>(a: T, b: U): [T, U] {
    return [a, b];
}

// 3. Mixed const and regular type parameters
function fn<const T, U>(a: T, b: U) {
    // T infers literals, U infers normally
}

// 4. In arrow functions
const fn = <const T>(x: T) => x;

// 5. With constraints
function fn<const T extends string>(x: T) {}

// 6. In classes/interfaces
class Container<const T> {
    constructor(public value: T) {}
}

interface Builder<const T> {
    build(): T;
}

// 7. In type aliases
type Fn<const T> = (x: T) => T;
```

## Instructions

### Step 1: Check Current State

```bash
# Test basic type parameter (likely works)
cargo run --example parse -- 'function f<T>(x: T) {}'

# Test const type parameter (likely fails)
cargo run --example parse -- 'function f<const T>(x: T) {}'
```

### Step 2: Extend AST

**File**: `parse-js/src/ast/type_expr.rs`

Add `is_const` flag to type parameter:

```rust
#[derive(Debug, Clone, Serialize)]
pub struct TypeParam {
    pub name: String,
    pub constraint: Option<Box<Node<TypeExpr>>>,
    pub default: Option<Box<Node<TypeExpr>>>,
    pub variance: Option<Variance>,  // 'in', 'out', 'in out'
    pub is_const: bool,  // ADD: for 'const T'
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum Variance {
    In,      // 'in T'
    Out,     // 'out T'
    InOut,   // 'in out T'
}
```

### Step 3: Implement Parser

**File**: `parse-js/src/parse/type_expr.rs`

#### 3.1: Update Type Parameter Parser

```rust
impl<'a> Parser<'a> {
    /// Parse type parameters: <T, U, V>
    fn type_parameters(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<TypeParam>> {
        self.expect(TT::LessThan)?;

        let mut params = Vec::new();

        while self.peek().typ != TT::GreaterThan {
            params.push(self.type_parameter(ctx)?);

            if !self.consume_if(TT::Comma).is_match() {
                break;
            }
        }

        self.expect(TT::GreaterThan)?;

        Ok(params)
    }

    /// Parse single type parameter: T, const T, in T, out T, etc.
    fn type_parameter(&mut self, ctx: ParseCtx) -> SyntaxResult<TypeParam> {
        // Parse modifiers: const, in, out
        let mut is_const = false;
        let mut variance = None;

        loop {
            if self.peek().typ == TT::KeywordConst {
                self.consume();
                is_const = true;
            } else if self.peek().typ == TT::Identifier {
                match self.peek().value.as_str() {
                    "in" => {
                        self.consume();
                        if self.peek().typ == TT::Identifier && self.peek().value == "out" {
                            self.consume();
                            variance = Some(Variance::InOut);
                        } else {
                            variance = Some(Variance::In);
                        }
                    }
                    "out" => {
                        self.consume();
                        variance = Some(Variance::Out);
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }

        // Parse type parameter name
        let name = self.expect_identifier()?;

        // Parse optional constraint: extends Type
        let constraint = if self.consume_if(TT::KeywordExtends).is_match() {
            Some(Box::new(self.type_expr(ctx)?))
        } else {
            None
        };

        // Parse optional default: = Type
        let default = if self.consume_if(TT::Equals).is_match() {
            Some(Box::new(self.type_expr(ctx)?))
        } else {
            None
        };

        Ok(TypeParam {
            name,
            constraint,
            default,
            variance,
            is_const,
        })
    }
}
```

#### 3.2: Handle Ambiguity with const Keyword

**Problem**: `const` can be:
- Variable declaration: `const x = 1`
- Type parameter modifier: `<const T>`
- Type assertion: `as const`

**Solution**: Context determines meaning:
- After `<` in type parameter position → modifier
- At statement start → variable declaration
- After `as` → type assertion

```rust
// In type_parameter() - we're already in type parameter context after '<'
// So 'const' is always the modifier here
if self.peek().typ == TT::KeywordConst {
    // Look ahead to confirm it's followed by identifier (type param name)
    if self.peek_nth(1).typ == TT::Identifier {
        self.consume();
        is_const = true;
    }
}
```

### Step 4: Update Function/Class/Interface Parsers

Ensure all places that parse type parameters use the updated `type_parameters()` function:

**File**: `parse-js/src/parse/stmt.rs` and others

```rust
// Function declarations
fn function_declaration(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    // ...
    let type_params = if self.peek().typ == TT::LessThan {
        Some(self.type_parameters(ctx)?)  // Already updated
    } else {
        None
    };
    // ...
}

// Class declarations
fn class_declaration(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    // ...
    let type_params = if self.peek().typ == TT::LessThan {
        Some(self.type_parameters(ctx)?)  // Already updated
    } else {
        None
    };
    // ...
}

// Type aliases
fn type_alias(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    // ...
    let type_params = if self.peek().typ == TT::LessThan {
        Some(self.type_parameters(ctx)?)  // Already updated
    } else {
        None
    };
    // ...
}
```

### Step 5: Write Tests

**File**: `parse-js/tests/const_type_parameters.rs`

```rust
use parse_js::*;

#[test]
fn test_const_type_parameter_function() {
    let src = r#"function identity<const T>(value: T): T { return value; }"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_type_parameter_arrow_function() {
    let src = r#"const fn = <const T>(x: T) => x;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_multiple_const_type_parameters() {
    let src = r#"function tuple<const T, const U>(a: T, b: U): [T, U] { return [a, b]; }"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_mixed_const_and_regular() {
    let src = r#"function fn<const T, U>(a: T, b: U) {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_with_constraint() {
    let src = r#"function fn<const T extends string>(x: T) {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_with_default() {
    let src = r#"function fn<const T = number>(x?: T) {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_in_class() {
    let src = r#"
        class Container<const T> {
            constructor(public value: T) {}
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_in_interface() {
    let src = r#"
        interface Builder<const T> {
            build(): T;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_in_type_alias() {
    let src = r#"type Fn<const T> = (x: T) => T;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_with_variance() {
    // Both const and variance modifiers
    let src = r#"type T<const in T> = { /* ... */ };"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_regular_type_parameter_still_works() {
    let src = r#"function fn<T>(x: T) {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_not_confused_with_declaration() {
    // Ensure 'const' keyword in different contexts doesn't interfere
    let src = r#"
        function fn<const T>(x: T) {
            const y = 1;  // Regular const declaration
            return x;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_const_not_confused_with_assertion() {
    let src = r#"
        function fn<const T>(x: T) {
            const arr = [1, 2, 3] as const;  // as const assertion
            return x;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}
```

### Step 6: Run Tests

```bash
cargo test const_type_parameters
cargo test
cargo test --release conformance_runner -- --filter "const"
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/07-const-type-parameters/implementation-report.md`

```markdown
# const Type Parameters Implementation Report

## Summary
Implemented TypeScript 5.0+ `const` type parameter modifier.

## Changes Made

### AST Changes
- Added `is_const: bool` field to `TypeParam` struct

### Parser Changes
- Updated `type_parameter()` to parse `const` modifier
- Handles `const` before type parameter name
- Works with constraints and defaults
- No conflicts with other uses of `const` keyword

## Test Results
- Unit tests: X/X passing
- Conformance tests: [results]

## Examples Supported

```typescript
function identity<const T>(value: T): T { return value; }
function tuple<const T, const U>(a: T, b: U): [T, U] { return [a, b]; }
class Container<const T> { /* ... */ }
```

## Known Limitations
None - full support for const type parameters.

## Performance Impact
Negligible - simple boolean flag in AST.
```

## Verification Commands

```bash
cargo check
cargo test const_type_parameters
cargo test --release conformance_runner
echo 'function f<const T>(x: T) {}' | cargo run --example parse
```

## Common Issues

### Issue 1: Ambiguity with const Keyword
**Problem**: `const` appears in multiple contexts

**Solution**: Context-sensitive parsing:
- After `<` in type parameter list → modifier
- At statement start → declaration
- After `as` → assertion

The parser is already in type parameter context when calling `type_parameter()`, so no ambiguity.

### Issue 2: Order of Modifiers
**Problem**: Can `const` appear with variance modifiers? What order?

**Solution**: According to TypeScript, allowed combinations:
- `const T` ✓
- `in const T` ✓
- `out const T` ✓
- `const in T` ✓ (either order works)

Parse flexibly - allow any order:

```rust
loop {
    if self.peek().typ == TT::KeywordConst {
        is_const = true;
        self.consume();
    } else if self.peek().value == "in" || self.peek().value == "out" {
        // parse variance
    } else {
        break;
    }
}
```

### Issue 3: Default Value with const
**Problem**: Does `const T = number` make sense?

**Solution**: Yes, it's valid. The `const` affects inference, not the default value.

```typescript
function fn<const T = number>(x?: T) {}
// T infers literal types when argument provided
// Falls back to number when no argument
```

## Acceptance Criteria

- [ ] `const` type parameters parse in all contexts (functions, classes, interfaces, type aliases)
- [ ] Works with constraints (`extends`)
- [ ] Works with defaults (`=`)
- [ ] Works with variance modifiers (`in`, `out`)
- [ ] No conflicts with other uses of `const`
- [ ] All tests pass
- [ ] Conformance tests improve
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- Conformance improvement: +2-4%
- Zero regressions

## Resources

- TypeScript 5.0 Release Notes: const Type Parameters
- TypeScript Handbook: Generics - const Type Parameters
- TypeScript source: `src/compiler/parser.ts` - `parseTypeParameter`

## Notes

The `const` type parameter modifier is a recent addition (TS 5.0, March 2023). It's syntactically simple - just a flag on the type parameter. The semantic meaning (inferring literal types) is handled by the type checker, not the parser.
