---
task_id: "03-implementation/06-satisfies-operator"
phase: "03-implementation"
title: "Implement satisfies Operator"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/expr.rs" (modified)
  - "parse-js/src/parse/expr.rs" (modified)
  - "parse-js/tests/satisfies_operator.rs"
  - "workspace/outputs/03-implementation/06-satisfies-operator/implementation-report.md"
estimated_duration: "2-3 hours"
complexity: "low"
priority: "medium"
---

# Task: Implement satisfies Operator

## Objective

Implement TypeScript's `satisfies` operator (introduced in TS 4.9) which validates that an expression satisfies a type constraint without widening the expression's type.

## Context

The `satisfies` operator is TypeScript's newest type operator (as of TS 4.9, Nov 2022). It provides type checking without type widening.

### Use Case

```typescript
// Without satisfies - type is widened
const config = {
    apiUrl: "https://api.com",  // Type: string (too wide)
    timeout: 5000,
};

// With satisfies - type is preserved while checking constraint
const config = {
    apiUrl: "https://api.com",  // Type: "https://api.com" (literal)
    timeout: 5000,
} satisfies Config;

// Now you get autocomplete AND type narrowing:
config.apiUrl.toUpperCase();  // OK - knows it's a string
const url: "https://api.com" = config.apiUrl;  // OK - knows exact value
```

### Current State
The `satisfies` operator is likely not implemented yet as it's a recent addition.

### Target Features

```typescript
// 1. Basic satisfies
const obj = { x: 1 } satisfies { x: number };

// 2. With const assertion
const config = {
    prod: "https://prod.com",
    dev: "https://dev.com",
} as const satisfies Record<string, string>;

// 3. In variable declarations
const palette = {
    red: [255, 0, 0],
    green: "#00ff00",
    blue: [0, 0, 255],
} satisfies Record<string, string | number[]>;

// 4. Chained with other type operators
const value = expr as T satisfies U;  // May not be valid, but test

// 5. In return statements
return { status: 200 } satisfies Response;

// 6. With generics
const data = { /* ... */ } satisfies Generic<T>;
```

## Instructions

### Step 1: Check Current State

```bash
# Test if satisfies is recognized (likely not)
cargo run --example parse -- 'const x = { a: 1 } satisfies T'
```

### Step 2: Extend AST

**File**: `parse-js/src/ast/expr.rs`

Add `Satisfies` expression variant:

```rust
#[derive(Debug, Clone, Serialize)]
pub enum Expr {
    // ... existing variants ...

    /// TypeScript satisfies operator: expr satisfies Type
    Satisfies {
        expr: Box<Node<Expr>>,
        type_: Box<Node<TypeExpr>>,
    },

    // ... other variants ...
}
```

Alternatively, if type operators are grouped:

```rust
#[derive(Debug, Clone, Serialize)]
pub enum Expr {
    // ...

    /// Type assertion: expr as Type, expr satisfies Type, <Type>expr
    TypeAssertion {
        expr: Box<Node<Expr>>,
        type_: Box<Node<TypeExpr>>,
        kind: TypeAssertionKind,
    },

    // ...
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum TypeAssertionKind {
    As,         // expr as Type
    Satisfies,  // expr satisfies Type
    Angle,      // <Type>expr (JSX conflicts)
}
```

### Step 3: Implement Parser

**File**: `parse-js/src/parse/expr.rs`

#### 3.1: Add satisfies to Binary Expression Parsing

The `satisfies` operator should have low precedence, similar to `as`:

```rust
impl<'a> Parser<'a> {
    /// Parse expression with type operators (as, satisfies)
    fn expr_with_type_operators(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Expr>> {
        let mut expr = self.conditional_expr(ctx)?;

        // Handle 'as' and 'satisfies' operators
        loop {
            if self.peek().typ == TT::KeywordAs {
                self.consume();
                let type_ = self.type_expr(ParseCtx::default())?;

                expr = Node::new(
                    self.loc_range(expr.loc.start),
                    Expr::TypeAssertion {
                        expr: Box::new(expr),
                        type_: Box::new(type_),
                        kind: TypeAssertionKind::As,
                    },
                );
            } else if self.peek().typ == TT::Identifier
                && self.peek().value == "satisfies"
            {
                self.consume();
                let type_ = self.type_expr(ParseCtx::default())?;

                expr = Node::new(
                    self.loc_range(expr.loc.start),
                    Expr::TypeAssertion {
                        expr: Box::new(expr),
                        type_: Box::new(type_),
                        kind: TypeAssertionKind::Satisfies,
                    },
                );
            } else {
                break;
            }
        }

        Ok(expr)
    }

    /// Update expression parsing to include type operators
    pub fn expression(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Expr>> {
        self.expr_with_type_operators(ctx)
    }
}
```

#### 3.2: Handle Operator Precedence

Make sure `satisfies` has correct precedence:

- Lower than all arithmetic/logical operators
- Same level as `as` operator
- Higher than comma operator

```rust
// Expression precedence (low to high):
// 1. Comma: a, b
// 2. Assignment: a = b
// 3. Conditional: a ? b : c
// 4. Type operators: a as T, a satisfies T  ← HERE
// 5. Logical OR: a || b
// ... (higher precedence)
```

#### 3.3: Alternative - Simpler Approach

If `satisfies` is just a postfix operator like `as`:

```rust
fn postfix_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Expr>> {
    let mut expr = self.primary_expr(ctx)?;

    loop {
        match self.peek().typ {
            // ... existing postfix operators (., [], (), etc.)

            TT::KeywordAs => {
                self.consume();
                let type_ = self.type_expr(ParseCtx::default())?;
                expr = Node::new(
                    self.loc_range(expr.loc.start),
                    Expr::As {
                        expr: Box::new(expr),
                        type_: Box::new(type_),
                    },
                );
            }

            _ if self.peek().value == "satisfies" => {
                self.consume();
                let type_ = self.type_expr(ParseCtx::default())?;
                expr = Node::new(
                    self.loc_range(expr.loc.start),
                    Expr::Satisfies {
                        expr: Box::new(expr),
                        type_: Box::new(type_),
                    },
                );
            }

            _ => break,
        }
    }

    Ok(expr)
}
```

### Step 4: Lexer Support (if needed)

**Check**: Is `satisfies` a keyword or contextual identifier?

**Answer**: It's a **contextual keyword** - only has special meaning in specific positions.

**Implication**: Don't add to lexer keywords. Parse as identifier and check value.

```rust
// In parser:
if self.peek().typ == TT::Identifier && self.peek().value == "satisfies" {
    // Handle satisfies operator
}
```

### Step 5: Write Tests

**File**: `parse-js/tests/satisfies_operator.rs`

```rust
use parse_js::*;

#[test]
fn test_satisfies_basic() {
    let src = r#"const obj = { x: 1 } satisfies { x: number };"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_with_const_assertion() {
    let src = r#"
        const config = {
            prod: "https://prod.com",
            dev: "https://dev.com",
        } as const satisfies Record<string, string>;
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_with_generics() {
    let src = r#"const data = { a: 1 } satisfies Record<string, number>;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_in_return() {
    let src = r#"
        function f() {
            return { status: 200 } satisfies Response;
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_with_array() {
    let src = r#"const arr = [1, 2, 3] satisfies number[];"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_with_function_call() {
    let src = r#"const result = fn() satisfies T;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_complex_type() {
    let src = r#"
        const palette = {
            red: [255, 0, 0],
            green: "#00ff00",
            blue: [0, 0, 255],
        } satisfies Record<string, string | number[]>;
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_as_identifier() {
    // 'satisfies' can be used as a regular identifier
    let src = r#"const satisfies = 1;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_satisfies_property_name() {
    let src = r#"const obj = { satisfies: true };"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_as_operator_still_works() {
    let src = r#"const x = value as number;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_nested_satisfies() {
    let src = r#"const x = (y satisfies A) satisfies B;"#;
    let result = parse(src);
    assert!(result.is_ok());
}
```

### Step 6: Run Tests

```bash
cargo test satisfies_operator
cargo test
cargo test --release conformance_runner -- --filter "satisfies"
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/06-satisfies-operator/implementation-report.md`

```markdown
# satisfies Operator Implementation Report

## Summary
Implemented TypeScript 4.9+ `satisfies` operator for type checking without type widening.

## Changes Made

### AST Changes
- Added `Satisfies` variant to `Expr` enum
- Or added `TypeAssertionKind::Satisfies` if grouped with `as`

### Parser Changes
- Updated expression parser to recognize `satisfies` contextual keyword
- Implemented with same precedence as `as` operator
- Supports chaining: `expr as T satisfies U`

## Test Results
- Unit tests: X/X passing
- Conformance tests: +X% improvement

## Examples Supported

```typescript
const config = { /* ... */ } satisfies Config;
const palette = { /* ... */ } satisfies Record<string, string | number[]>;
return { status: 200 } satisfies Response;
```

## Known Limitations
None - full support for all satisfies use cases.

## Performance Impact
Negligible - simple postfix operator parsing.
```

## Verification Commands

```bash
cargo check
cargo test satisfies_operator
cargo test --release conformance_runner
echo 'const x = {a:1} satisfies T' | cargo run --example parse
```

## Common Issues

### Issue 1: Contextual Keyword Handling
**Problem**: `satisfies` should be usable as identifier in non-operator positions

**Solution**: Only treat as operator when it follows an expression, not in declaration/binding positions

```rust
// These should work:
const satisfies = 1;           // satisfies is identifier
obj.satisfies();               // satisfies is property
function satisfies() {}        // satisfies is function name

// This is operator:
const x = expr satisfies T;    // satisfies is operator
```

### Issue 2: Precedence with `as`
**Problem**: How to parse `expr as T satisfies U`?

**Solution**: Both have same precedence, parse left-to-right:
```typescript
expr as T satisfies U
// Parses as: (expr as T) satisfies U
```

### Issue 3: Interaction with `as const`
**Problem**: `expr as const satisfies T` - order matters

**Solution**: Parse naturally due to precedence:
```typescript
expr as const satisfies T
// Parses as: (expr as const) satisfies T  ✓ Correct
```

## Acceptance Criteria

- [ ] `satisfies` operator parses in all valid positions
- [ ] Can be used as identifier when not in operator position
- [ ] Works with all type expressions
- [ ] Chains correctly with `as`
- [ ] All tests pass
- [ ] Conformance tests improve
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- Conformance improvement: +2-5%
- Zero regressions

## Resources

- TypeScript 4.9 Release Notes: The `satisfies` operator
- TypeScript Handbook: More on Functions - `satisfies`
- TypeScript source: `src/compiler/parser.ts` - search for "satisfies"

## Notes

The `satisfies` operator is relatively straightforward to implement as it's syntactically similar to `as`. The main complexity is ensuring it's treated as a contextual keyword rather than a reserved keyword.
