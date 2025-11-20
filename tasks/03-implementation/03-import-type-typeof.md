---
task_id: "03-implementation/03-import-type-typeof"
phase: "03-implementation"
title: "Implement typeof with import() Type"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/type_expr.rs" (modified)
  - "parse-js/src/parse/type_expr.rs" (modified)
  - "parse-js/tests/import_type_typeof.rs"
  - "workspace/outputs/03-implementation/03-import-type-typeof/implementation-report.md"
estimated_duration: "3-4 hours"
complexity: "medium"
priority: "medium"
---

# Task: Implement typeof with import() Type

## Objective

Implement support for combining `typeof` operator with `import()` type syntax:
- `typeof import("module")`
- `typeof import("module").member`
- Nested combinations: `typeof import("./mod").default.foo`

## Context

TypeScript allows using `typeof` with dynamic import types to extract the type of a module or its exports without importing the value. This is commonly used in type-only contexts and declaration files.

### Current State
- Basic `typeof` operator likely works: `typeof value`
- Basic `import("...")` type likely works: `import("module").Type`
- Combination may not work: `typeof import("module")`

### Target Features

```typescript
// 1. typeof import - get module type
type ModuleType = typeof import("./module");

// 2. typeof import member - get export type
type ExportType = typeof import("./module").exportedValue;

// 3. typeof import default
type DefaultType = typeof import("./component").default;

// 4. Nested member access
type NestedType = typeof import("./lib").default.foo.bar;

// 5. In generic constraints
function f<T extends typeof import("./mod")>() {}

// 6. Combined with indexed access
type PropType = (typeof import("./mod").config)["apiUrl"];
```

## Instructions

### Step 1: Understand Current AST

Check current representation:
```bash
# Test if basic import type works
cargo run --example parse_type -- 'type T = import("mod").Type'

# Test if typeof works
cargo run --example parse_type -- 'type T = typeof value'

# Test combination (likely fails)
cargo run --example parse_type -- 'type T = typeof import("mod")'
```

### Step 2: Review AST Structure

**File**: `parse-js/src/ast/type_expr.rs`

Verify these exist:

```rust
pub enum TypeExpr {
    // ...
    TypeOf(Box<Node<TypeExpr>>),  // typeof T
    Import {
        path: String,
        qualifier: Option<Vec<String>>,  // .member.submember
    },
    // ...
}
```

If `TypeOf` takes an expression instead of type:
```rust
pub enum TypeExpr {
    TypeOf(Box<Node<Expr>>),  // typeof value
    // Need to support typeof on type expressions too
}
```

### Step 3: Determine Necessary Changes

**Option A**: `TypeOf` already supports type expressions
- Just need to ensure `import()` type can be parsed inside `typeof`
- No AST changes needed

**Option B**: `TypeOf` only supports value expressions
- Need to allow both value and type expressions
- May need new variant or union type

**Recommended approach** (verify current code first):
```rust
pub enum TypeExpr {
    // ...
    TypeOf(Box<TypeOfTarget>),
    // ...
}

pub enum TypeOfTarget {
    /// typeof value (value expression)
    Expr(Box<Node<Expr>>),
    /// typeof import("...") (type expression)
    ImportType { path: String, members: Vec<String> },
}
```

### Step 4: Implement Parser

**File**: `parse-js/src/parse/type_expr.rs`

#### 4.1: Parse typeof Operator

Update `typeof_type()` or equivalent function:

```rust
impl<'a> Parser<'a> {
    fn typeof_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
        let start = self.lexer.loc_start();

        self.expect(TT::KeywordTypeof)?;

        // Check if next token is 'import'
        if self.peek().typ == TT::KeywordImport {
            self.consume();
            self.expect(TT::ParenOpen)?;

            // Parse module path
            let path = self.expect_string_literal()?;

            self.expect(TT::ParenClose)?;

            // Parse optional member access chain
            let mut members = Vec::new();
            while self.consume_if(TT::Dot).is_match() {
                members.push(self.expect_identifier()?);
            }

            Ok(Node::new(
                self.loc_range(start),
                TypeExpr::TypeOf(Box::new(TypeOfTarget::ImportType { path, members })),
            ))
        } else {
            // Parse as value expression
            let expr = self.unary_expr(ctx)?;

            Ok(Node::new(
                self.loc_range(start),
                TypeExpr::TypeOf(Box::new(TypeOfTarget::Expr(expr))),
            ))
        }
    }
}
```

#### 4.2: Alternative Simpler Approach

If AST already represents `import("...")` as a `TypeExpr`, just parse it:

```rust
fn typeof_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start = self.lexer.loc_start();
    self.expect(TT::KeywordTypeof)?;

    // Parse the operand as a type expression (which includes import types)
    let operand = self.type_primary(ctx)?;

    Ok(Node::new(
        self.loc_range(start),
        TypeExpr::TypeOf(Box::new(operand)),
    ))
}
```

**Key insight**: In type contexts, `typeof import("...")` treats the entire `import("...")` as a type expression, not a value expression. This makes parsing simpler.

### Step 5: Handle Member Access

Ensure member access works after `import()`:

```rust
fn type_postfix(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let mut base = self.type_primary(ctx)?;

    loop {
        match self.peek().typ {
            TT::Dot => {
                self.consume();
                let member = self.expect_identifier()?;

                base = Node::new(
                    self.loc_range(base.loc.start),
                    TypeExpr::MemberAccess {
                        object: Box::new(base),
                        member,
                    },
                );
            }

            TT::BracketOpen => {
                // Indexed access: T["key"]
                self.consume();
                let index = self.type_expr(ctx)?;
                self.expect(TT::BracketClose)?;

                base = Node::new(
                    self.loc_range(base.loc.start),
                    TypeExpr::IndexedAccess {
                        object: Box::new(base),
                        index: Box::new(index),
                    },
                );
            }

            _ => break,
        }
    }

    Ok(base)
}
```

### Step 6: Write Tests

**File**: `parse-js/tests/import_type_typeof.rs`

```rust
use parse_js::*;

#[test]
fn test_typeof_import_simple() {
    let src = r#"type T = typeof import("./module");"#;
    let result = parse(src);
    assert!(result.is_ok(), "Should parse typeof import");
}

#[test]
fn test_typeof_import_member() {
    let src = r#"type T = typeof import("./module").exportedValue;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_typeof_import_default() {
    let src = r#"type T = typeof import("./component").default;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_typeof_import_nested_members() {
    let src = r#"type T = typeof import("./lib").default.foo.bar;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_typeof_import_in_generic() {
    let src = r#"function f<T extends typeof import("./mod")>() {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_typeof_import_with_indexed_access() {
    let src = r#"type T = (typeof import("./mod").config)["apiUrl"];"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_typeof_import_relative_path() {
    let src = r#"type T = typeof import("../utils/helper");"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_typeof_import_scoped_package() {
    let src = r#"type T = typeof import("@org/package");"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_import_without_typeof() {
    let src = r#"type T = import("./mod").Type;"#;
    let result = parse(src);
    assert!(result.is_ok(), "Regular import type should still work");
}

#[test]
fn test_typeof_value_expression() {
    let src = r#"type T = typeof myValue;"#;
    let result = parse(src);
    assert!(result.is_ok(), "Regular typeof should still work");
}
```

### Step 7: Run Tests

```bash
# Run new tests
cargo test import_type_typeof

# Run all tests
cargo test

# Test against conformance suite
cargo test --release conformance_runner -- --filter "import"
cargo test --release conformance_runner -- --filter "typeof"
```

### Step 8: Manual Testing

```bash
# Test various combinations
cargo run --example parse_type -- 'type T = typeof import("mod")'
cargo run --example parse_type -- 'type T = typeof import("mod").member'
cargo run --example parse_type -- 'type T = (typeof import("mod"))["key"]'
```

### Step 9: Create Implementation Report

**File**: `workspace/outputs/03-implementation/03-import-type-typeof/implementation-report.md`

```markdown
# typeof import() Implementation Report

## Summary
Implemented support for `typeof` operator with `import()` type syntax.

## Changes Made

### AST Changes
[Describe any AST modifications - likely none if using existing TypeOf + Import nodes]

### Parser Changes
- Updated `typeof_type()` to recognize `import` keyword after `typeof`
- Ensured `type_postfix()` handles member access on import types
- [Any other changes]

## Test Results
- Unit tests: X/X passing
- Conformance tests: [results]

## Examples Supported

```typescript
type T1 = typeof import("./module");
type T2 = typeof import("./module").member;
type T3 = typeof import("./lib").default.nested;
type T4 = (typeof import("./config"))["key"];
```

## Known Limitations
[Any limitations or edge cases not supported]

## Performance Impact
No significant performance impact expected - minor additional parsing logic.
```

## Verification Commands

```bash
# 1. Compile
cargo check

# 2. Unit tests
cargo test import_type_typeof

# 3. Conformance tests
cargo test --release conformance_runner

# 4. Manual verification
echo 'type T = typeof import("mod")' | cargo run --example parse_type
```

## Common Issues

### Issue 1: Ambiguity Between typeof Expression and typeof Type
**Problem**: `typeof import(...)` could be parsed as expression or type

**Solution**: In type context, always parse as type. The context (`ParseCtx`) should indicate we're in a type position.

### Issue 2: Member Access Not Working
**Problem**: `typeof import("mod").member` parses but member access not applied

**Solution**: Ensure `typeof` result goes through `type_postfix()` to handle member/indexed access

```rust
fn type_prefix(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let base = match self.peek().typ {
        TT::KeywordTypeof => self.typeof_type(ctx)?,
        _ => return self.type_postfix(ctx),
    };

    // Apply postfix operators to typeof result
    self.apply_type_postfix(base, ctx)
}
```

### Issue 3: String Literal Path Parsing
**Problem**: Import path might be parsed incorrectly (template literals, etc.)

**Solution**: Only accept simple string literals for import paths

```rust
fn expect_string_literal(&mut self) -> SyntaxResult<String> {
    match self.peek().typ {
        TT::LitStr => {
            let value = self.peek().value.clone();
            self.consume();
            Ok(value)
        }
        _ => Err(SyntaxError::expected("string literal"))
    }
}
```

## Acceptance Criteria

- [ ] `typeof import("...")` parses correctly
- [ ] Member access works: `typeof import("...").member`
- [ ] Nested members work: `typeof import("...").a.b.c`
- [ ] Works in generic constraints
- [ ] Works with indexed access
- [ ] All unit tests pass
- [ ] Conformance tests pass or improve
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- Conformance test improvement: +2-5%
- No regressions

## Resources

- TypeScript Handbook: Modules - `import()` types
- TypeScript source: `src/compiler/parser.ts` - `parseTypeQuery`
- MDN: typeof operator

## Notes

This feature is primarily used in declaration files (`.d.ts`) and type-only contexts. The implementation should focus on parsing correctness; semantic validation is out of scope.
