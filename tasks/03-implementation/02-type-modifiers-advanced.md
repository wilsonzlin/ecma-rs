---
task_id: "03-implementation/02-type-modifiers-advanced"
phase: "03-implementation"
title: "Implement Advanced Type Modifiers"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/function-signatures.rs"
outputs:
  - "parse-js/src/ast/type_expr.rs" (modified)
  - "parse-js/src/parse/type_expr.rs" (modified)
  - "parse-js/tests/type_modifiers_advanced.rs"
  - "workspace/outputs/03-implementation/02-type-modifiers-advanced/implementation-report.md"
estimated_duration: "4-6 hours"
complexity: "high"
priority: "high"
---

# Task: Implement Advanced Type Modifiers

## Objective

Implement support for advanced TypeScript type modifiers that are currently missing or incomplete:
- `-?` optional modifier removal
- `+readonly` and `-readonly` modifier variance
- Readonly tuples with rest elements
- Optional property modifiers in mapped types

## Context

TypeScript supports advanced variance modifiers in mapped types and special combinations of modifiers in tuple types. These features are critical for accurately parsing modern TypeScript codebases that use utility types like `Required<T>`, `Readonly<T>`, and custom mapped type transformations.

### Current State
- Basic `readonly` and `?` modifiers work in simple cases
- Variance prefixes (`+`, `-`) may not be fully supported
- Readonly tuples with rest elements may not parse correctly

### Target Features

```typescript
// 1. Variance modifiers in mapped types
type Required<T> = { [K in keyof T]-?: T[K] };
type Mutable<T> = { -readonly [K in keyof T]: T[K] };
type ReadonlyPartial<T> = { +readonly [K in keyof T]+?: T[K] };

// 2. Readonly tuples with rest
type ReadonlyTupleRest = readonly [string, ...number[]];
type ReadonlyRestFirst = readonly [...string[], number];

// 3. Complex combinations
type ComplexMapped = {
  +readonly [K in keyof T as `get${K}`]-?: () => T[K]
};
```

## Instructions

### Step 1: Review AST Design

Read the AST design from Phase 2:
```bash
cat workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md | \
  grep -A 20 "Modifier"
```

Understand:
- How variance modifiers should be represented (`+`, `-`, or default)
- Whether to use an enum or boolean fields
- Impact on existing AST nodes

### Step 2: Extend AST Nodes

**File**: `parse-js/src/ast/type_expr.rs`

Add variance modifier support:

```rust
/// Modifier variance for mapped types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ModifierVariance {
    /// No explicit variance (default behavior)
    Default,
    /// + prefix (add modifier)
    Add,
    /// - prefix (remove modifier)
    Remove,
}

/// Property modifier in mapped types
#[derive(Debug, Clone, Serialize)]
pub struct PropertyModifier {
    /// readonly modifier
    pub readonly: Option<ModifierVariance>,
    /// optional (?) modifier
    pub optional: Option<ModifierVariance>,
}
```

Update existing structures:

```rust
pub struct TypeMapped {
    pub type_param: TypeParam,
    pub name_type: Option<Node<TypeExpr>>,
    pub type_expr: Option<Node<TypeExpr>>,
    pub modifiers: PropertyModifier,  // UPDATED: was separate bools
}

pub struct TypeTupleElement {
    pub label: Option<String>,
    pub optional: bool,
    pub rest: bool,
    pub readonly: bool,  // ADD: for readonly tuples
    pub type_expr: Node<TypeExpr>,
}
```

### Step 3: Implement Parser Extensions

**File**: `parse-js/src/parse/type_expr.rs`

#### 3.1: Parse Variance Modifiers

Add helper function:

```rust
impl<'a> Parser<'a> {
    /// Parse optional variance modifier (+ or -)
    fn parse_variance_modifier(&mut self) -> ModifierVariance {
        match self.peek().typ {
            TT::Plus => {
                self.consume();
                ModifierVariance::Add
            }
            TT::Minus => {
                self.consume();
                ModifierVariance::Remove
            }
            _ => ModifierVariance::Default,
        }
    }
}
```

#### 3.2: Update Mapped Type Parser

Modify `mapped_type()` function:

```rust
fn mapped_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    // ... existing code for '{'

    // Parse readonly with variance
    let readonly_variance = if self.consume_if(TT::KeywordReadonly).is_match() {
        // Already consumed 'readonly', check if there was a +/- before
        // Need to look back or parse in correct order
        Some(ModifierVariance::Default)  // Simplified
    } else {
        None
    };

    // Actually, need to parse variance BEFORE keyword:
    let readonly_variance = {
        let variance = self.parse_variance_modifier();
        if self.consume_if(TT::KeywordReadonly).is_match() {
            Some(variance)
        } else {
            None
        }
    };

    // Parse [K in keyof T]
    // ... existing code ...

    // Parse optional with variance
    let optional_variance = {
        let variance = self.parse_variance_modifier();
        if self.consume_if(TT::Question).is_match() {
            Some(variance)
        } else {
            None
        }
    };

    let modifiers = PropertyModifier {
        readonly: readonly_variance,
        optional: optional_variance,
    };

    // ... rest of function
}
```

#### 3.3: Update Tuple Type Parser

Modify `tuple_type()` function:

```rust
fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start = self.lexer.loc_start();

    // Check for 'readonly' prefix
    let readonly = self.consume_if(TT::KeywordReadonly).is_match();

    self.expect(TT::BracketOpen)?;

    let mut elements = Vec::new();

    while !self.consume_if(TT::BracketClose).is_match() {
        // Parse rest element
        let is_rest = self.consume_if(TT::DotDotDot).is_match();

        // Parse label if present: 'name: type' or 'name?: type'
        let (label, optional) = if self.peek_nth(1).typ == TT::Colon
            || self.peek_nth(1).typ == TT::Question
        {
            let name = self.expect_identifier()?;
            let optional = self.consume_if(TT::Question).is_match();
            self.expect(TT::Colon)?;
            (Some(name), optional)
        } else {
            (None, false)
        };

        let type_expr = self.type_expr(ctx)?;

        elements.push(TypeTupleElement {
            label,
            optional,
            rest: is_rest,
            readonly,  // Apply readonly from tuple-level to each element
            type_expr,
        });

        if !self.consume_if(TT::Comma).is_match() {
            self.expect(TT::BracketClose)?;
            break;
        }
    }

    Ok(Node::new(
        self.loc_range(start),
        TypeExpr::Tuple(elements),
    ))
}
```

### Step 4: Write Tests

**File**: `parse-js/tests/type_modifiers_advanced.rs`

Create comprehensive test suite:

```rust
use parse_js::*;

#[test]
fn test_variance_modifier_remove_optional() {
    let src = r#"
        type Required<T> = { [K in keyof T]-?: T[K] };
    "#;

    let result = parse(src);
    assert!(result.is_ok());

    let ast = result.unwrap();
    // Assert TypeMapped has optional: Some(Remove)
    // ... detailed assertions
}

#[test]
fn test_variance_modifier_remove_readonly() {
    let src = r#"
        type Mutable<T> = { -readonly [K in keyof T]: T[K] };
    "#;

    let result = parse(src);
    assert!(result.is_ok());
    // Assert TypeMapped has readonly: Some(Remove)
}

#[test]
fn test_variance_modifier_add_both() {
    let src = r#"
        type Both<T> = { +readonly [K in keyof T]+?: T[K] };
    "#;

    let result = parse(src);
    assert!(result.is_ok());
    // Assert both modifiers have Add variance
}

#[test]
fn test_readonly_tuple_with_rest() {
    let src = r#"
        type T = readonly [string, ...number[]];
    "#;

    let result = parse(src);
    assert!(result.is_ok());

    // Assert tuple elements have readonly=true
}

#[test]
fn test_readonly_rest_first() {
    let src = r#"
        type T = readonly [...string[], number];
    "#;

    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_labeled_readonly_tuple() {
    let src = r#"
        type Point = readonly [x: number, y: number];
    "#;

    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_complex_mapped_type() {
    let src = r#"
        type Getters<T> = {
            +readonly [K in keyof T as `get${K & string}`]-?: () => T[K]
        };
    "#;

    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_no_variance_default() {
    let src = r#"
        type Simple<T> = { readonly [K in keyof T]?: T[K] };
    "#;

    let result = parse(src);
    assert!(result.is_ok());
    // Assert modifiers use Default variance
}
```

### Step 5: Run and Verify Tests

```bash
# Run new tests
cargo test type_modifiers_advanced

# Run all type expression tests
cargo test --test type_expr

# Check for regressions
cargo test
```

### Step 6: Test Against Conformance Suite

```bash
# Run conformance tests for mapped types
cargo test --release conformance_runner -- --filter "mappedType"

# Run conformance tests for tuple types
cargo test --release conformance_runner -- --filter "tuple"
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/02-type-modifiers-advanced/implementation-report.md`

Document:
```markdown
# Advanced Type Modifiers Implementation Report

## Summary
Implemented support for TypeScript variance modifiers in mapped types and readonly tuple types.

## Changes Made

### AST Extensions
- Added `ModifierVariance` enum (Default, Add, Remove)
- Added `PropertyModifier` struct
- Updated `TypeMapped` to use `PropertyModifier`
- Added `readonly` field to `TypeTupleElement`

### Parser Changes
- Added `parse_variance_modifier()` helper
- Updated `mapped_type()` to parse variance prefixes
- Updated `tuple_type()` to handle readonly prefix

## Test Results
- Unit tests: X/Y passing
- Conformance tests: X/Y passing
- New test coverage: X additional test cases

## Examples Supported

### Before
```typescript
// Could only parse:
type T = { readonly [K in keyof T]: T[K] };
```

### After
```typescript
// Now supports:
type Required<T> = { [K in keyof T]-?: T[K] };
type Mutable<T> = { -readonly [K in keyof T]: T[K] };
type ReadonlyTuple = readonly [string, ...number[]];
```

## Known Limitations
[List any remaining issues or edge cases]

## Performance Impact
[Note any performance changes observed]
```

## Verification Commands

```bash
# 1. Compile check
cargo check

# 2. Run tests
cargo test type_modifiers_advanced

# 3. Check AST output
cargo run --example parse_type -- "type T = { -readonly [K in keyof T]-?: T[K] }"

# 4. Run conformance tests
cargo test --release conformance_runner
```

## Common Issues

### Issue 1: Ambiguity with Binary Minus
**Problem**: `-readonly` could be confused with binary minus operator

**Solution**: Check context - in mapped type context, `-` before `readonly` or `?` is always a variance modifier

```rust
// In mapped_type() function:
let variance = self.parse_variance_modifier();
// Must be followed by 'readonly' or type expression
```

### Issue 2: Readonly on Wrong Tuple Element
**Problem**: `readonly` applies to entire tuple, not individual elements

**Solution**: Parse `readonly` at tuple level, propagate to all elements

```rust
let readonly = self.consume_if(TT::KeywordReadonly).is_match();
// ... later, for each element:
elements.push(TypeTupleElement { readonly, ... });
```

### Issue 3: Variance Without Modifier
**Problem**: Parsing `+` without following `readonly` or `?`

**Solution**: Validate that variance is followed by appropriate keyword

```rust
let variance = self.parse_variance_modifier();
if variance != ModifierVariance::Default {
    // Must be followed by 'readonly' or reach '?' position
    if !matches!(self.peek().typ, TT::KeywordReadonly | ...) {
        return Err(SyntaxError::expected("readonly or ?"));
    }
}
```

## Acceptance Criteria

- [ ] AST extensions implemented as designed
- [ ] Parser correctly handles all variance modifier combinations
- [ ] Readonly tuples with rest elements parse correctly
- [ ] All unit tests pass
- [ ] Conformance test pass rate improves or stays same
- [ ] No panics on fuzz testing
- [ ] Implementation report created

## Success Metrics

- Parse all TypeScript utility types: `Required<T>`, `Readonly<T>`, `Partial<T>`, etc.
- Conformance tests: +5-10% pass rate improvement
- Zero regressions in existing tests

## Resources

- TypeScript Handbook: Mapped Types
- TypeScript source: `src/compiler/parser.ts` (search for "MappedType")
- TypeScript spec: Mapped Type Grammar

## Notes

This task focuses on **parsing only**. Type checking or semantic validation of variance modifiers is out of scope for this phase. The goal is to correctly represent the syntax in the AST.
