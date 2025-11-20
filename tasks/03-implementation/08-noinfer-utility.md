---
task_id: "03-implementation/08-noinfer-utility"
phase: "03-implementation"
title: "Implement NoInfer Utility Type"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/type_expr.rs" (modified)
  - "parse-js/src/parse/type_expr.rs" (modified)
  - "parse-js/tests/noinfer_utility.rs"
  - "workspace/outputs/03-implementation/08-noinfer-utility/implementation-report.md"
estimated_duration: "1-2 hours"
complexity: "low"
priority: "low"
---

# Task: Implement NoInfer Utility Type

## Objective

Implement TypeScript 5.4+ `NoInfer<T>` intrinsic utility type which prevents TypeScript from inferring type arguments from specific positions.

## Context

TypeScript 5.4 introduced `NoInfer<T>` as a built-in utility type to give developers control over type inference in generic functions.

### Use Case

```typescript
// Without NoInfer - unwanted inference
function createStreetLight<C extends string>(
    colors: C[],
    defaultColor: C  // TypeScript infers C from BOTH parameters
) {}

createStreetLight(["red", "yellow", "green"], "blue");
// Works! But "blue" shouldn't be valid

// With NoInfer - controlled inference
function createStreetLight<C extends string>(
    colors: C[],
    defaultColor: NoInfer<C>  // Don't infer from this parameter
) {}

createStreetLight(["red", "yellow", "green"], "blue");
// Error! "blue" is not assignable to "red" | "yellow" | "green"
```

### Current State
`NoInfer<T>` is likely not recognized as it's a recent addition (TS 5.4, March 2024).

### Target Features

```typescript
// 1. Basic NoInfer
function fn<T>(a: T, b: NoInfer<T>) {}

// 2. With arrays
function fn<T>(items: T[], default: NoInfer<T>) {}

// 3. With unions
function fn<T>(x: T | NoInfer<string>) {}

// 4. Nested
function fn<T>(x: NoInfer<NoInfer<T>>) {}  // Silly but valid

// 5. In object types
function fn<T>(obj: { a: T, b: NoInfer<T> }) {}

// 6. In type aliases
type Fn<T> = (a: T, b: NoInfer<T>) => void;
```

## Instructions

### Step 1: Check Current State

```bash
# Test if NoInfer is recognized (likely not)
cargo run --example parse_type -- 'type T = NoInfer<string>'
```

### Step 2: Determine Implementation Approach

`NoInfer<T>` can be implemented in two ways:

**Option A**: Intrinsic type (special AST node)
```rust
pub enum TypeExpr {
    // ...
    NoInfer(Box<Node<TypeExpr>>),
}
```

**Option B**: Regular type reference (like `Readonly<T>`, `Partial<T>`)
- No special AST node needed
- Parsed as `TypeReference` with name "NoInfer"
- Semantic meaning handled by type checker (if implemented)

**Recommendation**: **Option B** is simpler for parsing. The type checker would give `NoInfer` special meaning, but the parser can treat it as a regular generic type.

### Step 3: Check if Already Supported

If `NoInfer<T>` already parses as a regular type reference, this task may be **already complete**!

Test:
```bash
cargo run --example parse_type -- 'type T = NoInfer<string>'
```

If it parses successfully, then:
- ✅ Task complete - no code changes needed
- Document that `NoInfer` is supported as a type reference
- Write tests to ensure it continues to work

If it fails, investigate why (likely an unrelated issue).

### Step 4: If Special Support Needed

**Only if Option A is required** (unlikely):

**File**: `parse-js/src/ast/type_expr.rs`

```rust
#[derive(Debug, Clone, Serialize)]
pub enum TypeExpr {
    // ... existing variants ...

    /// NoInfer<T> - prevent type inference from this position
    NoInfer(Box<Node<TypeExpr>>),

    // ... other variants ...
}
```

**File**: `parse-js/src/parse/type_expr.rs`

```rust
impl<'a> Parser<'a> {
    fn type_reference(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
        let start = self.lexer.loc_start();
        let name = self.expect_identifier()?;

        // Special handling for intrinsic types
        if name == "NoInfer" && self.peek().typ == TT::LessThan {
            self.consume();  // <
            let inner = self.type_expr(ctx)?;
            self.expect(TT::GreaterThan)?;

            return Ok(Node::new(
                self.loc_range(start),
                TypeExpr::NoInfer(Box::new(inner)),
            ));
        }

        // Regular type reference
        // ... existing code ...
    }
}
```

### Step 5: Write Tests

**File**: `parse-js/tests/noinfer_utility.rs`

```rust
use parse_js::*;

#[test]
fn test_noinfer_basic() {
    let src = r#"type T = NoInfer<string>;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_in_function_parameter() {
    let src = r#"function fn<T>(a: T, b: NoInfer<T>) {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_with_array() {
    let src = r#"function fn<T>(items: T[], default: NoInfer<T>) {}"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_in_union() {
    let src = r#"type T<U> = U | NoInfer<string>;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_nested() {
    let src = r#"type T = NoInfer<NoInfer<number>>;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_in_object_type() {
    let src = r#"
        function fn<T>(obj: { a: T, b: NoInfer<T> }) {}
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_in_type_alias() {
    let src = r#"type Fn<T> = (a: T, b: NoInfer<T>) => void;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_complex_example() {
    let src = r#"
        function createStreetLight<C extends string>(
            colors: C[],
            defaultColor: NoInfer<C>
        ): void {}
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_with_conditional() {
    let src = r#"type T<U> = U extends string ? NoInfer<U> : never;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_noinfer_in_tuple() {
    let src = r#"type T<U> = [U, NoInfer<U>];"#;
    let result = parse(src);
    assert!(result.is_ok());
}
```

### Step 6: Run Tests

```bash
cargo test noinfer_utility
cargo test
cargo test --release conformance_runner -- --filter "NoInfer"
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/08-noinfer-utility/implementation-report.md`

```markdown
# NoInfer Utility Type Implementation Report

## Summary
Verified/Implemented support for TypeScript 5.4+ `NoInfer<T>` utility type.

## Approach
[Describe which approach was taken - likely "already supported as type reference"]

## Changes Made

### AST Changes
[Likely none - parsed as regular TypeReference]

### Parser Changes
[Likely none - no special handling needed]

## Test Results
- Unit tests: X/X passing
- Conformance tests: [results]

## Examples Supported

```typescript
function fn<T>(a: T, b: NoInfer<T>) {}
type T<U> = NoInfer<U>;
```

## Known Limitations
NoInfer is parsed as a regular type reference. Semantic meaning (preventing inference) is a type checker concern, not parser.

## Performance Impact
None - no parser changes or minimal changes.
```

## Verification Commands

```bash
cargo check
cargo test noinfer_utility
echo 'type T = NoInfer<string>' | cargo run --example parse_type
```

## Common Issues

### Issue 1: Not Recognized as Keyword
**Problem**: `NoInfer` isn't a keyword

**Solution**: It's not supposed to be! It's a regular identifier that TypeScript's type checker treats specially. The parser should treat it as a normal type reference.

### Issue 2: Confusion with Other Utilities
**Problem**: How is `NoInfer` different from `Readonly`, `Partial`, etc.?

**Solution**: From the parser's perspective, they're all the same - generic type references. The difference is semantic (handled by type checker).

## Acceptance Criteria

- [ ] `NoInfer<T>` parses as valid type
- [ ] Works in all positions where types are allowed
- [ ] Can be nested: `NoInfer<NoInfer<T>>`
- [ ] Works with other type operators
- [ ] All tests pass
- [ ] Conformance tests pass
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- No regressions
- Minimal/zero code changes (if already supported)

## Resources

- TypeScript 5.4 Release Notes: NoInfer Utility Type
- TypeScript Handbook: Utility Types
- TypeScript source: `src/lib/es5.d.ts` - NoInfer definition

## Notes

`NoInfer<T>` is syntactically trivial - it's just a generic type reference. The semantic meaning (controlling type inference) is entirely in the type checker. The parser should already support it without modification if generic type references work correctly.

**Recommendation**: Verify it works, write tests, document, done. Don't overthink it.
