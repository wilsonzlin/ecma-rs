---
task_id: "02-planning/04-define-test-strategy"
title: "Define Comprehensive Testing Strategy"
phase: "planning"
estimated_duration: "3-4 hours"
complexity: "medium"
dependencies:
  - "02-planning/01-prioritize-features"
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "../../02-planning/01-prioritize-features/prioritized-features.json"
  - "../../02-planning/02-design-ast-nodes/ast-extensions.md"
  - "../../02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "test-strategy.md"
  - "test-templates.md"
  - "conformance-test-plan.md"
  - "regression-prevention.md"
skills_required:
  - "Testing strategy"
  - "Rust testing"
  - "TypeScript knowledge"
---

# Task: Define Comprehensive Testing Strategy

## Objective

Design a complete testing strategy covering unit tests, integration tests, conformance tests, and regression prevention for all new TypeScript parsing features.

## Context

### Why This Matters

Good tests:
1. **Catch bugs early** - Before they reach production
2. **Document behavior** - Tests as examples
3. **Enable refactoring** - Confidence to change code
4. **Prevent regressions** - Features stay working
5. **Guide implementation** - TDD approach

Without tests:
- Features break silently
- Edge cases missed
- Refactoring risky
- Code quality degrades

### Test Pyramid

```
           /\
          /  \    E2E Tests (conformance suite)
         /____\   Few, slow, comprehensive
        /      \
       /        \ Integration Tests (parser + AST)
      /__________\ Many, medium speed
     /            \
    /              \ Unit Tests (individual functions)
   /________________\ Most, fast, focused
```

### Current State

Existing tests:
- 21,065 TypeScript conformance tests
- Some unit tests (check parse-js/tests/)
- Conformance test runner

Need:
- Tests for new features
- Regression prevention
- Better coverage

## Prerequisites

### Files to Review

1. **Existing Tests** (`parse-js/tests/`)
   - See current test patterns
   - Note organization
   - Check coverage

2. **Conformance Runner** (`parse-js/tests/conformance_runner.rs`)
   - Understand test infrastructure
   - See parallel execution

3. **Planning Outputs**
   - AST extensions (task 02)
   - Parser plan (task 03)
   - Feature priorities (task 01)

### Testing Tools Available

```rust
// Unit tests
#[test]
fn test_name() { ... }

// Integration tests
#[test]
fn parse_full_file() { ... }

// Property-based testing (if needed)
use proptest::prelude::*;

// Fuzzing (if needed)
cargo fuzz

// Benchmarking
use criterion::{black_box, criterion_group, criterion_main, Criterion};
```

## Instructions

### Step 1: Define Test Levels

**test-strategy.md**:

```markdown
# Comprehensive Testing Strategy

## Test Levels

### Level 1: Unit Tests (Fast, Many)

**Scope**: Individual functions
**Speed**: <1ms per test
**Quantity**: 100+ tests
**Location**: `parse-js/src/parse/tests/`

**What to test**:
- Each parser function independently
- Edge cases for each feature
- Error conditions
- Boundary values

**Example**:
```rust
#[test]
fn test_type_param_const_modifier() {
    let src = "<const T extends readonly any[]>";
    let result = parse_type_parameters(src);

    let param = &result.unwrap()[0];
    assert_eq!(param.is_const, true);
    assert_eq!(param.name, "T");
}
```

---

### Level 2: Integration Tests (Medium, Some)

**Scope**: Parser + AST together
**Speed**: ~10ms per test
**Quantity**: 30-50 tests
**Location**: `parse-js/tests/integration/`

**What to test**:
- Complete type expressions
- Multiple features combined
- Realistic TypeScript code
- AST structure correctness

**Example**:
```rust
#[test]
fn test_complex_mapped_type() {
    let src = r#"
        type RemoveReadonly<T> = {
            -readonly [K in keyof T as Exclude<K, symbol>]: T[K]
        };
    "#;

    let ast = parse(src).unwrap();

    // Assert AST structure
    let type_alias = &ast.statements[0];
    assert!(matches!(type_alias, Stmt::TypeAlias(_)));

    // Check mapped type details
    let mapped = extract_mapped_type(type_alias);
    assert_eq!(mapped.readonly_modifier, Some(MappedModifier::Minus));
    assert!(mapped.name_type.is_some()); // 'as' clause present
}
```

---

### Level 3: Conformance Tests (Slow, Comprehensive)

**Scope**: Full TypeScript test suite
**Speed**: ~20 minutes for all
**Quantity**: 21,065 tests
**Location**: `parse-js/tests/TypeScript/`

**What to test**:
- All TypeScript syntax
- Official test cases
- Regression prevention
- Compatibility

**Execution**:
```bash
cargo test --release --test conformance_runner
```

**Success metric**: >95% pass rate

---

### Level 4: Property-Based Tests (Exploratory)

**Scope**: Generated test cases
**Speed**: Variable
**Quantity**: Thousands generated
**Location**: `parse-js/tests/property/`

**What to test**:
- Roundtrip: parse → print → parse
- Invariants (e.g., union is commutative)
- Fuzzing for crashes

**Example**:
```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn roundtrip_type_expr(type_str in any::<TypeExpr>()) {
        let source = type_str.to_source();
        let parsed = parse(&source).unwrap();
        let source2 = parsed.to_source();
        let parsed2 = parse(&source2).unwrap();

        // Should be equivalent
        assert_eq!(parsed, parsed2);
    }
}
```

---

## Test Categories by Feature

### Category A: New Parser Functions

For each new parser function:

**Required tests**:
1. Happy path (valid syntax)
2. Edge cases (boundary values)
3. Error cases (invalid syntax)
4. Integration with other features

**Example - Using Declarations**:
```rust
mod using_declarations {
    #[test]
    fn basic_using() {
        let src = "using resource = getResource();";
        let stmt = parse_stmt(src).unwrap();
        assert!(matches!(stmt, Stmt::Using(_)));
    }

    #[test]
    fn await_using() {
        let src = "await using resource = getResource();";
        let stmt = parse_stmt(src).unwrap();
        let using = extract_using(stmt);
        assert_eq!(using.is_await, true);
    }

    #[test]
    fn multiple_declarations() {
        let src = "using a = getA(), b = getB();";
        let stmt = parse_stmt(src).unwrap();
        let using = extract_using(stmt);
        assert_eq!(using.declarations.len(), 2);
    }

    #[test]
    fn error_missing_initializer() {
        let src = "using resource;";
        let result = parse_stmt(src);
        assert!(result.is_err());
    }
}
```

---

### Category B: Extended Parser Functions

For each modified function:

**Required tests**:
1. New feature works
2. Existing behavior preserved (regression)
3. New + old features combined

**Example - TypeParam.is_const**:
```rust
mod type_param_const {
    #[test]
    fn const_type_parameter() {
        let src = "<const T extends readonly any[]>";
        let params = parse_type_parameters(src).unwrap();
        assert_eq!(params[0].is_const, true);
    }

    #[test]
    fn regular_type_parameter() {
        // Regression: ensure non-const still works
        let src = "<T extends U>";
        let params = parse_type_parameters(src).unwrap();
        assert_eq!(params[0].is_const, false);
    }

    #[test]
    fn const_with_default() {
        let src = "<const T extends readonly any[] = []>";
        let params = parse_type_parameters(src).unwrap();
        assert_eq!(params[0].is_const, true);
        assert!(params[0].default.is_some());
    }
}
```

---

### Category C: Lookahead Logic

For each lookahead change:

**Required tests**:
1. Both paths of lookahead
2. Boundary cases (what triggers each path)
3. Combinations

**Example - readonly [ vs readonly T**:
```rust
mod readonly_lookahead {
    #[test]
    fn readonly_tuple() {
        let src = "type T = readonly [string, number];";
        let ast = parse(src).unwrap();
        let tuple = extract_tuple_type(ast);
        assert_eq!(tuple.readonly, true);
    }

    #[test]
    fn readonly_array() {
        let src = "type T = readonly string[];";
        let ast = parse(src).unwrap();
        // Should be ReadonlyType wrapping ArrayType
        assert!(matches!(ast, TypeExpr::Readonly(_)));
    }

    #[test]
    fn readonly_type_reference() {
        let src = "type T = readonly Foo;";
        let ast = parse(src).unwrap();
        assert!(matches!(ast, TypeExpr::Readonly(_)));
    }
}
```

---

## Test Organization

### Directory Structure

```
parse-js/tests/
├── conformance_runner.rs      # Main conformance test
├── integration/
│   ├── complex_types.rs       # Multi-feature tests
│   ├── real_world.rs          # Real TypeScript files
│   └── edge_cases.rs          # Tricky combinations
├── unit/
│   └── types/
│       ├── primitives.rs
│       ├── unions.rs
│       ├── conditionals.rs
│       ├── mapped.rs
│       ├── tuples.rs
│       ├── readonly_tuple_rest.rs  # NEW
│       ├── const_type_params.rs    # NEW
│       ├── typeof_import.rs        # NEW
│       └── using_declarations.rs   # NEW
└── property/
    └── roundtrip.rs           # Property-based tests
```

---

## Test Naming Convention

```rust
// Pattern: test_{feature}_{scenario}

#[test]
fn test_readonly_tuple_basic() { ... }

#[test]
fn test_readonly_tuple_with_rest() { ... }

#[test]
fn test_readonly_tuple_empty() { ... }

#[test]
fn test_readonly_tuple_error_missing_bracket() { ... }
```

**Naming rules**:
- Start with `test_`
- Feature name
- Scenario being tested
- Errors: end with `_error_{reason}`

---

## Assertion Patterns

### Pattern 1: Match AST Structure

```rust
#[test]
fn test_union_type() {
    let src = "type T = A | B | C;";
    let ast = parse(src).unwrap();

    match &ast.statements[0] {
        Stmt::TypeAlias(TypeAliasDecl {
            name,
            type_expr: TypeExpr::Union(union),
            ..
        }) => {
            assert_eq!(name, "T");
            assert_eq!(union.types.len(), 3);
        }
        _ => panic!("Expected TypeAlias with Union"),
    }
}
```

### Pattern 2: Extract and Assert

```rust
fn extract_mapped_type(stmt: &Stmt) -> &TypeMapped {
    match stmt {
        Stmt::TypeAlias(TypeAliasDecl {
            type_expr: TypeExpr::Mapped(mapped), ..
        }) => mapped,
        _ => panic!("Not a mapped type"),
    }
}

#[test]
fn test_mapped_with_as() {
    let src = "type T = { [K in keyof O as NewK]: V };";
    let ast = parse(src).unwrap();
    let mapped = extract_mapped_type(&ast.statements[0]);

    assert!(mapped.name_type.is_some());
}
```

### Pattern 3: Serialization Roundtrip

```rust
#[test]
fn test_serialization() {
    let src = "type T = readonly [string, ...number[]];";
    let ast = parse(src).unwrap();

    // Serialize to JSON
    let json = serde_json::to_string(&ast).unwrap();

    // Deserialize back
    let ast2: TopLevel = serde_json::from_str(&json).unwrap();

    // Should be identical
    assert_eq!(ast, ast2);
}
```
```

### Step 2: Create Test Templates

**test-templates.md**:

```markdown
# Test Templates for Each Feature

## Template 1: New Type Syntax

Use for: readonly tuples, typeof import, const type params, etc.

```rust
mod {feature_name} {
    use super::*;

    #[test]
    fn basic_{feature}() {
        let src = r#"type T = {TypeScript syntax};"#;
        let ast = parse(src).unwrap();

        // Assert it parsed
        assert!(matches!(&ast.statements[0], Stmt::TypeAlias(_)));

        // Assert AST structure
        let type_expr = extract_type_expr(&ast.statements[0]);
        assert!(matches!(type_expr, TypeExpr::{Variant}(_)));
    }

    #[test]
    fn {feature}_edge_case_1() {
        // Test boundary/edge case
    }

    #[test]
    fn {feature}_edge_case_2() {
        // Test another edge case
    }

    #[test]
    fn {feature}_combined_with_other() {
        // Test combination with other features
    }

    #[test]
    fn {feature}_error_invalid_syntax() {
        let src = r#"invalid syntax"#;
        let result = parse(src);
        assert!(result.is_err());
    }
}
```

---

## Template 2: Parser Function Extension

Use for: Modified functions that need backward compatibility tests

```rust
mod {function_name}_extension {
    use super::*;

    #[test]
    fn new_feature_works() {
        // Test new functionality
        let src = "new syntax";
        let result = {parser_function}(src).unwrap();
        assert_eq!(result.new_field, expected_value);
    }

    #[test]
    fn existing_behavior_preserved() {
        // REGRESSION TEST: old syntax still works
        let src = "old syntax";
        let result = {parser_function}(src).unwrap();
        assert_eq!(result, expected_old_result);
    }

    #[test]
    fn new_and_old_combined() {
        // Test that new + old features work together
        let src = "combined syntax";
        let result = {parser_function}(src).unwrap();
        // Assert both old and new aspects
    }
}
```

---

## Template 3: Lookahead Disambiguation

Use for: Features with ambiguous syntax requiring lookahead

```rust
mod {lookahead_case} {
    use super::*;

    #[test]
    fn path_a_{first_interpretation}() {
        // Test first interpretation (e.g., readonly tuple)
        let src = "syntax that triggers path A";
        let result = parse(src).unwrap();
        // Assert path A taken
    }

    #[test]
    fn path_b_{second_interpretation}() {
        // Test second interpretation (e.g., readonly modifier)
        let src = "syntax that triggers path B";
        let result = parse(src).unwrap();
        // Assert path B taken
    }

    #[test]
    fn lookahead_boundary() {
        // Test the exact boundary case
        // e.g., readonly followed by different tokens
    }
}
```

---

## Template 4: Error Cases

```rust
mod {feature}_errors {
    use super::*;

    #[test]
    fn error_{missing_required_token}() {
        let src = "incomplete syntax";
        let err = parse(src).unwrap_err();

        assert!(matches!(err, ParseError::UnexpectedToken { .. }));
        assert!(err.to_string().contains("Expected "));
    }

    #[test]
    fn error_{invalid_combination}() {
        let src = "invalid combination";
        let err = parse(src).unwrap_err();
        // Assert specific error
    }

    #[test]
    fn error_message_quality() {
        let src = "bad syntax";
        let err = parse(src).unwrap_err();

        let message = err.to_string();
        // Check error message is helpful
        assert!(message.contains("line"));
        assert!(message.contains("column"));
        assert!(message.contains("Expected") || message.contains("Help"));
    }
}
```

---

## Complete Example: readonly [T, ...U]

```rust
mod readonly_tuple_with_rest {
    use super::*;
    use crate::ast::{TypeExpr, TypeTuple, Stmt};

    #[test]
    fn basic_readonly_tuple_rest() {
        let src = "type T = readonly [string, ...number[]];";
        let ast = parse(src).unwrap();

        match &ast.statements[0] {
            Stmt::TypeAlias(type_alias) => {
                match &*type_alias.type_expr {
                    TypeExpr::Tuple(tuple) => {
                        assert_eq!(tuple.readonly, true);
                        assert_eq!(tuple.elements.len(), 2);

                        // First element: string
                        assert_eq!(tuple.elements[0].rest, false);

                        // Second element: ...number[]
                        assert_eq!(tuple.elements[1].rest, true);
                    }
                    _ => panic!("Expected Tuple type"),
                }
            }
            _ => panic!("Expected TypeAlias"),
        }
    }

    #[test]
    fn readonly_tuple_labeled_rest() {
        let src = "type T = readonly [first: string, ...rest: number[]];";
        let ast = parse(src).unwrap();

        let tuple = extract_tuple(&ast.statements[0]);
        assert_eq!(tuple.readonly, true);
        assert_eq!(tuple.elements[0].label, Some("first"));
        assert_eq!(tuple.elements[1].label, Some("rest"));
        assert_eq!(tuple.elements[1].rest, true);
    }

    #[test]
    fn readonly_empty_tuple() {
        let src = "type T = readonly [];";
        let ast = parse(src).unwrap();

        let tuple = extract_tuple(&ast.statements[0]);
        assert_eq!(tuple.readonly, true);
        assert_eq!(tuple.elements.len(), 0);
    }

    #[test]
    fn readonly_tuple_multiple_then_rest() {
        let src = "type T = readonly [string, number, boolean, ...any[]];";
        let ast = parse(src).unwrap();

        let tuple = extract_tuple(&ast.statements[0]);
        assert_eq!(tuple.elements.len(), 4);
        assert_eq!(tuple.elements[0].rest, false);
        assert_eq!(tuple.elements[1].rest, false);
        assert_eq!(tuple.elements[2].rest, false);
        assert_eq!(tuple.elements[3].rest, true);
    }

    #[test]
    fn regression_regular_tuple_still_works() {
        // Ensure non-readonly tuples still parse
        let src = "type T = [string, number];";
        let ast = parse(src).unwrap();

        let tuple = extract_tuple(&ast.statements[0]);
        assert_eq!(tuple.readonly, false);
    }

    #[test]
    fn regression_readonly_array_distinct() {
        // Ensure readonly T[] is different from readonly [T]
        let src = "type T = readonly string[];";
        let ast = parse(src).unwrap();

        // Should NOT be a tuple
        match extract_type_expr(&ast.statements[0]) {
            TypeExpr::Readonly(_) => {}, // Correct
            TypeExpr::Tuple(_) => panic!("Should be Readonly, not Tuple"),
            _ => panic!("Unexpected type"),
        }
    }

    #[test]
    fn serialization_roundtrip() {
        let src = "type T = readonly [string, ...number[]];";
        let ast = parse(src).unwrap();

        let json = serde_json::to_string(&ast).unwrap();
        let ast2: TopLevel = serde_json::from_str(&json).unwrap();

        assert_eq!(ast, ast2);
    }

    // Helper function
    fn extract_tuple(stmt: &Stmt) -> &TypeTuple {
        match stmt {
            Stmt::TypeAlias(alias) => {
                match &*alias.type_expr {
                    TypeExpr::Tuple(tuple) => tuple,
                    _ => panic!("Not a tuple"),
                }
            }
            _ => panic!("Not a type alias"),
        }
    }
}
```
```

### Step 3: Plan Conformance Test Strategy

**conformance-test-plan.md**:

```markdown
# Conformance Test Strategy

## Current Conformance Suite

- **Total tests**: 21,065
- **Current pass rate**: ~90% (estimated, need to run)
- **Location**: `parse-js/tests/TypeScript/`
- **Runner**: `conformance_runner.rs`

## Goals

- **Target pass rate**: >95%
- **Zero panics**: No crashes on any input
- **Clear failures**: Know why each test fails

## Execution Strategy

### Phase 1: Baseline (Week 1)

Run tests, establish baseline:

```bash
cargo test --release --test conformance_runner
```

**Outputs**:
- Pass rate: X%
- Failures list: Which tests fail
- Panic count: Any crashes

### Phase 2: Implementation (Weeks 2-3)

After each feature implementation:

```bash
# Run conformance tests
cargo test --release --test conformance_runner

# Compare with baseline
# Expected: pass rate increases
```

**Track progress**:
- Feature X implemented → +45 tests pass
- Feature Y implemented → +23 tests pass

### Phase 3: Final Validation (Week 4)

```bash
# Full test run
cargo test --release --test conformance_runner

# Target: >95% pass rate
```

## Failure Analysis

### Categorize Failures

From `typescript_conformance_failures.txt`:

1. **Missing features**: Syntax not implemented yet
2. **Parser bugs**: Feature exists but broken
3. **Edge cases**: Rare syntax combinations
4. **Test harness issues**: Test itself problematic

### Prioritize Fixes

**High Priority**:
- Panics (crashes)
- Common syntax (>10 failures)
- Regressions (used to pass)

**Medium Priority**:
- Moderate usage (2-10 failures)
- Edge cases with workarounds

**Low Priority**:
- Rare syntax (<2 failures)
- Experimental features

## Regression Prevention

### After Each Feature

```bash
# Save new baseline
cargo test --release --test conformance_runner -- --save-baseline feature-X
```

### Before Merging

```bash
# Compare with main branch
cargo test --release --test conformance_runner -- --baseline main

# Should not decrease pass rate
```

## Test Organization

### Per-Feature Tracking

```json
{
  "readonly_tuple_rest": {
    "tests_before": 18958,
    "tests_after": 19003,
    "tests_fixed": 45,
    "new_failures": 0,
    "net_improvement": 45
  }
}
```

## Success Metrics

- [ ] >95% conformance pass rate
- [ ] Zero panics on any test
- [ ] All regressions caught
- [ ] Failure categories understood
```

### Step 4: Plan Regression Prevention

**regression-prevention.md**:

```markdown
# Regression Prevention Strategy

## Definition

**Regression**: A feature that worked before now broken.

**Prevention**: Ensure features stay working as code changes.

## Strategies

### Strategy 1: Comprehensive Test Suite

**What**: Every feature has tests
**How**: Use templates (see test-templates.md)
**Effect**: Catch regressions immediately

**Example**:
```rust
#[test]
fn regression_readonly_tuple() {
    // This test protects readonly tuple feature
    let src = "type T = readonly [string, number];";
    assert!(parse(src).is_ok());
}
```

### Strategy 2: Continuous Integration

**What**: Run tests on every commit
**How**: GitHub Actions / CI pipeline
**Effect**: Fast feedback

**CI Configuration**:
```yaml
name: Tests
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - run: cargo test --release --all
      - run: cargo test --release --test conformance_runner
```

### Strategy 3: Conformance Baseline

**What**: Track conformance test pass rate
**How**: Save baseline, compare changes

```bash
# Save baseline
cargo test --test conformance_runner -- --save-baseline main

# Check for regressions
cargo test --test conformance_runner -- --baseline main

# Fail if pass rate decreases
```

### Strategy 4: Property-Based Testing

**What**: Generate random inputs
**How**: Use proptest
**Effect**: Find unexpected regressions

```rust
proptest! {
    #[test]
    fn no_panic_on_any_input(s in ".*") {
        // Should never panic, even on garbage input
        let _ = parse(&s);
    }
}
```

### Strategy 5: Fuzzing

**What**: Random mutation of inputs
**How**: `cargo fuzz`
**Effect**: Find crash bugs

```bash
cargo install cargo-fuzz
cargo fuzz run parse_target
```

## Regression Detection

### Automated Checks

```rust
// In CI:
fn check_regressions() {
    let baseline_pass_rate = load_baseline();
    let current_pass_rate = run_conformance_tests();

    assert!(
        current_pass_rate >= baseline_pass_rate,
        "Regression: pass rate decreased from {}% to {}%",
        baseline_pass_rate,
        current_pass_rate
    );
}
```

### Manual Review

Before merging PR:
- [ ] All existing tests pass
- [ ] Conformance rate not decreased
- [ ] No new panics introduced
- [ ] Performance not regressed (>10% slower)

## Recovery from Regressions

If regression found:

1. **Identify**: Which commit broke it?
   ```bash
   git bisect start
   git bisect bad HEAD
   git bisect good v1.0.0
   # Test each commit until found
   ```

2. **Fix**: Restore functionality

3. **Test**: Add regression test
   ```rust
   #[test]
   fn regression_issue_123() {
       // Reproduces bug from issue #123
       let src = "problematic code";
       assert!(parse(src).is_ok());
   }
   ```

4. **Prevent**: Why did tests not catch it?
   - Add missing test coverage
   - Improve test assertions

## Success Criteria

- [ ] All features have tests
- [ ] CI runs tests automatically
- [ ] Conformance baseline tracked
- [ ] Regression detection automated
- [ ] Recovery process defined
```

### Step 5: Create Testing Checklist

**test-strategy.md** (continued):

```markdown
## Implementation Testing Checklist

For each new/modified feature:

### Design Phase
- [ ] Test strategy defined
- [ ] Test cases identified
- [ ] Edge cases listed
- [ ] Error cases specified

### Implementation Phase
- [ ] Write failing test first (TDD)
- [ ] Implement feature
- [ ] Test passes
- [ ] Add edge case tests
- [ ] Add error case tests
- [ ] Check conformance tests

### Integration Phase
- [ ] Run full test suite
- [ ] Check for regressions
- [ ] Update baseline if needed
- [ ] Document test coverage

### Review Phase
- [ ] All tests pass
- [ ] No decrease in conformance rate
- [ ] No new warnings
- [ ] Performance impact acceptable

## Coverage Goals

| Component | Target Coverage | Current | Gap |
|-----------|----------------|---------|-----|
| Type primitives | 100% | ~100% | 0% |
| Type operators | 95% | ~90% | 5% |
| Advanced types | 90% | ~80% | 10% |
| New features | 100% | 0% | 100% |

## Test Metrics

Track over time:
- Total tests: Increasing
- Conformance pass rate: >95%
- Code coverage: >80% (if measured)
- Test execution time: <5 minutes

## Tools and Infrastructure

### Required
- `cargo test` - Basic testing
- Conformance runner - TypeScript tests

### Recommended
- `cargo-tarpaulin` - Code coverage
- `cargo-nextest` - Faster test runner
- `proptest` - Property-based testing

### Optional
- `cargo-fuzz` - Fuzzing
- `cargo-mutants` - Mutation testing
```

## Acceptance Criteria

### Required Outputs

✅ **test-strategy.md**: Complete testing strategy

✅ **test-templates.md**: Reusable test patterns

✅ **conformance-test-plan.md**: Conformance test approach

✅ **regression-prevention.md**: Regression prevention strategy

### Quality Checks

- [ ] All test levels defined
- [ ] Templates provided for common cases
- [ ] Conformance strategy clear
- [ ] Regression prevention comprehensive
- [ ] Examples included for each pattern

### Success Metrics

- Testing strategy complete
- All features covered
- Regression prevention planned
- Ready for implementation

## Common Issues & Solutions

### Issue: Unsure what to test

**Solution**:
- Start with happy path
- Add edge cases from TypeScript spec
- Look at TypeScript's own tests
- Think about invalid inputs

### Issue: Too many tests to write

**Solution**:
- Use templates
- Prioritize by feature importance
- Start with conformance tests
- Add unit tests for bugs found

### Issue: Tests are slow

**Solution**:
- Use `cargo nextest` (parallel)
- Mark slow tests with `#[ignore]`
- Run conformance tests separately
- Profile test suite

## Time Estimate Breakdown

- Define test levels: 45 min
- Create templates: 1 hour
- Plan conformance strategy: 45 min
- Regression prevention: 45 min
- Documentation: 45 min

**Total: 3-4 hours**

## Downstream Impact

Critical for:
- **03-implementation/***: TDD approach
- **04-validation/***: Validation strategy
- **Future maintenance**: Regression prevention

## Notes for Agent

- Good tests save debugging time later
- Templates make test writing faster
- Conformance tests are integration tests
- Regression prevention is critical
- Your test strategy determines code quality

---

**Ready?** Start with Step 1: Define Test Levels
