---
task_id: "03-implementation/01-readonly-tuples-rest"
title: "Implement Readonly Tuples with Rest Elements"
phase: "implementation"
estimated_duration: "4-8 hours"
complexity: "medium"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
  - "02-planning/04-define-test-strategy"
inputs:
  - "../../02-planning/02-design-ast-nodes/ast-extensions.md"
  - "../../02-planning/03-plan-parser-extensions/parser-plan.md"
  - "../../02-planning/04-define-test-strategy/test-templates.md"
outputs:
  - "implementation-notes.md"
  - "test-cases.rs"
  - "lessons-learned.md"
  - "git-patch.diff"
skills_required:
  - "Rust programming"
  - "Parser implementation"
  - "TypeScript knowledge"
  - "Testing"
---

# Task: Implement Readonly Tuples with Rest Elements

## Objective

Add support for TypeScript's readonly tuple types with rest elements:

```typescript
type T1 = readonly [string, ...number[]];
type T2 = readonly [first: string, ...rest: number[]];
type T3 = readonly [string, number, ...boolean[]];
```

## Context

### Feature Description

TypeScript allows tuple types to be marked `readonly` and include rest elements (`...`). This combines two features:
1. **Readonly modifier**: Makes tuple immutable
2. **Rest elements**: Variable-length tail in tuple

### Current State

Based on analysis phase:
- AST has `TypeTuple` struct with `readonly: bool` field
- AST has `TypeTupleElement` struct with `rest: bool` field
- Parser handles readonly arrays: `readonly string[]`
- Parser handles tuple rest: `[string, ...number[]]`
- **Missing**: Combination of both features

### Why This Feature

- Priority: **HIGH** (45 test failures)
- TypeScript version: 3.4
- Common in real code: Yes (type-safe array operations)
- Difficulty: **LOW** (combines existing features)

## Prerequisites

### Files to Understand

1. **AST Definition**: `parse-js/src/ast/type_expr.rs`
   - Lines 151-169: `TypeTuple` and `TypeTupleElement` structs
   - Already has `readonly` field ✅

2. **Parser**: `parse-js/src/parse/type_expr.rs`
   - Lines 1156-1182: `tuple_type()` function
   - Lines 1184-1224: `tuple_element()` function
   - Lines 320-380: readonly modifier handling

3. **Test Runner**: `parse-js/tests/conformance_runner.rs`

### TypeScript Specification

From TypeScript handbook:
```typescript
// Readonly tuple
type T1 = readonly [string, number];

// Tuple with rest
type T2 = [string, ...number[]];

// COMBINATION (what we're implementing)
type T3 = readonly [string, ...number[]];

// With labels
type T4 = readonly [name: string, ...ids: number[]];
```

## Instructions

### Step 1: Write Failing Tests

Create `parse-js/src/parse/tests/types/readonly_tuple_rest.rs`:

```rust
use crate::parse::parse;

#[test]
fn test_readonly_tuple_with_rest_basic() {
    let src = r#"type T = readonly [string, ...number[]];"#;
    let result = parse(src);

    assert!(result.is_ok(), "Should parse successfully");

    let ast = result.unwrap();
    // TODO: Add assertions about AST structure
}

#[test]
fn test_readonly_tuple_with_rest_labeled() {
    let src = r#"type T = readonly [first: string, ...rest: number[]];"#;
    let result = parse(src);

    assert!(result.is_ok(), "Should parse labeled readonly tuple with rest");
}

#[test]
fn test_readonly_tuple_multiple_elements_then_rest() {
    let src = r#"type T = readonly [string, number, boolean, ...any[]];"#;
    let result = parse(src);

    assert!(result.is_ok(), "Should parse multiple elements before rest");
}

#[test]
fn test_readonly_tuple_rest_must_be_array() {
    let src = r#"type T = readonly [string, ...number];"#;
    let result = parse(src);

    // This should fail - rest must be array type
    assert!(result.is_err(), "Rest element must be array type");
}

#[test]
fn test_readonly_empty_tuple() {
    let src = r#"type T = readonly [];"#;
    let result = parse(src);

    assert!(result.is_ok(), "Should parse empty readonly tuple");
}
```

Run tests to confirm they fail:
```bash
cd /home/user/ecma-rs/parse-js
cargo test readonly_tuple_rest
```

Expected: All tests fail (feature not implemented yet)

### Step 2: Understand Current Parser Logic

Read `parse-js/src/parse/type_expr.rs`:

**Current `tuple_type()` implementation** (lines 1156-1182):
```rust
fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::BracketOpen)?;

    let mut elements = Vec::new();
    // ... parse elements ...

    self.require(TT::BracketClose)?;

    Ok(Node::new(outer_loc, TypeExpr::TupleType(Node::new(start_loc, TypeTuple {
        readonly: false,  // ❌ Always false!
        elements,
    }))))
}
```

**Current `type_primary()` handling** (lines 320-380):
```rust
TT::KeywordReadonly => {
    // Handles: readonly T[]
    // Does NOT handle: readonly [T, U]
}
```

### Step 3: Implement Parser Changes

**Modify `type_primary()` to recognize `readonly` before `[`**:

```rust
// In type_primary(), around line 322
TT::KeywordReadonly => {
    let [_, next] = self.peek_n::<2>();

    if next.typ == TT::BracketOpen {
        // readonly [T, U] - it's a readonly tuple!
        self.consume(); // consume 'readonly'
        let readonly = true;

        let start_loc = self.peek().loc;
        self.require(TT::BracketOpen)?;

        let mut elements = Vec::new();
        let end_loc;

        loop {
            if self.peek().typ == TT::BracketClose {
                end_loc = self.peek().loc;
                self.consume();
                break;
            }

            elements.push(self.tuple_element(ctx)?);

            if !self.consume_if(TT::Comma).is_match() {
                end_loc = self.peek().loc;
                self.require(TT::BracketClose)?;
                break;
            }
        }

        use crate::loc::Loc;
        let outer_loc = Loc(start_loc.0, end_loc.1);
        let tuple = Node::new(start_loc, TypeTuple {
            readonly,  // ✅ Now true!
            elements
        });
        return Ok(Node::new(outer_loc, TypeExpr::TupleType(tuple)));
    } else {
        // readonly T[] - existing logic
        // ... keep current code ...
    }
}
```

**Alternative: Refactor to share code with `tuple_type()`**:

```rust
// Add parameter to tuple_type
fn tuple_type(&mut self, ctx: ParseCtx, readonly: bool) -> SyntaxResult<Node<TypeExpr>> {
    // existing implementation, but use readonly parameter
}

// In type_primary
TT::KeywordReadonly => {
    let [_, next] = self.peek_n::<2>();
    if next.typ == TT::BracketOpen {
        self.consume(); // consume 'readonly'
        return self.tuple_type(ctx, true);
    }
    // ... existing readonly T[] logic
}

TT::BracketOpen => {
    // Regular tuple (not readonly)
    self.tuple_type(ctx, false)
}
```

### Step 4: Run Tests

```bash
cargo test readonly_tuple_rest
```

Expected: Tests now pass! ✅

If tests fail, debug:
1. Print AST: `println!("{:#?}", ast);`
2. Check token stream: Add debug logging
3. Verify tuple_element() handles rest correctly (should already work)

### Step 5: Run Conformance Tests

```bash
cargo test --release --test conformance_runner
```

Compare with baseline:
- Previous: X% pass rate
- Now: X+N% pass rate
- New passes: Should include readonly tuple tests

### Step 6: Document Implementation

Create `implementation-notes.md`:

```markdown
# Implementation: Readonly Tuples with Rest Elements

## Summary

Added support for `readonly [T, ...U[]]` syntax by extending `type_primary()` to recognize `readonly` keyword before tuple brackets.

## Changes Made

### File: parse-js/src/parse/type_expr.rs

**Function: `type_primary()`** (line ~322)
- Added lookahead check for `readonly` followed by `[`
- Route to tuple parsing with readonly=true
- Refactored to avoid code duplication

## Test Coverage

- ✅ Basic readonly tuple with rest
- ✅ Labeled elements
- ✅ Multiple elements before rest
- ✅ Empty readonly tuple
- ✅ Error case: rest must be array type

## Conformance Impact

- Previous pass rate: 90.00%
- New pass rate: 90.21%
- New passing tests: 45 (all readonly tuple tests)

## Edge Cases Handled

1. **Empty tuple**: `readonly []` ✅
2. **No rest**: `readonly [string, number]` ✅ (already worked)
3. **Rest only**: `readonly [...number[]]` ✅
4. **Multiple rest**: `[...number[], ...string[]]` ❌ (TypeScript error, parser rejects)

## Known Limitations

None - feature complete!

## Performance Impact

Minimal - adds one lookahead check in hot path. No measurable impact.

## Lessons Learned

- Lookahead pattern works well for keyword+bracket combinations
- Code sharing between readonly array and readonly tuple kept implementation DRY
- Test-first approach caught edge case with empty tuples early
```

Create `lessons-learned.md`:

```markdown
# Lessons Learned: Readonly Tuples with Rest

## What Went Well

- **Clear specification**: TypeScript docs were unambiguous
- **Existing infrastructure**: AST and tuple_element() already supported needed features
- **Test-first approach**: Caught edge cases before implementing

## Challenges

- **Code duplication**: Initial implementation duplicated tuple parsing logic
  - **Solution**: Refactored to add readonly parameter to tuple_type()

- **Lookahead complexity**: Multiple token lookahead felt fragile
  - **Mitigation**: Documented the pattern, added clear comments

## Unexpected Discoveries

- Empty readonly tuples are valid: `readonly []`
- Parser already handled rest elements correctly in tuples
- No performance impact from additional lookahead

## Recommendations for Future Features

1. Always check for existing similar features first
2. Prefer refactoring to share code over duplication
3. Test edge cases early (empty, single element, complex)
4. Run full conformance suite, not just new tests

## Time Estimate Accuracy

- Estimated: 4-8 hours
- Actual: 5 hours
  - Planning: 1 hour
  - Implementation: 2 hours
  - Testing: 1 hour
  - Documentation: 1 hour

## Code Quality

- No new warnings
- No clippy issues
- Follows existing code style
- Well-commented
```

### Step 7: Create Git Patch

```bash
cd /home/user/ecma-rs

# Commit changes
git add parse-js/src/parse/type_expr.rs
git add parse-js/src/parse/tests/types/readonly_tuple_rest.rs
git commit -m "feat(parser): Add readonly tuple with rest elements support

- Extend type_primary() to handle 'readonly [T, ...U[]]' syntax
- Add comprehensive test coverage
- Fixes 45 conformance test failures
- TypeScript 3.4 compatibility

Closes: readonly-tuple-rest implementation task"

# Create patch
git format-patch -1 HEAD --stdout > workspace/outputs/03-implementation/01-readonly-tuples-rest/git-patch.diff
```

## Acceptance Criteria

### Required Outputs

✅ **implementation-notes.md**: Complete implementation summary

✅ **test-cases.rs**: Comprehensive test coverage (5+ tests)

✅ **lessons-learned.md**: Insights for future tasks

✅ **git-patch.diff**: Clean, committable changes

### Quality Checks

- [ ] All new tests pass
- [ ] No regressions (existing tests still pass)
- [ ] Conformance pass rate increased
- [ ] Code follows project style
- [ ] No new compiler warnings
- [ ] Changes are minimal (no over-engineering)

### Success Metrics

- Feature fully implemented ✅
- Tests comprehensive ✅
- Documentation clear ✅
- Ready to merge ✅

## Verification Commands

```bash
# Run new tests
cargo test readonly_tuple_rest

# Run all parser tests
cargo test --package parse-js

# Check conformance improvement
cargo test --release --test conformance_runner | grep "Passed:"

# Verify no warnings
cargo clippy --package parse-js
```

## Common Issues & Solutions

### Issue: Tests pass but conformance still fails
**Diagnosis**: Check if conformance tests use different syntax
**Solution**: Examine actual failing test cases in TypeScript repo

### Issue: Parser accepts invalid syntax
**Diagnosis**: Not validating rest element is array type
**Solution**: Add validation in tuple_element() or semantic pass

### Issue: Conflicts with existing readonly array parsing
**Diagnosis**: Lookahead incorrect or ambiguous
**Solution**: Adjust lookahead logic, ensure precedence correct

## Time Estimate Breakdown

- Read context & setup: 1 hour
- Write tests: 1 hour
- Implement parser changes: 2 hours
- Debug & refine: 1 hour
- Run conformance tests: 30 min
- Documentation: 1.5 hours

**Total: 4-8 hours**

## Downstream Impact

This implementation:
- Unblocks 45 conformance tests
- Provides pattern for other readonly+modifier combinations
- Demonstrates feature implementation workflow
- Feeds into validation phase

## Notes for Agent

- You are implementing ONE feature independently
- Other agents may implement other features in parallel
- Focus on correctness over cleverness
- Document everything - your lessons help other agents
- If stuck >2 hours, document the blocker and move on

---

**Ready?** Start with Step 1: Write Failing Tests

## Appendix: Example TypeScript Tests

From microsoft/TypeScript conformance suite:

**tests/cases/conformance/types/tuple/readonlyTupleWithRest.ts**:
```typescript
type T1 = readonly [string, ...number[]];
type T2 = readonly [first: string, ...rest: number[]];

function f1(x: T1) {
    x[0] = "x"; // Error: readonly
    x.push(1);  // Error: readonly
}
```

Use these as reference for correct behavior.
