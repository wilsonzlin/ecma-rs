---
task_id: "03-implementation/XX-feature-name"
title: "Implement [Feature Name]"
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
outputs:
  - "implementation-notes.md"
  - "test-cases.rs"
  - "lessons-learned.md"
  - "git-patch.diff"
skills_required:
  - "Rust programming"
  - "Parser implementation"
  - "TypeScript knowledge"
---

# Task: Implement [Feature Name]

## Objective

Add support for TypeScript's [feature description]:

```typescript
// Example syntax this feature enables
```

## Context

### Feature Description

[What this feature does in TypeScript]

### Current State

Based on analysis phase:
- [What exists]
- [What's missing]
- **Gap**: [Specific missing piece]

### Why This Feature

- Priority: **[HIGH/MEDIUM/LOW]** (X test failures)
- TypeScript version: X.X
- Common in real code: [Yes/No]
- Difficulty: **[LOW/MEDIUM/HIGH]**

## Prerequisites

### Files to Understand

1. **AST Definition**: `parse-js/src/ast/type_expr.rs`
   - Lines X-Y: Relevant structs

2. **Parser**: `parse-js/src/parse/type_expr.rs`
   - Lines X-Y: Relevant functions

### TypeScript Specification

From TypeScript handbook:
```typescript
// Official examples
```

## Instructions

### Step 1: Write Failing Tests

Create `parse-js/src/parse/tests/types/[feature_name].rs`:

```rust
#[test]
fn test_[feature]_basic() {
    let src = r#"..."#;
    let result = parse(src);
    assert!(result.is_ok());
}

// Add 3-5 more test cases covering edge cases
```

### Step 2: Understand Current Parser

[Read relevant parser code sections]

### Step 3: Implement Parser Changes

[Specific implementation guidance]

### Step 4: Run Tests

```bash
cargo test [feature_name]
```

### Step 5: Run Conformance Tests

```bash
cargo test --release --test conformance_runner
```

### Step 6: Document Implementation

Create implementation-notes.md, lessons-learned.md

### Step 7: Create Git Patch

```bash
git format-patch -1 HEAD --stdout > workspace/outputs/03-implementation/XX-[feature]/git-patch.diff
```

## Acceptance Criteria

### Required Outputs

✅ **implementation-notes.md**: Implementation summary
✅ **test-cases.rs**: Comprehensive tests
✅ **lessons-learned.md**: Insights
✅ **git-patch.diff**: Changes

### Quality Checks

- [ ] All new tests pass
- [ ] No regressions
- [ ] Conformance pass rate increased
- [ ] No compiler warnings

## Verification Commands

```bash
cargo test [feature_name]
cargo test --package parse-js
cargo clippy --package parse-js
```

## Common Issues & Solutions

[Feature-specific debugging tips]

## Time Estimate Breakdown

- Read context: 1 hour
- Write tests: 1 hour
- Implement: 2 hours
- Debug: 1 hour
- Documentation: 1.5 hours

**Total: 4-8 hours**

## Notes for Agent

- You are implementing ONE feature independently
- Focus on correctness over cleverness
- Document everything for other agents
- If stuck >2 hours, document blocker
