---
task_id: "02-planning/01-prioritize-features"
title: "Prioritize Features for Implementation"
phase: "planning"
estimated_duration: "2-3 hours"
complexity: "medium"
dependencies:
  - "01-analysis/01-run-conformance-tests"
  - "01-analysis/02-categorize-failures"
  - "01-analysis/05-research-feature-usage"
inputs:
  - "../01-analysis/01-run-conformance-tests/test-summary.md"
  - "../01-analysis/02-categorize-failures/priority-matrix.md"
  - "../01-analysis/02-categorize-failures/feature-gaps.json"
  - "../01-analysis/05-research-feature-usage/usage-frequency.json"
outputs:
  - "prioritized-features.json"
  - "implementation-roadmap.md"
  - "feature-specs.md"
skills_required:
  - "Technical decision making"
  - "TypeScript knowledge"
  - "Project planning"
---

# Task: Prioritize Features for Implementation

## Objective

Create a prioritized, data-driven list of TypeScript features to implement, considering:
1. Test failure frequency (from conformance analysis)
2. Real-world usage patterns (from usage research)
3. Implementation difficulty (technical assessment)
4. Dependencies between features

## Context

You have three sources of data:
- **Conformance failures**: Which features cause most test failures
- **Categorization**: What features are missing vs buggy
- **Usage research**: How often features appear in real code

Your job is to synthesize this into an actionable implementation plan.

## Instructions

### Step 1: Load Input Data

Read from previous tasks:

1. **feature-gaps.json**: Missing features with failure counts
```json
{
  "missing_features": [
    {"name": "satisfies operator", "test_failures": 67},
    {"name": "using declarations", "test_failures": 45},
    ...
  ]
}
```

2. **usage-frequency.json**: Real-world usage data
```json
{
  "features": [
    {"name": "satisfies operator", "repos_using": 1234, "percentage": 12.3},
    {"name": "using declarations", "repos_using": 234, "percentage": 2.3},
    ...
  ]
}
```

3. **priority-matrix.md**: Initial priority assessment

### Step 2: Score Each Feature

Create scoring formula:
```
Score = (test_failures * 0.3) +
        (usage_percentage * 10 * 0.3) +
        (ease_of_implementation * 0.2) +
        (typescript_version_weight * 0.2)

where:
  ease_of_implementation: 1-10 (10 = easiest)
  typescript_version_weight: 10 for v4.x, 8 for v5.0-5.2, 6 for v5.3+
```

Example:
```
satisfies operator:
  test_failures = 67 → 67 * 0.3 = 20.1
  usage = 12.3% → 12.3 * 10 * 0.3 = 36.9
  ease = 8 → 8 * 0.2 = 1.6
  version (4.9) → 10 * 0.2 = 2.0
  TOTAL = 60.6

using declarations:
  test_failures = 45 → 45 * 0.3 = 13.5
  usage = 2.3% → 2.3 * 10 * 0.3 = 6.9
  ease = 7 → 7 * 0.2 = 1.4
  version (5.2) → 8 * 0.2 = 1.6
  TOTAL = 23.4
```

### Step 3: Identify Dependencies

Some features depend on others:
```markdown
## Feature Dependencies

- **Decorator metadata** depends on:
  - Decorators (already implemented ✅)
  - Type reflection (not needed for parsing)

- **Template literal types** depends on:
  - String literal types (already implemented ✅)
  - Template parsing (already implemented ✅)

- **Infer with extends** depends on:
  - Conditional types (already implemented ✅)
  - Infer keyword (already implemented ✅)
```

Mark features that should be implemented together or in sequence.

### Step 4: Assess Implementation Difficulty

For each feature, estimate:
- **Lines of code**: 10-50, 50-200, 200-500, 500+
- **AST changes needed**: None, Minor (add fields), Major (new nodes)
- **Parser complexity**: Simple (keyword match), Medium (lookahead), Complex (backtracking)
- **Test complexity**: Simple, Medium, Complex

Example assessment:
```markdown
### Satisfies Operator

**Difficulty**: Low
- LOC: ~50 lines
- AST changes: Minor (add `SatisfiesExpr` variant - already exists!)
- Parser complexity: Simple (postfix operator like `as`)
- Test complexity: Simple
- Estimated time: 4-6 hours

### Using Declarations

**Difficulty**: Low-Medium
- LOC: ~100 lines
- AST changes: Minor (add to `VarDeclMode` enum - already exists!)
- Parser complexity: Simple (like `const`/`let`)
- Test complexity: Medium (resource management semantics)
- Estimated time: 6-8 hours
```

### Step 5: Create Prioritized List

Output `prioritized-features.json`:

```json
{
  "metadata": {
    "created_at": "2025-11-20T10:00:00Z",
    "total_features": 15,
    "estimated_total_hours": 80
  },
  "features": [
    {
      "rank": 1,
      "name": "satisfies operator",
      "score": 60.6,
      "priority": "P0",
      "test_failures": 67,
      "real_world_usage_pct": 12.3,
      "difficulty": "low",
      "estimated_hours": 5,
      "dependencies": [],
      "typescript_version": "4.9",
      "rationale": "High usage, many test failures, easy to implement"
    },
    {
      "rank": 2,
      "name": "readonly tuples with rest",
      "score": 52.1,
      "priority": "P0",
      "test_failures": 45,
      "real_world_usage_pct": 8.7,
      "difficulty": "low",
      "estimated_hours": 5,
      "dependencies": [],
      "typescript_version": "3.4",
      "rationale": "Combines existing features, high compatibility value"
    },
    ...
  ]
}
```

### Step 6: Create Implementation Roadmap

Output `implementation-roadmap.md`:

```markdown
# TypeScript Feature Implementation Roadmap

## Summary

**Total Features**: 15
**Estimated Duration**: 80 hours (10 days with 1 developer)
**Parallelization**: Up to 5 features can be implemented simultaneously

## Phase 1: High-Priority Features (P0)

### Week 1 Goals
- Implement top 5 features
- Reduce test failures by ~200 (35% improvement)
- Focus on high-usage features

| # | Feature | Hours | Test Impact | Dependencies |
|---|---------|-------|-------------|--------------|
| 1 | satisfies operator | 5h | +67 tests | None |
| 2 | readonly tuples with rest | 5h | +45 tests | None |
| 3 | using declarations | 7h | +45 tests | None |
| 4 | abstract constructors | 6h | +28 tests | None |
| 5 | decorator metadata | 8h | +35 tests | None |

**Parallelization**: All 5 can run in parallel (independent tasks)

## Phase 2: Medium-Priority Features (P1)

### Week 2 Goals
- Implement next 5 features
- Address TypeScript 5.x compatibility
- Reduce test failures by ~100

| # | Feature | Hours | Test Impact | Dependencies |
|---|---------|-------|-------------|--------------|
| 6 | import type with typeof | 6h | +23 tests | None |
| 7 | template literal types (edge cases) | 8h | +19 tests | None |
| 8 | infer with extends constraint | 7h | +18 tests | None |
| 9 | const type parameters | 5h | +15 tests | None |
| 10 | JSDoc types (basic) | 9h | +12 tests | None |

**Parallelization**: All 5 can run in parallel

## Phase 3: Polish & Edge Cases (P2)

### Week 3 Goals
- Handle remaining edge cases
- Achieve >95% conformance pass rate
- Performance optimization

| # | Feature | Hours | Test Impact | Dependencies |
|---|---------|-------|-------------|--------------|
| 11-15 | Various edge cases | 15h | +30 tests | Phase 1+2 |

## Expected Outcomes

- **Start**: 90.0% pass rate (18,958 / 21,065 tests)
- **After Phase 1**: 92.4% pass rate (+220 tests)
- **After Phase 2**: 94.5% pass rate (+95 tests)
- **After Phase 3**: >95% pass rate (+30 tests)

## Implementation Strategy

### Parallel Execution
- 5 developers can work simultaneously on Phase 1
- Each feature is independent
- Outputs merge via git

### Risk Mitigation
- Implement P0 features first (highest value)
- Test after each feature (no big-bang integration)
- Roll back if feature causes regressions
```

### Step 7: Write Feature Specifications

Output `feature-specs.md`:

For each feature, write a brief spec:

```markdown
# Feature Specifications

## 1. Satisfies Operator

### TypeScript Syntax
```typescript
const config = {
  apiUrl: "https://api.com",
  timeout: 5000
} satisfies Config;
```

### Description
The `satisfies` operator validates that an expression matches a type without widening the expression's type.

### AST Changes
Add to `parse-js/src/ast/expr/mod.rs`:
```rust
pub enum Expr {
  // ...
  SatisfiesExpr(Node<SatisfiesExpr>),  // Already exists! ✅
}

pub struct SatisfiesExpr {
  pub expression: Node<Expr>,
  pub type_annotation: Node<TypeExpr>,
}
```

### Parser Changes
In `parse-js/src/parse/expr.rs`, handle as postfix operator:
```rust
// After parsing primary expression
if self.consume_if(TT::KeywordSatisfies).is_match() {
  let type_annotation = self.type_expr(ctx)?;
  expr = SatisfiesExpr { expression: expr, type_annotation };
}
```

### Test Cases
1. Basic: `x satisfies T`
2. Complex type: `obj satisfies { [key: string]: number }`
3. Precedence: `x satisfies T as U` (satisfies binds tighter)

### References
- TypeScript 4.9 release notes
- Conformance tests: `tests/cases/conformance/expressions/satisfies*.ts`

---

## 2. Readonly Tuples with Rest

(Similar spec for each feature)

---
```

## Acceptance Criteria

### Required Outputs

✅ **prioritized-features.json**: Data-driven ranking

✅ **implementation-roadmap.md**: Week-by-week plan

✅ **feature-specs.md**: Implementation guidance for each feature

### Quality Checks

- [ ] Priorities justified with data (not intuition)
- [ ] All input sources considered
- [ ] Dependencies identified
- [ ] Time estimates realistic
- [ ] Roadmap accounts for parallelization

### Success Metrics

- Clear implementation order
- Realistic time estimates
- Maximum parallelization identified
- Ready to assign to implementation agents

## Time Estimate Breakdown

- Load and analyze data: 30 min
- Score each feature: 30 min
- Assess dependencies: 30 min
- Estimate difficulty: 1 hour
- Create roadmap: 30 min

**Total: 2-3 hours**

## Notes for Agent

- This is strategic planning - be thoughtful
- Data over opinions
- Consider maintainability (simple features first)
- Document your reasoning
- If torn between two features, choose the easier one

---

**Ready?** Start with Step 1: Load Input Data
