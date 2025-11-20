---
task_id: "01-analysis/02-categorize-failures"
title: "Categorize Test Failures"
phase: "analysis"
estimated_duration: "3-5 hours"
complexity: "medium"
dependencies:
  - "01-analysis/01-run-conformance-tests"
inputs:
  - "../01-run-conformance-tests/failures.txt"
  - "../01-run-conformance-tests/test-results.json"
  - "../01-run-conformance-tests/timeout-cases.txt"
outputs:
  - "categories.json"
  - "category-analysis.md"
  - "feature-gaps.json"
  - "priority-matrix.md"
skills_required:
  - "Pattern recognition"
  - "Data analysis"
  - "TypeScript knowledge"
---

# Task: Categorize Test Failures

## Objective

Analyze the ~2,100 test failures from conformance tests and categorize them by:
1. Error type (parse error, panic, timeout)
2. Missing feature (which TypeScript syntax is unsupported)
3. Test category (what part of TypeScript: types, expressions, statements, etc.)
4. Priority (frequency, importance, difficulty)

## Context

The conformance test runner has identified which tests fail, but we need to understand **why** they fail. This categorization will drive implementation priorities.

### Available Data

From previous task (`01-run-conformance-tests`):
- `failures.txt`: ~2,100 lines with file paths and error messages
- `test-results.json`: Summary statistics
- `timeout-cases.txt`: Tests that timed out

### Expected Patterns

Based on TypeScript's evolution, failures likely include:
- **Missing features**: TypeScript 5.x syntax not implemented
- **Edge cases**: Rare syntax combinations
- **Error recovery**: Parser too strict for IDE-friendly TypeScript
- **Performance**: Complex types causing timeouts or stack overflow

## Instructions

### Step 1: Parse Failure Data

Read `failures.txt` which has format:
```
================================================================================
File: tests/cases/conformance/types/typeRelationships/...
Duration: 12ms
Error: SyntaxError(ExpectedSyntax("type expression"))
  at line 5, column 12
```

Extract structured data:
```rust
// Suggested analysis tool structure
struct FailureCase {
    file_path: String,
    test_category: String,  // Extract from path
    duration: Duration,
    error_type: ErrorType,
    error_message: String,
    location: Option<(usize, usize)>,
}

enum ErrorType {
    ParseError,
    Panic,
    Timeout,
    AssertionFailure,
}
```

### Step 2: Categorize by Test Directory

TypeScript organizes tests by feature:
```
tests/cases/conformance/
  types/                    <- Type system tests
    conditional/
    mapped/
    literal/
    ...
  expressions/              <- Expression tests
  statements/               <- Statement tests
  classes/                  <- Class tests
  decorators/               <- Decorator tests
  ...
```

Count failures per directory:
```json
{
  "by_directory": {
    "types/conditional": 45,
    "types/mapped": 32,
    "expressions/arrowFunction": 28,
    "decorators/metadata": 67,
    ...
  }
}
```

### Step 3: Categorize by Error Pattern

Group by error message patterns:

**Pattern 1: Missing keyword support**
```
Error: ExpectedSyntax("satisfies operator")
Error: ExpectedSyntax("using declaration")
Error: ExpectedSyntax("abstract constructor")
```
→ **Category**: Missing feature implementation

**Pattern 2: Unexpected token**
```
Error: UnexpectedToken(Token { typ: PrivateMember, ... })
```
→ **Category**: Unsupported syntax location

**Pattern 3: Timeout**
```
Error: TIMEOUT after 10 seconds
```
→ **Category**: Performance issue (infinite loop? exponential complexity?)

**Pattern 4: Panic**
```
Error: PANIC: thread panicked at 'index out of bounds'
```
→ **Category**: Bug (HIGH PRIORITY!)

Create error pattern regex:
```python
# Pseudo-code for pattern matching
patterns = {
    r'ExpectedSyntax\("([^"]+)"\)': "missing_feature",
    r'UnexpectedToken.*PrivateMember': "private_name_in_wrong_location",
    r'TIMEOUT': "performance_issue",
    r'PANIC': "crash_bug",
    r'stack overflow': "recursion_limit",
}
```

### Step 4: Extract Missing Features

From error messages like `ExpectedSyntax("satisfies operator")`, create a list of missing features:

```json
{
  "missing_features": [
    {
      "name": "satisfies operator",
      "occurrences": 67,
      "example_file": "tests/cases/conformance/expressions/satisfies.ts",
      "typescript_version": "4.9",
      "priority": "high"
    },
    {
      "name": "using declaration",
      "occurrences": 45,
      "example_file": "tests/cases/conformance/statements/using.ts",
      "typescript_version": "5.2",
      "priority": "medium"
    },
    ...
  ]
}
```

For each missing feature:
1. Count how many tests fail because of it
2. Find example test file
3. Look up TypeScript version introduced
4. Assign priority based on frequency

### Step 5: Create Priority Matrix

Prioritize features by:
- **Frequency**: How many tests fail? (high freq = high priority)
- **Importance**: Common in real code? (check TypeScript usage stats)
- **Difficulty**: How hard to implement? (estimate based on similar features)
- **Blocking**: Does it block other features?

```markdown
## Priority Matrix

### P0: Critical (Must Fix)
- **Panics** (3 cases): Security/stability issue
  - File: tests/.../panic-case-1.ts
  - Cause: Index out of bounds in tuple parsing
  - Action: Fix immediately

### P1: High Priority (Common Features)
- **Satisfies operator** (67 cases): TypeScript 4.9, widely used
  - Difficulty: Low (similar to type assertions)
  - Blocking: No
  - Action: Implement in Phase 3

- **Using declarations** (45 cases): TypeScript 5.2, resource management
  - Difficulty: Low (similar to const/let)
  - Blocking: No
  - Action: Implement in Phase 3

### P2: Medium Priority
- **Abstract constructor signatures** (23 cases): Less common
  - Difficulty: Medium
  - Blocking: No
  - Action: Implement if time permits

### P3: Low Priority
- **Exotic edge cases** (12 cases): Rare syntax combinations
  - Difficulty: Varies
  - Blocking: No
  - Action: Address in refinement phase
```

### Step 6: Analyze Timeouts

For timeout cases (`timeout-cases.txt`), identify patterns:

```markdown
## Timeout Analysis

**Total Timeouts**: 45 cases

### Patterns

1. **Deeply nested conditionals** (20 cases)
   - Example: `type T = A extends B ? C extends D ? E extends F ? ...`
   - Hypothesis: Exponential backtracking in conditional type parsing

2. **Large union types** (15 cases)
   - Example: `type T = A | B | C | ... | ZZZZ` (100+ members)
   - Hypothesis: O(n²) comparison in type checking

3. **Recursive type references** (10 cases)
   - Example: `type T = { x: T }`
   - Hypothesis: Infinite recursion without proper cycle detection
```

## Acceptance Criteria

### Required Outputs

✅ **categories.json**: Machine-readable categorization
```json
{
  "summary": {
    "total_failures": 2107,
    "by_error_type": {
      "parse_error": 2059,
      "panic": 3,
      "timeout": 45
    },
    "by_directory": { ... },
    "by_feature": { ... }
  },
  "missing_features": [ ... ],
  "timeout_patterns": [ ... ],
  "panic_cases": [ ... ]
}
```

✅ **category-analysis.md**: Human-readable analysis with insights

✅ **feature-gaps.json**: List of unimplemented TypeScript features
```json
[
  {
    "feature": "satisfies operator",
    "test_failures": 67,
    "priority": "high",
    "difficulty": "low",
    "typescript_version": "4.9"
  },
  ...
]
```

✅ **priority-matrix.md**: Prioritized action plan

### Quality Checks

- [ ] All failures accounted for (sum of categories = total failures)
- [ ] Patterns make sense (validate with spot checks)
- [ ] Priorities justified with data
- [ ] JSON files validate
- [ ] Markdown renders correctly

### Success Metrics

- Clear understanding of why tests fail
- Prioritized list of features to implement
- Actionable insights for next phase
- No arbitrary decisions - all backed by data

## Analysis Tools

You may want to write a script to help:

```rust
// Suggested: Create tasks/scripts/analyze_failures.rs

use std::collections::HashMap;
use std::fs;
use regex::Regex;

fn main() {
    let failures = fs::read_to_string("../workspace/outputs/01-analysis/01-run-conformance-tests/failures.txt")?;

    let mut by_directory = HashMap::new();
    let mut by_error_pattern = HashMap::new();
    let mut missing_features = Vec::new();

    // Parse failures
    for failure in parse_failures(&failures) {
        // Count by directory
        *by_directory.entry(failure.directory()).or_insert(0) += 1;

        // Categorize by error
        let category = categorize_error(&failure.error);
        *by_error_pattern.entry(category).or_insert(0) += 1;

        // Extract missing features
        if let Some(feature) = extract_missing_feature(&failure.error) {
            missing_features.push(feature);
        }
    }

    // Output JSON
    let output = serde_json::json!({
        "by_directory": by_directory,
        "by_error_pattern": by_error_pattern,
        "missing_features": missing_features,
    });

    fs::write("categories.json", serde_json::to_string_pretty(&output)?)?;
}
```

Alternatively, use command-line tools:
```bash
# Count failures by directory
cat failures.txt | grep "^File:" | sed 's/File: tests\/cases\/conformance\///' | cut -d'/' -f1-2 | sort | uniq -c | sort -rn

# Count error patterns
cat failures.txt | grep "^Error:" | sort | uniq -c | sort -rn

# Extract "ExpectedSyntax" patterns
cat failures.txt | grep -o 'ExpectedSyntax("[^"]*")' | sort | uniq -c | sort -rn
```

## Common Patterns to Look For

### TypeScript 5.x Features
- `const` type parameters
- `satisfies` operator
- `using` and `await using` declarations
- Decorator metadata
- `NoInfer` utility type

### Edge Cases
- `readonly` in unexpected locations
- Private names (`#foo`) in type positions
- `abstract` modifiers on constructors
- Complex mapped type modifiers

### Error Recovery
- TypeScript allows some "errors" for IDE friendliness
- Parser might be too strict

## Time Estimate Breakdown

- Parse failures.txt: 30 min
- Group by directory: 30 min
- Categorize by error pattern: 1 hour
- Extract missing features: 1 hour
- Prioritization analysis: 1 hour
- Write documentation: 1 hour

**Total: 3-5 hours**

## Downstream Impact

This task feeds into:
- **02-planning/01-prioritize-features**: Uses priority-matrix.md
- **02-planning/02-design-ast-nodes**: Uses feature-gaps.json
- **02-planning/03-plan-parser-extensions**: Uses category-analysis.md

## Notes for Agent

- Be thorough - good categorization saves time later
- Look for unexpected patterns - might reveal bugs
- Document any confusing cases
- If pattern doesn't fit categories, create new category
- Prioritize based on data, not intuition

---

**Ready?** Start with Step 1: Parse Failure Data
